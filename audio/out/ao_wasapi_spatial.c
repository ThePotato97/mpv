/*
 * This file is part of mpv.
 *
 * mpv is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * mpv is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with mpv.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Dolby Atmos objects to Windows' spatial audio (ISpatialAudioObjectRenderStream), so the
 * spatial sound provider (Dolby Atmos for Headphones, Windows Sonic) renders them as it renders
 * those of Windows' own DD+ decoder.
 *
 * It plays only what FFmpeg's libatmos decoders give: ATMOS_CHANNELS unnamed float channels at
 * 48 kHz with AV_FRAME_DATA_ATMOS_OBJECTS, one AVAtmosObject per channel. Anything else fails
 * init, so the next audio output in the list plays it. A static channel goes out as its
 * AudioObjectType; a dynamic one as a dynamic object, activated in channel order (the stream's
 * OAMD order, as Windows' decoder activates them), at its position, with its volume left at 1:
 * the samples already carry each object's gain, and the provider applies its own headroom, clip
 * and position smoothing. Objects are released on every reset (a seek), as Windows' decoder path
 * releases them.
 */

#include <math.h>

#define COBJMACROS 1
#include <windows.h>
#include <mmdeviceapi.h>
#include <spatialaudioclient.h>
#include <hstring.h>

#include <libavutil/frame.h>

#include "audio/format.h"
#include "common/msg.h"
#include "osdep/threads.h"
#include "osdep/timer.h"
#include "ao.h"
#include "internal.h"

#ifdef AV_FRAME_DATA_ATMOS_OBJECTS_AVAILABLE
#include <libavutil/atmos_objects.h>
#endif

#define ATMOS_CHANNELS 32
#define ATMOS_RATE 48000
/* FrontLeft .. TopBackRight, LowFrequency included: the bed's static types */
#define STATIC_MASK 0x1FFE
/* Dolby Atmos' 32 active objects: a 7.1.4 bed and 20 dynamic */
#define MAX_DYNAMIC 20

/* Defined in ao_wasapi_utils.c. */
extern const GUID CLSID_MMDeviceEnumerator;
extern const GUID IID_IMMDeviceEnumerator;
extern const GUID IID_IAudioClock;
/* ao_wasapi_utils.c: the device --audio-device names (wasapi's), or the default. */
LPWSTR wasapi_find_deviceID(struct ao *ao);

static const GUID spatial_IID_ISpatialAudioClient =
    {0xbbf8e066, 0xaaaa, 0x49be, {0x9a, 0x4d, 0xfd, 0x2a, 0x85, 0x8e, 0xa2, 0x7f}};
static const GUID spatial_IID_ISpatialAudioObjectRenderStream =
    {0xbab5f473, 0xb423, 0x477b, {0x85, 0xf5, 0xb5, 0xa3, 0x32, 0xa0, 0x41, 0x53}};

#ifndef AV_FRAME_DATA_ATMOS_OBJECTS_AVAILABLE
typedef struct AVAtmosObject {
    uint32_t object_type;
    float x, y, z;
    uint32_t active;
} AVAtmosObject;
#endif

/*
 * The spatial renderer's processing delay. Windows gives apps no way to read it (the spatial
 * stream has no latency call, its clock leaves the delay out, and GetStreamLatency is always 0),
 * so, as Windows' own ASAR does, it comes from the device's active spatial format (WinRT's
 * SpatialAudioDeviceConfiguration.ActiveSpatialAudioFormat), read on open and again whenever the
 * device's configuration changes (ConfigurationChanged), whether or not that tears the stream down.
 * Dolby Atmos for Headphones' figure adds the object FIFO that ASAR's 512 leaves out: N mod 256
 * for N-frame passes.
 */
enum {
    RENDERER_UNKNOWN,
    RENDERER_SONIC,
    RENDERER_DOLBY_HEADPHONES,
    RENDERER_DOLBY_SPEAKERS,
    RENDERER_DOLBY_HDMI,    // Dolby Atmos for home theater
    RENDERER_DTS,           // DTS Headphone:X / DTS:X Ultra
    RENDERER_DTS_HDMI,      // DTS:X for home theater
};

static const char *const renderer_names[] = {
    "unknown", "Windows Sonic", "Dolby Atmos for Headphones", "Dolby Atmos for speakers",
    "Dolby Atmos for home theater", "DTS Headphone:X / DTS:X Ultra", "DTS:X for home theater",
};

// The public SpatialAudioFormatSubtype values, which are the encoder GUIDs ASAR keys its
// latencies on.
static const struct {
    const wchar_t *guid;
    int renderer;
} spatial_formats[] = {
    {L"1459AC38-3875-49BF-BB59-0FE80F4D395D", RENDERER_DOLBY_HEADPHONES},
    {L"4C81E564-C8EF-4AD9-9F2C-9EF995533790", RENDERER_DOLBY_SPEAKERS},
    {L"4444ACB0-8DC0-4C2C-A0D8-2C76DB470F86", RENDERER_DTS},        // DTSHeadphoneX
    {L"ADAFD3C6-AC4C-404A-836A-9615E9060564", RENDERER_DTS},        // DTSXUltra
    {L"A289735D-FA3E-4E35-9D7D-B6F896ACB2E7", RENDERER_DOLBY_HDMI},
    {L"10201B4A-3322-4967-BF40-2CAA9BAFCA44", RENDERER_DTS_HDMI},
    {L"B53D940C-B846-4831-9F76-D102B9B725A0", RENDERER_SONIC},
};

static double processing_delay(int renderer, UINT32 frames)
{
    switch (renderer) {
    case RENDERER_DOLBY_HEADPHONES: return (512.0 + frames % 256) / ATMOS_RATE;
    // ASAR's figure: whether DolbyHrtfEnc's FIFO applies here too isn't traced
    case RENDERER_DOLBY_SPEAKERS:   return 512.0 / ATMOS_RATE;
    case RENDERER_DTS:              return 256.0 / ATMOS_RATE;
    // the receiver's own delay comes on top, which Windows can't see
    case RENDERER_DOLBY_HDMI:       return 0.020;
    case RENDERER_DTS_HDMI:         return 0.010;
    default:                        return 0; // Windows Sonic works its out at init: not traced
    }
}

// WinRT through combase.dll's exports and the interfaces' vtable slots (mingw has no headers for
// Windows.Media.Audio): IInspectable's six methods, then each interface's in declaration order.
typedef HRESULT (WINAPI *RoGetActivationFactoryFn)(HSTRING, REFIID, void **);
typedef HRESULT (WINAPI *WindowsCreateStringFn)(LPCWSTR, UINT32, HSTRING *);
typedef HRESULT (WINAPI *WindowsDeleteStringFn)(HSTRING);
typedef PCWSTR (WINAPI *WindowsGetStringRawBufferFn)(HSTRING, UINT32 *);
typedef HRESULT (STDMETHODCALLTYPE *GetStringFn)(void *, HSTRING *);
typedef HRESULT (STDMETHODCALLTYPE *GetBoolFn)(void *, boolean *);
typedef HRESULT (STDMETHODCALLTYPE *GetForDeviceIdFn)(void *, HSTRING, void **);
typedef HRESULT (STDMETHODCALLTYPE *AddHandlerFn)(void *, void *, INT64 *);
typedef HRESULT (STDMETHODCALLTYPE *RemoveHandlerFn)(void *, INT64);
typedef ULONG (STDMETHODCALLTYPE *ReleaseFn)(void *);
#define WINRT_SLOT(obj, n) ((*(void *const **)(obj))[n])
#define WINRT_RELEASE(obj) ((ReleaseFn)WINRT_SLOT(obj, 2))(obj)
// ISpatialAudioDeviceConfigurationStatics
#define SLOT_GET_FOR_DEVICE_ID 6
// ISpatialAudioDeviceConfiguration
#define SLOT_IS_SPATIAL_AUDIO_SUPPORTED 7
#define SLOT_ACTIVE_SPATIAL_AUDIO_FORMAT 9
#define SLOT_ADD_CONFIGURATION_CHANGED 12
#define SLOT_REMOVE_CONFIGURATION_CHANGED 13

static const GUID IID_SpatialAudioDeviceConfigurationStatics =
    {0x3ec37f7b, 0x936d, 0x4e04, {0x97, 0x28, 0x28, 0x27, 0xd9, 0xf7, 0x58, 0xc4}};
// TypedEventHandler<SpatialAudioDeviceConfiguration, IInspectable>, WinRT's parameterized IID
static const GUID IID_ConfigurationChangedHandler =
    {0x34cb725d, 0xd620, 0x5c8d, {0x97, 0xf6, 0xa3, 0xeb, 0xdf, 0xf1, 0xf9, 0x64}};
static const GUID IID_AgileObject =
    {0x94ea2b94, 0xe9cc, 0x49e0, {0xc0, 0xff, 0xee, 0x64, 0xca, 0x8f, 0x5b, 0x90}};
static const GUID IID_Unknown =
    {0x00000000, 0x0000, 0x0000, {0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x46}};

struct winrt {
    RoGetActivationFactoryFn factory;
    WindowsCreateStringFn create;
    WindowsDeleteStringFn delete;
    WindowsGetStringRawBufferFn raw;
};

static bool winrt_load(struct winrt *w)
{
    HMODULE combase = GetModuleHandleW(L"combase.dll");
    if (!combase)
        combase = LoadLibraryW(L"combase.dll");
    if (!combase)
        return false;
    w->factory = (RoGetActivationFactoryFn)(void *)GetProcAddress(combase, "RoGetActivationFactory");
    w->create = (WindowsCreateStringFn)(void *)GetProcAddress(combase, "WindowsCreateString");
    w->delete = (WindowsDeleteStringFn)(void *)GetProcAddress(combase, "WindowsDeleteString");
    w->raw = (WindowsGetStringRawBufferFn)(void *)GetProcAddress(combase, "WindowsGetStringRawBuffer");
    return w->factory && w->create && w->delete && w->raw;
}

static HSTRING winrt_string(struct winrt *w, const wchar_t *s)
{
    HSTRING h = NULL;
    return SUCCEEDED(w->create(s, (UINT32)wcslen(s), &h)) ? h : NULL;
}

// The ConfigurationChanged handler: a flag the feeding thread reads before each pass.
struct format_watch;
struct format_watch_vtbl {
    HRESULT (STDMETHODCALLTYPE *QueryInterface)(struct format_watch *, REFIID, void **);
    ULONG (STDMETHODCALLTYPE *AddRef)(struct format_watch *);
    ULONG (STDMETHODCALLTYPE *Release)(struct format_watch *);
    HRESULT (STDMETHODCALLTYPE *Invoke)(struct format_watch *, void *sender, void *args);
};
struct format_watch {
    const struct format_watch_vtbl *vtbl;
    atomic_ulong refs;
    atomic_bool changed;
};

static ULONG STDMETHODCALLTYPE watch_add_ref(struct format_watch *w)
{
    return atomic_fetch_add(&w->refs, 1) + 1;
}

static ULONG STDMETHODCALLTYPE watch_release(struct format_watch *w)
{
    ULONG refs = atomic_fetch_sub(&w->refs, 1) - 1;
    if (!refs)
        free(w);
    return refs;
}

static HRESULT STDMETHODCALLTYPE watch_query_interface(struct format_watch *w, REFIID iid, void **out)
{
    if (IsEqualGUID(iid, &IID_Unknown) || IsEqualGUID(iid, &IID_AgileObject) ||
        IsEqualGUID(iid, &IID_ConfigurationChangedHandler))
    {
        watch_add_ref(w);
        *out = w;
        return S_OK;
    }
    *out = NULL;
    return E_NOINTERFACE;
}

static HRESULT STDMETHODCALLTYPE watch_invoke(struct format_watch *w, void *sender, void *args)
{
    atomic_store(&w->changed, true);
    return S_OK;
}

static const struct format_watch_vtbl format_watch_vtbl = {
    watch_query_interface, watch_add_ref, watch_release, watch_invoke,
};

struct spatial_format {
    struct winrt w;
    void *config;               // ISpatialAudioDeviceConfiguration
    struct format_watch *watch;
    INT64 token;
};

// The endpoint's spatial configuration, watched for changes. WinRT names an endpoint by its
// device interface path (the bare IMMDevice id gives a configuration that reads as unsupported).
static void format_open(struct ao *ao, struct spatial_format *f, const wchar_t *id)
{
    if (!winrt_load(&f->w))
        return;
    HSTRING class = winrt_string(&f->w, L"Windows.Media.Audio.SpatialAudioDeviceConfiguration");
    void *devices = NULL;
    if (!class || FAILED(f->w.factory(class, &IID_SpatialAudioDeviceConfigurationStatics, &devices)))
        devices = NULL;
    f->w.delete(class);
    if (!devices)
        return;
    wchar_t path[512];
    _snwprintf(path, MP_ARRAY_SIZE(path),
               L"\\\\?\\SWD#MMDEVAPI#%ls#{e6327cad-dcec-4949-ae8a-991e976a79d2}", id);
    path[MP_ARRAY_SIZE(path) - 1] = 0;
    HSTRING h = winrt_string(&f->w, path);
    if (!h || FAILED(((GetForDeviceIdFn)WINRT_SLOT(devices, SLOT_GET_FOR_DEVICE_ID))(devices, h, &f->config)))
        f->config = NULL;
    f->w.delete(h);
    WINRT_RELEASE(devices);
    if (!f->config)
        return;

    struct format_watch *watch = calloc(1, sizeof(*watch));
    if (!watch)
        return;
    watch->vtbl = &format_watch_vtbl;
    atomic_init(&watch->refs, 1);
    atomic_init(&watch->changed, false);
    HRESULT hr = ((AddHandlerFn)WINRT_SLOT(f->config, SLOT_ADD_CONFIGURATION_CHANGED))(
        f->config, watch, &f->token);
    if (FAILED(hr)) {
        MP_VERBOSE(ao, "Can't watch the spatial format for changes (0x%lx)\n", (unsigned long)hr);
        watch_release(watch);
        return;
    }
    f->watch = watch;
}

static void format_close(struct spatial_format *f)
{
    if (f->watch) {
        ((RemoveHandlerFn)WINRT_SLOT(f->config, SLOT_REMOVE_CONFIGURATION_CHANGED))(f->config, f->token);
        watch_release(f->watch);
        f->watch = NULL;
    }
    if (f->config) {
        WINRT_RELEASE(f->config);
        f->config = NULL;
    }
}

// Whether `s` is the GUID `guid` (no braces), with or without braces, in either case.
static bool is_guid(const wchar_t *s, const wchar_t *guid)
{
    if (*s == L'{')
        s++;
    return _wcsnicmp(s, guid, 36) == 0 && (!s[36] || s[36] == L'}');
}

// The renderer the endpoint's active spatial format names.
static int format_read(struct ao *ao, struct spatial_format *f)
{
    boolean supported = 0;
    HSTRING format = NULL;
    if (!f->config ||
        FAILED(((GetBoolFn)WINRT_SLOT(f->config, SLOT_IS_SPATIAL_AUDIO_SUPPORTED))(f->config, &supported)) ||
        !supported ||
        FAILED(((GetStringFn)WINRT_SLOT(f->config, SLOT_ACTIVE_SPATIAL_AUDIO_FORMAT))(f->config, &format)) ||
        !format || is_guid(f->w.raw(format, NULL), L"00000000-0000-0000-0000-000000000000"))
    {
        MP_WARN(ao, "Couldn't read the device's spatial format: no processing delay counted\n");
        if (format)
            f->w.delete(format);
        return RENDERER_UNKNOWN;
    }
    const wchar_t *s = f->w.raw(format, NULL);
    int renderer = RENDERER_UNKNOWN;
    for (int i = 0; i < MP_ARRAY_SIZE(spatial_formats); i++) {
        if (is_guid(s, spatial_formats[i].guid))
            renderer = spatial_formats[i].renderer;
    }
    MP_VERBOSE(ao, "Spatial format %ls: %s\n", s, renderer_names[renderer]);
    f->w.delete(format);
    return renderer;
}

struct priv {
    mp_thread thread;
    HANDLE event;           // the stream's buffer-ready event
    HANDLE wake;            // our requests to the thread
    HANDLE init_done;
    bool init_ok;
    atomic_int request;     // REQ_*
    ISpatialAudioClient *client;
    ISpatialAudioObjectRenderStream *stream;
    IAudioClock *clock;     // the stream's clock (GetService), or NULL
    UINT64 clock_frequency;
    UINT64 written;         // frames handed to the stream since it last started from zero
    ISpatialAudioObject *objects[ATMOS_CHANNELS];
    uint32_t types[ATMOS_CHANNELS];
    AVAtmosObject meta[ATMOS_CHANNELS];
    float *planes[ATMOS_CHANNELS];
    UINT32 planes_frames;
    UINT32 max_dynamic;
    struct spatial_format format;
    int renderer;           // RENDERER_*, the device's active spatial format
    bool started;
    bool running;           // the thread is up
    bool reloading;         // the stream failed: mpv reopens the output
};

enum { REQ_NONE, REQ_START, REQ_PAUSE, REQ_RESET, REQ_QUIT };

static void release_objects(struct priv *p)
{
    for (int c = 0; c < ATMOS_CHANNELS; c++) {
        if (p->objects[c]) {
            ISpatialAudioObject_Release(p->objects[c]);
            p->objects[c] = NULL;
        }
        p->types[c] = 0;
    }
}

static bool open_stream(struct ao *ao)
{
    struct priv *p = ao->priv;
    IMMDeviceEnumerator *enumerator = NULL;
    IMMDevice *device = NULL;
    HRESULT hr;

    hr = CoCreateInstance(&CLSID_MMDeviceEnumerator, NULL, CLSCTX_ALL,
                          &IID_IMMDeviceEnumerator, (void **)&enumerator);
    if (FAILED(hr))
        goto fail;
    // the device the app's setting names (Dolby Atmos for Headphones is set per output)
    LPWSTR device_id = wasapi_find_deviceID(ao);
    if (!device_id)
        goto fail;
    hr = IMMDeviceEnumerator_GetDevice(enumerator, device_id, &device);
    if (SUCCEEDED(hr)) {
        format_close(&p->format);
        format_open(ao, &p->format, device_id);
        p->renderer = format_read(ao, &p->format);
    }
    talloc_free(device_id);
    if (FAILED(hr))
        goto fail;
    hr = IMMDevice_Activate(device, &spatial_IID_ISpatialAudioClient, CLSCTX_INPROC_SERVER,
                            NULL, (void **)&p->client);
    if (FAILED(hr)) {
        MP_VERBOSE(ao, "No spatial audio on this device (0x%lx)\n", (unsigned long)hr);
        goto fail;
    }

    WAVEFORMATEX format = {
        .wFormatTag = WAVE_FORMAT_IEEE_FLOAT,
        .nChannels = 1,
        .nSamplesPerSec = ATMOS_RATE,
        .wBitsPerSample = 32,
        .nBlockAlign = 4,
        .nAvgBytesPerSec = ATMOS_RATE * 4,
    };
    hr = ISpatialAudioClient_IsAudioObjectFormatSupported(p->client, &format);
    if (FAILED(hr)) {
        MP_VERBOSE(ao, "48 kHz float objects not supported (0x%lx)\n", (unsigned long)hr);
        goto fail;
    }
    hr = ISpatialAudioClient_GetMaxDynamicObjectCount(p->client, &p->max_dynamic);
    if (FAILED(hr) || !p->max_dynamic) {
        // spatial sound off, or a provider without dynamic objects
        MP_VERBOSE(ao, "No dynamic spatial audio objects available\n");
        goto fail;
    }
    p->max_dynamic = MPMIN(p->max_dynamic, MAX_DYNAMIC);

    SpatialAudioObjectRenderStreamActivationParams params = {
        .ObjectFormat = &format,
        .StaticObjectTypeMask = STATIC_MASK,
        .MinDynamicObjectCount = 0,
        .MaxDynamicObjectCount = p->max_dynamic,
        .Category = AudioCategory_Movie,
        .EventHandle = p->event,
        .NotifyObject = NULL,
    };
    PROPVARIANT activation;
    PropVariantInit(&activation);
    activation.vt = VT_BLOB;
    activation.blob.cbSize = sizeof(params);
    activation.blob.pBlobData = (BYTE *)&params;
    hr = ISpatialAudioClient_ActivateSpatialAudioStream(p->client, &activation,
            &spatial_IID_ISpatialAudioObjectRenderStream, (void **)&p->stream);
    if (FAILED(hr)) {
        MP_VERBOSE(ao, "Spatial audio stream refused (0x%lx)\n", (unsigned long)hr);
        goto fail;
    }
    MP_VERBOSE(ao, "Spatial audio stream: %u dynamic objects\n", (unsigned)p->max_dynamic);

    // The stream's clock (AudioSes' spatial client clock), for the delay; without it, an estimate.
    if (SUCCEEDED(ISpatialAudioObjectRenderStream_GetService(p->stream, &IID_IAudioClock, (void **)&p->clock)) &&
        FAILED(IAudioClock_GetFrequency(p->clock, &p->clock_frequency)))
    {
        IAudioClock_Release(p->clock);
        p->clock = NULL;
    }
    if (!p->clock || !p->clock_frequency) {
        MP_VERBOSE(ao, "No stream clock: estimating the delay\n");
        p->clock_frequency = 0;
    }

    IMMDevice_Release(device);
    IMMDeviceEnumerator_Release(enumerator);
    return true;

fail:
    if (device)
        IMMDevice_Release(device);
    if (enumerator)
        IMMDeviceEnumerator_Release(enumerator);
    return false;
}

static void close_stream(struct priv *p)
{
    release_objects(p);
    if (p->clock) {
        IAudioClock_Release(p->clock);
        p->clock = NULL;
    }
    if (p->stream) {
        ISpatialAudioObjectRenderStream_Stop(p->stream);
        ISpatialAudioObjectRenderStream_Release(p->stream);
        p->stream = NULL;
    }
    if (p->client) {
        ISpatialAudioClient_Release(p->client);
        p->client = NULL;
    }
    format_close(&p->format);
}

/* One pass: the provider asks for `frames` samples of every active object. */
static void feed(struct ao *ao)
{
    struct priv *p = ao->priv;
    UINT32 available = 0, frames = 0;

    // the spatial format changed (ConfigurationChanged), whether or not the stream survives it
    if (p->format.watch && atomic_exchange(&p->format.watch->changed, false))
        p->renderer = format_read(ao, &p->format);

    HRESULT hr = ISpatialAudioObjectRenderStream_BeginUpdatingAudioObjects(p->stream, &available, &frames);
    if (FAILED(hr)) {
        // Spatial sound turned off or changed, or the device gone, invalidates the stream: mpv
        // reopens the output, on a new stream where spatial audio remains, else another output.
        if (!p->reloading) {
            MP_WARN(ao, "Spatial audio stream failed (0x%lx): reopening the output\n", (unsigned long)hr);
            p->reloading = true;
            ao_request_reload(ao);
        }
        return;
    }

    if (frames > p->planes_frames) {
        for (int c = 0; c < ATMOS_CHANNELS; c++)
            p->planes[c] = talloc_realloc(ao, p->planes[c], float, frames);
        p->planes_frames = frames;
    }
    // When this buffer's last sample plays: what's written and not yet played, by the stream's
    // clock, plus this buffer; without a clock, this buffer and the one playing. The clock counts
    // samples handed to the spatial renderer, not heard, so add the renderer's own processing.
    // Windows' endpoint limiter is left out, as plain wasapi leaves it out.
    double processing = processing_delay(p->renderer, frames);
    double delay = 2.0 * frames / ATMOS_RATE + processing;
    UINT64 position = 0;
    if (p->clock && SUCCEEDED(IAudioClock_GetPosition(p->clock, &position, NULL))) {
        double queued = (double)p->written / ATMOS_RATE - (double)position / p->clock_frequency;
        delay = MPMAX(queued, 0) + (double)frames / ATMOS_RATE + processing;
    }
    int64_t out_time = mp_time_ns() + MP_TIME_S_TO_NS(delay);
    p->written += frames;
    ao_read_data(ao, (void **)p->planes, frames, out_time, NULL, true, true);
    if (ao_get_atmos_objects(ao, p->meta, sizeof(p->meta)) != sizeof(p->meta))
        memset(p->meta, 0, sizeof(p->meta)); // silence or a gap: every object idle

    for (int c = 0; c < ATMOS_CHANNELS; c++) {
        uint32_t type = p->meta[c].object_type;
        if (p->objects[c] && type != p->types[c]) {
            // its element changed (a new layout): the old object ends here
            ISpatialAudioObject_SetEndOfStream(p->objects[c], 0);
            ISpatialAudioObject_Release(p->objects[c]);
            p->objects[c] = NULL;
            p->types[c] = 0;
        }
        if (!type)
            continue;
        if (!p->objects[c]) {
            if (type == AudioObjectType_Dynamic && !available)
                continue; // the provider has no dynamic object left for it
            if (FAILED(ISpatialAudioObjectRenderStream_ActivateSpatialAudioObject(
                    p->stream, (AudioObjectType)type, &p->objects[c])))
            {
                p->objects[c] = NULL;
                continue;
            }
            p->types[c] = type;
            if (type == AudioObjectType_Dynamic)
                available--;
            ISpatialAudioObject_SetVolume(p->objects[c], 1.0f);
        }
        if (type == AudioObjectType_Dynamic)
            ISpatialAudioObject_SetPosition(p->objects[c], p->meta[c].x, p->meta[c].y, p->meta[c].z);
        BYTE *buffer = NULL;
        UINT32 bytes = 0;
        if (SUCCEEDED(ISpatialAudioObject_GetBuffer(p->objects[c], &buffer, &bytes)) && buffer)
            memcpy(buffer, p->planes[c], MPMIN(bytes, frames * sizeof(float)));
    }

    ISpatialAudioObjectRenderStream_EndUpdatingAudioObjects(p->stream);
}

static MP_THREAD_VOID audio_thread(void *arg)
{
    struct ao *ao = arg;
    struct priv *p = ao->priv;
    mp_thread_set_name("ao/wasapi_spatial");
    CoInitializeEx(NULL, COINIT_MULTITHREADED);

    p->init_ok = open_stream(ao);
    SetEvent(p->init_done);
    if (!p->init_ok)
        goto done;

    while (true) {
        HANDLE handles[] = {p->event, p->wake};
        DWORD r = WaitForMultipleObjects(2, handles, FALSE, INFINITE);
        if (r == WAIT_OBJECT_0) {
            if (p->started)
                feed(ao);
            continue;
        }
        int request = atomic_exchange(&p->request, REQ_NONE);
        if (request == REQ_QUIT)
            break;
        if (request == REQ_START && !p->started) {
            if (SUCCEEDED(ISpatialAudioObjectRenderStream_Start(p->stream)))
                p->started = true;
        } else if (request == REQ_PAUSE && p->started) {
            ISpatialAudioObjectRenderStream_Stop(p->stream);
            p->started = false;
        } else if (request == REQ_RESET) {
            ISpatialAudioObjectRenderStream_Stop(p->stream);
            ISpatialAudioObjectRenderStream_Reset(p->stream);
            release_objects(p);
            p->started = false;
            p->written = 0; // a reset stream's clock starts again from zero
        }
    }

done:
    close_stream(p);
    CoUninitialize();
    MP_THREAD_RETURN();
}

static void request(struct ao *ao, int req)
{
    struct priv *p = ao->priv;
    atomic_store(&p->request, req);
    SetEvent(p->wake);
}

static void close_handles(struct priv *p)
{
    if (p->event)
        CloseHandle(p->event);
    if (p->wake)
        CloseHandle(p->wake);
    if (p->init_done)
        CloseHandle(p->init_done);
    p->event = p->wake = p->init_done = NULL;
}

static void uninit(struct ao *ao)
{
    struct priv *p = ao->priv;
    if (p->running) {
        request(ao, REQ_QUIT);
        mp_thread_join(p->thread);
        p->running = false;
    }
    close_handles(p);
}

static int init(struct ao *ao)
{
    struct priv *p = ao->priv;

    if (ao->samplerate != ATMOS_RATE || ao->channels.num != ATMOS_CHANNELS ||
        !mp_chmap_is_unknown(&ao->channels))
    {
        MP_VERBOSE(ao, "Not Atmos objects: another output plays this\n");
        return -1;
    }
    ao->format = AF_FORMAT_FLOATP;

    p->event = CreateEventW(NULL, FALSE, FALSE, NULL);
    p->wake = CreateEventW(NULL, FALSE, FALSE, NULL);
    p->init_done = CreateEventW(NULL, FALSE, FALSE, NULL);
    if (!p->event || !p->wake || !p->init_done)
        goto fail;
    if (mp_thread_create(&p->thread, audio_thread, ao))
        goto fail;
    WaitForSingleObject(p->init_done, INFINITE);
    if (!p->init_ok) {
        // the thread has closed what it opened and returned
        mp_thread_join(p->thread);
        goto fail;
    }
    p->running = true;
    return 0;

fail:
    close_handles(p);
    return -1;
}

static void start(struct ao *ao)
{
    request(ao, REQ_START);
}

static void reset(struct ao *ao)
{
    request(ao, REQ_RESET);
}

static bool set_pause(struct ao *ao, bool paused)
{
    request(ao, paused ? REQ_PAUSE : REQ_START);
    return true;
}

const struct ao_driver audio_out_wasapi_spatial = {
    .description = "Windows spatial audio objects (Dolby Atmos objects from libatmos)",
    .name        = "wasapi_spatial",
    .init        = init,
    .uninit      = uninit,
    .reset       = reset,
    .start       = start,
    .set_pause   = set_pause,
    .priv_size   = sizeof(struct priv),
};
