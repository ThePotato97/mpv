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

/*
 * The spatial renderer's processing delay. Windows gives apps no way to read it (the spatial
 * stream has no latency call and its clock leaves the delay out), so, as Windows' own ASAR does,
 * it comes from the device's active spatial format (WinRT's
 * SpatialAudioDeviceConfiguration.ActiveSpatialAudioFormat). Dolby's figure adds the 224-sample
 * object FIFO that ASAR's 512 leaves out: N mod 256 for N-frame passes.
 */
enum {
    RENDERER_UNKNOWN,
    RENDERER_SONIC,
    RENDERER_DOLBY,         // Dolby Atmos for Headphones / for speakers
    RENDERER_DOLBY_HDMI,    // Dolby Atmos for home theater
    RENDERER_DTS,           // DTS Headphone:X / DTS:X Ultra
    RENDERER_DTS_HDMI,      // DTS:X for home theater
};

static const char *const renderer_names[] = {
    "unknown", "Windows Sonic", "Dolby Atmos (headphones/speakers)", "Dolby Atmos (home theater)",
    "DTS (headphones/speakers)", "DTS:X (home theater)",
};

static double processing_delay(int renderer, UINT32 frames)
{
    switch (renderer) {
    case RENDERER_DOLBY:        return (512.0 + frames % 256) / ATMOS_RATE;
    case RENDERER_DTS:          return 256.0 / ATMOS_RATE;
    case RENDERER_DOLBY_HDMI:   return 0.020;
    case RENDERER_DTS_HDMI:     return 0.010;
    default:                    return 0; // Windows Sonic: not traced
    }
}

// WinRT through combase.dll's exports and the interfaces' vtable slots (mingw has no headers for
// Windows.Media.Audio): IInspectable's six methods, then each interface's in declaration order.
typedef HRESULT (WINAPI *RoGetActivationFactoryFn)(HSTRING, REFIID, void **);
typedef HRESULT (WINAPI *WindowsCreateStringFn)(LPCWSTR, UINT32, HSTRING *);
typedef HRESULT (WINAPI *WindowsDeleteStringFn)(HSTRING);
typedef PCWSTR (WINAPI *WindowsGetStringRawBufferFn)(HSTRING, UINT32 *);
typedef HRESULT (STDMETHODCALLTYPE *GetStringFn)(void *, HSTRING *);
typedef HRESULT (STDMETHODCALLTYPE *GetForDeviceIdFn)(void *, HSTRING, void **);
typedef ULONG (STDMETHODCALLTYPE *ReleaseFn)(void *);
#define WINRT_SLOT(obj, n) ((*(void *const **)(obj))[n])
#define WINRT_RELEASE(obj) ((ReleaseFn)WINRT_SLOT(obj, 2))(obj)

static const GUID IID_SpatialAudioDeviceConfigurationStatics =
    {0x3ec37f7b, 0x936d, 0x4e04, {0x97, 0x28, 0x28, 0x27, 0xd9, 0xf7, 0x58, 0xc4}};
static const GUID IID_SpatialAudioFormatSubtypeStatics =
    {0xb3de8a47, 0x83ee, 0x4266, {0xa9, 0x45, 0xbe, 0xdf, 0x50, 0x7a, 0xfe, 0xed}};
static const GUID IID_SpatialAudioFormatSubtypeStatics2 =
    {0x4565e6cb, 0xd95b, 0x5621, {0xb6, 0xaf, 0x0e, 0x88, 0x49, 0xc5, 0x7c, 0x80}};

struct winrt {
    RoGetActivationFactoryFn factory;
    WindowsCreateStringFn create;
    WindowsDeleteStringFn delete;
    WindowsGetStringRawBufferFn raw;
};

static HSTRING winrt_string(struct winrt *w, const wchar_t *s)
{
    HSTRING h = NULL;
    return SUCCEEDED(w->create(s, (UINT32)wcslen(s), &h)) ? h : NULL;
}

static void *winrt_statics(struct winrt *w, const wchar_t *class, const GUID *iid)
{
    HSTRING name = winrt_string(w, class);
    void *statics = NULL;
    if (name && FAILED(w->factory(name, iid, &statics)))
        statics = NULL;
    w->delete(name);
    return statics;
}

// Whether the format subtype at `slot` of `statics` is `format`.
static bool winrt_is_format(struct winrt *w, void *statics, int slot, HSTRING format)
{
    HSTRING subtype = NULL;
    if (!statics || FAILED(((GetStringFn)WINRT_SLOT(statics, slot))(statics, &subtype)))
        return false;
    bool same = wcscmp(w->raw(subtype, NULL), w->raw(format, NULL)) == 0;
    w->delete(subtype);
    return same;
}

// The active spatial format of the endpoint with IMMDevice id `id`.
static int active_renderer(struct ao *ao, const wchar_t *id)
{
    HMODULE combase = GetModuleHandleW(L"combase.dll");
    if (!combase)
        combase = LoadLibraryW(L"combase.dll");
    struct winrt w = {
        .factory = combase ? (RoGetActivationFactoryFn)(void *)GetProcAddress(combase, "RoGetActivationFactory") : NULL,
        .create = combase ? (WindowsCreateStringFn)(void *)GetProcAddress(combase, "WindowsCreateString") : NULL,
        .delete = combase ? (WindowsDeleteStringFn)(void *)GetProcAddress(combase, "WindowsDeleteString") : NULL,
        .raw = combase ? (WindowsGetStringRawBufferFn)(void *)GetProcAddress(combase, "WindowsGetStringRawBuffer") : NULL,
    };
    if (!w.factory || !w.create || !w.delete || !w.raw)
        return RENDERER_UNKNOWN;

    int renderer = RENDERER_UNKNOWN;
    void *devices = winrt_statics(&w, L"Windows.Media.Audio.SpatialAudioDeviceConfiguration",
                                  &IID_SpatialAudioDeviceConfigurationStatics);
    void *config = NULL;
    HSTRING format = NULL;
    if (!devices)
        goto done;
    // WinRT names an endpoint by its device interface path; the bare IMMDevice id as a fallback.
    wchar_t path[512];
    _snwprintf(path, MP_ARRAY_SIZE(path),
               L"\\\\?\\SWD#MMDEVAPI#%ls#{e6327cad-dcec-4949-ae8a-991e976a79d2}", id);
    path[MP_ARRAY_SIZE(path) - 1] = 0;
    const wchar_t *ids[] = {path, id};
    for (int i = 0; i < MP_ARRAY_SIZE(ids) && !config; i++) {
        HSTRING h = winrt_string(&w, ids[i]);
        if (h && FAILED(((GetForDeviceIdFn)WINRT_SLOT(devices, 6))(devices, h, &config)))
            config = NULL;
        w.delete(h);
    }
    // ActiveSpatialAudioFormat: after DeviceId, IsSpatialAudioSupported, IsSpatialAudioFormatSupported
    if (!config || FAILED(((GetStringFn)WINRT_SLOT(config, 9))(config, &format)) || !format)
        goto done;
    MP_VERBOSE(ao, "Active spatial format: %ls\n", w.raw(format, NULL));

    void *subtypes = winrt_statics(&w, L"Windows.Media.Audio.SpatialAudioFormatSubtype",
                                   &IID_SpatialAudioFormatSubtypeStatics);
    void *subtypes2 = winrt_statics(&w, L"Windows.Media.Audio.SpatialAudioFormatSubtype",
                                    &IID_SpatialAudioFormatSubtypeStatics2);
    // WindowsSonic, DolbyAtmosForHeadphones, DolbyAtmosForHomeTheater, DolbyAtmosForSpeakers,
    // DTSHeadphoneX, DTSXUltra; then (Statics2) DTSXForHomeTheater
    static const int kinds[] = {RENDERER_SONIC, RENDERER_DOLBY, RENDERER_DOLBY_HDMI,
                                RENDERER_DOLBY, RENDERER_DTS, RENDERER_DTS};
    for (int i = 0; i < MP_ARRAY_SIZE(kinds) && renderer == RENDERER_UNKNOWN; i++) {
        if (winrt_is_format(&w, subtypes, 6 + i, format))
            renderer = kinds[i];
    }
    if (renderer == RENDERER_UNKNOWN && winrt_is_format(&w, subtypes2, 6, format))
        renderer = RENDERER_DTS_HDMI;
    if (subtypes)
        WINRT_RELEASE(subtypes);
    if (subtypes2)
        WINRT_RELEASE(subtypes2);

done:
    if (format)
        w.delete(format);
    if (config)
        WINRT_RELEASE(config);
    if (devices)
        WINRT_RELEASE(devices);
    if (!config)
        MP_VERBOSE(ao, "Couldn't read the device's active spatial format\n");
    return renderer;
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
    // read on every open: a change of spatial format invalidates the stream and mpv reopens it
    if (SUCCEEDED(hr))
        p->renderer = active_renderer(ao, device_id);
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
    MP_VERBOSE(ao, "Spatial audio stream: %u dynamic objects, renderer %s\n",
               (unsigned)p->max_dynamic, renderer_names[p->renderer]);

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
}

/* One pass: the provider asks for `frames` samples of every active object. */
static void feed(struct ao *ao)
{
    struct priv *p = ao->priv;
    UINT32 available = 0, frames = 0;

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
