// islita: isla dinámica para Windows, estilo Apple.
// Win32 + Direct2D (render por software) + ventana por capas. Sin frameworks.
#ifndef UNICODE
#define UNICODE
#endif
#define _WIN32_WINNT 0x0A00
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <d2d1.h>
#include <dwrite.h>
#include <wincodec.h>
#include <shellapi.h>
#include <shlobj.h>
#include <commctrl.h>
#include <pdh.h>
#include <roapi.h>
#include <winstring.h>
#include <inspectable.h>
#include <asyncinfo.h>
#include <shcore.h>
#include <shellscalingapi.h>
#define _USE_MATH_DEFINES
#include <cmath>
#include <cstdio>
#include <cwchar>
#include <string>
#include <vector>
#include <mutex>
#include <atomic>
#include <thread>
#include <set>
#include <algorithm>
#include <climits>
#include <winhttp.h>
#include <map>
#include <mmsystem.h>
#include <mmdeviceapi.h>
#include <endpointvolume.h>
#include <dwmapi.h>
#include <wbemidl.h>
#include <shlwapi.h>

// ---------------------------------------------------------------- constantes
static const float EW = 720, EH = 264, ER = 40;   // panel abierto
static const float CH = 34;                       // alto de la píldora
static const float CW_IDLE = 236, CW_PLAY = 304, CW_EVENT = 340;  // ancho de la píldora
static const float TOPGAP = 6;                    // separación con el borde superior
static const float M = 18;                        // margen para la sombra

enum { T_TICK = 1, T_CLOCK, T_POLL, T_COLLAPSE, T_TRIM, T_HOVER, T_PEEK };
enum { WM_APP_MEDIA = WM_APP + 1, WM_APP_STATS, WM_APP_CAL };
enum { H_NONE = 0, H_PREV, H_PLAY, H_NEXT, H_CPREV, H_CNEXT, H_CTITLE, H_CBACK, H_COPEN,
       H_TAB0 = 10, H_TAB1, H_GEAR, H_TM_PLAY, H_TM_RESET, H_TM_ADD, H_SW_L, H_SW_R, H_VOL, H_EDIT_CAL, H_EDIT_APPS, H_QUIT, H_TM_SKIP, H_BRI, H_CLAUDE, H_NEXTEV, H_SHELF_CLEAR,
       H_DAY = 100, H_APP = 200, H_EVT = 300, H_TM_PRE = 400, H_Q = 420, H_SET = 440, H_SEG_ALERT = 460, H_SEG_SIZE = 470, H_SEG_OPA = 475, H_ACC = 480, H_SEG_TMODE = 486, H_PICK = 490, H_TM_MODE = 495, H_TAB2 = 499, H_SHELF = 600, H_SHELF_DEL = 650 };

// ---------------------------------------------------------------- utilidades
template <class T> static void SafeRelease(T*& p) { if (p) { p->Release(); p = nullptr; } }
static float clampf(float v, float a, float b) { return v < a ? a : (v > b ? b : v); }

// ---------------------------------------------------------------- estado compartido con el hilo de fondo
struct MediaInfo {
    bool has = false, playing = false;
    std::wstring title, artist, app;
    std::vector<BYTE> art, artSmall; int artPx = 0, artSPx = 0;
    unsigned artVer = 0;
    D2D1_COLOR_F accent{1, 1, 1, 1};
};
struct StatsInfo { float cpuT = -1, gpuT = -1, cpuU = -1, gpuU = -1, ram = -1; };

static std::mutex gMx;
static MediaInfo gMediaShared;
static StatsInfo gStatsShared;
static std::atomic<bool> gExpandedA{false}, gQuit{false}, gVisibleA{true}, gPollSoon{false};
static HANDLE gWake;
static HWND gHwnd;
static std::wstring gCfgDir, gCalFile;

// eventos del calendario: día = días desde 1970-01-01 (hora local); minutos desde las 00:00, -1 = todo el día
struct CalEvent { long day; int start, end; std::wstring title, loc; D2D1_COLOR_F color; };
static std::vector<CalEvent> gEventsShared;

static long daysFromCivil(int y, unsigned m, unsigned d) {
    y -= m <= 2;
    const long era = (y >= 0 ? y : y - 399) / 400;
    const unsigned yoe = (unsigned)(y - era * 400);
    const unsigned doy = (153 * (m > 2 ? m - 3 : m + 9) + 2) / 5 + d - 1;
    const unsigned doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    return era * 146097 + (long)doe - 719468;
}
static void civilFromDays(long z, int& y, int& m, int& d) {
    z += 719468;
    const long era = (z >= 0 ? z : z - 146096) / 146097;
    const unsigned doe = (unsigned)(z - era * 146097);
    const unsigned yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    const unsigned doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    const unsigned mp = (5 * doy + 2) / 153;
    d = (int)(doy - (153 * mp + 2) / 5 + 1);
    m = (int)(mp < 10 ? mp + 3 : mp - 9);
    y = (int)(yoe + era * 400) + (m <= 2);
}
static int wdMon(long day) { return (int)(((day + 3) % 7 + 7) % 7); }  // 0 = lunes
static int dim(int y, int m) {
    static const int d[] = {31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31};
    return (m == 2 && ((y % 4 == 0 && y % 100 != 0) || y % 400 == 0)) ? 29 : d[m - 1];
}
static long todayNum() { SYSTEMTIME st; GetLocalTime(&st); return daysFromCivil(st.wYear, st.wMonth, st.wDay); }

// ================================================================ HILO DE FONDO: música + sensores
namespace bg {
static void** VT(void* p) { return *(void***)p; }
typedef HRESULT(STDMETHODCALLTYPE* FnObj)(void*, void**);
typedef HRESULT(STDMETHODCALLTYPE* FnHs)(void*, HSTRING*);
typedef HRESULT(STDMETHODCALLTYPE* FnInt)(void*, int*);
static void rel(void*& p) { if (p) { ((IUnknown*)p)->Release(); p = nullptr; } }

static const IID IID_MgrStatics = {0x2050c4ee, 0x11a0, 0x57de, {0xae, 0xd7, 0xc9, 0x7c, 0x70, 0x33, 0x82, 0x45}};
static const IID IID_AsyncInfo = {0x00000036, 0, 0, {0xC0, 0, 0, 0, 0, 0, 0, 0x46}};

static void* waitAsync(void* op, int ms = 1500) {
    if (!op) return nullptr;
    IAsyncInfo* ai = nullptr; void* r = nullptr;
    if (SUCCEEDED(((IUnknown*)op)->QueryInterface(IID_AsyncInfo, (void**)&ai))) {
        AsyncStatus st = Started;
        for (int t = 0; t < ms; t += 5) { ai->get_Status(&st); if (st != Started) break; Sleep(5); }
        if (st == Completed) ((FnObj)VT(op)[8])(op, &r);   // IAsyncOperation<T>::GetResults
        else if (st == Started) ai->Cancel();
        ai->Release();
    }
    rel(op);
    return r;
}
static std::wstring hs(HSTRING h) {
    if (!h) return L"";
    UINT32 n; const wchar_t* s = WindowsGetStringRawBuffer(h, &n);
    std::wstring r(s, n); WindowsDeleteString(h); return r;
}
static std::wstring prettyApp(const std::wstring& id) {
    std::wstring s = id, l;
    size_t b = s.find(L'!'); if (b != std::wstring::npos) s = s.substr(b + 1);
    if (s.size() > 4 && _wcsicmp(s.c_str() + s.size() - 4, L".exe") == 0) s.resize(s.size() - 4);
    size_t d = s.rfind(L'.'); if (d != std::wstring::npos && d + 1 < s.size()) s = s.substr(d + 1);
    for (auto c : s) l += (wchar_t)towlower(c);
    if (l == L"zunemusic" || l == L"media") return L"Reproductor multimedia";
    if (l == L"msedge") return L"Microsoft Edge";
    if (l == L"chrome") return L"Google Chrome";
    if (l == L"firefox") return L"Firefox";
    if (l == L"spotify") return L"Spotify";
    if (!s.empty()) s[0] = towupper(s[0]);
    return s;
}

static IWICImagingFactory* wic = nullptr;

// decodifica la carátula: recorte cuadrado centrado, 2 tamaños, color de acento
static bool decodeArt(IStream* is, MediaInfo& mi) {
    IWICBitmapDecoder* dec = nullptr; IWICBitmapFrameDecode* fr = nullptr;
    bool ok = false;
    if (SUCCEEDED(wic->CreateDecoderFromStream(is, nullptr, WICDecodeMetadataCacheOnDemand, &dec)) && SUCCEEDED(dec->GetFrame(0, &fr))) {
        UINT w, h; fr->GetSize(&w, &h);
        UINT s = w < h ? w : h;
        WICRect rc{(INT)(w - s) / 2, (INT)(h - s) / 2, (INT)s, (INT)s};
        IWICBitmapClipper* clip = nullptr;
        if (s > 0 && SUCCEEDED(wic->CreateBitmapClipper(&clip)) && SUCCEEDED(clip->Initialize(fr, &rc))) {
            auto grab = [&](UINT px, std::vector<BYTE>& out) {
                IWICBitmapScaler* sc = nullptr; IWICFormatConverter* cv = nullptr; bool g = false;
                if (SUCCEEDED(wic->CreateBitmapScaler(&sc)) && SUCCEEDED(sc->Initialize(clip, px, px, WICBitmapInterpolationModeFant)) &&
                    SUCCEEDED(wic->CreateFormatConverter(&cv)) &&
                    SUCCEEDED(cv->Initialize(sc, GUID_WICPixelFormat32bppPBGRA, WICBitmapDitherTypeNone, nullptr, 0, WICBitmapPaletteTypeCustom))) {
                    out.resize(px * px * 4);
                    g = SUCCEEDED(cv->CopyPixels(nullptr, px * 4, (UINT)out.size(), out.data()));
                }
                SafeRelease(cv); SafeRelease(sc); return g;
            };
            if (grab(176, mi.art) && grab(64, mi.artSmall)) {
                mi.artPx = 176; mi.artSPx = 64; ok = true;
                // acento: media ponderada por saturación, luego se aclara
                double R = 0, G = 0, B = 0, W = 0;
                for (size_t i = 0; i < mi.artSmall.size(); i += 4) {
                    double b = mi.artSmall[i] / 255.0, g = mi.artSmall[i + 1] / 255.0, r = mi.artSmall[i + 2] / 255.0;
                    double mx = fmax(r, fmax(g, b)), mn = fmin(r, fmin(g, b));
                    double wt = (mx - mn) * mx + 0.02;
                    R += r * wt; G += g * wt; B += b * wt; W += wt;
                }
                R /= W; G /= W; B /= W;
                double mx = fmax(R, fmax(G, B)), mn = fmin(R, fmin(G, B));
                if (mx - mn < 0.08) mi.accent = D2D1::ColorF(0.92f, 0.92f, 0.95f);
                else { double k = 1.0 / mx; mi.accent = D2D1::ColorF((float)fmin(1, R * k), (float)fmin(1, G * k), (float)fmin(1, B * k)); }
            }
        }
        SafeRelease(clip);
    }
    SafeRelease(fr); SafeRelease(dec);
    return ok;
}

static void* mgr = nullptr;
static DWORD lastMgrTry = 0;
static std::wstring lastKey;

static void pollMedia() {
    if (!mgr && GetTickCount() - lastMgrTry > 5000) {
        lastMgrTry = GetTickCount();
        HSTRING cls; const wchar_t* cn = L"Windows.Media.Control.GlobalSystemMediaTransportControlsSessionManager";
        WindowsCreateString(cn, (UINT32)wcslen(cn), &cls);
        void* st = nullptr;
        if (SUCCEEDED(RoGetActivationFactory(cls, IID_MgrStatics, &st))) {
            void* op = nullptr;
            if (SUCCEEDED(((FnObj)VT(st)[6])(st, &op))) mgr = waitAsync(op, 3000);
            rel(st);
        }
        WindowsDeleteString(cls);
    }
    MediaInfo mi;
    bool artChanged = false;
    if (mgr) {
        void* ses = nullptr;
        HRESULT hr = ((FnObj)VT(mgr)[6])(mgr, &ses);           // GetCurrentSession
        if (FAILED(hr)) { rel(mgr); }
        else if (ses) {
            mi.has = true;
            HSTRING h = nullptr; ((FnHs)VT(ses)[6])(ses, &h); mi.app = prettyApp(hs(h));
            void* pi = nullptr;
            if (SUCCEEDED(((FnObj)VT(ses)[9])(ses, &pi)) && pi) {  // GetPlaybackInfo
                int s = 0; ((FnInt)VT(pi)[7])(pi, &s); mi.playing = (s == 4); rel(pi);
            }
            void* op = nullptr; void* props = nullptr;
            if (SUCCEEDED(((FnObj)VT(ses)[7])(ses, &op))) props = waitAsync(op);  // TryGetMediaPropertiesAsync
            if (props) {
                h = nullptr; ((FnHs)VT(props)[6])(props, &h); mi.title = hs(h);
                h = nullptr; ((FnHs)VT(props)[9])(props, &h); mi.artist = hs(h);
                if (mi.artist.empty()) { h = nullptr; ((FnHs)VT(props)[8])(props, &h); mi.artist = hs(h); }
                std::wstring key = mi.app + L"\n" + mi.title + L"\n" + mi.artist;
                if (key != lastKey) {
                    artChanged = true;
                    void* ref = nullptr;
                    if (SUCCEEDED(((FnObj)VT(props)[15])(props, &ref)) && ref) {  // Thumbnail
                        void* op2 = nullptr; void* ras = nullptr;
                        if (SUCCEEDED(((FnObj)VT(ref)[6])(ref, &op2))) ras = waitAsync(op2, 2500);  // OpenReadAsync
                        if (ras) {
                            IStream* is = nullptr;
                            if (SUCCEEDED(CreateStreamOverRandomAccessStream((IUnknown*)ras, IID_IStream, (void**)&is))) {
                                decodeArt(is, mi); is->Release();
                            }
                            rel(ras);
                        }
                        rel(ref);
                    }
                    // a veces la carátula llega un poco después que el título: reintentar en la siguiente vuelta
                    if (!mi.art.empty() || mi.title.empty()) lastKey = key;
                }
                rel(props);
            }
            rel(ses);
        }
    }
    std::lock_guard<std::mutex> lk(gMx);
    MediaInfo& o = gMediaShared;
    bool changed = artChanged || o.has != mi.has || o.playing != mi.playing || o.title != mi.title || o.artist != mi.artist || o.app != mi.app;
    if (!changed) return;
    if (!artChanged) { mi.art.swap(o.art); mi.artSmall.swap(o.artSmall); mi.artPx = o.artPx; mi.artSPx = o.artSPx; mi.accent = o.accent; mi.artVer = o.artVer; }
    else mi.artVer = o.artVer + 1;
    o = std::move(mi);
    PostMessage(gHwnd, WM_APP_MEDIA, 0, 0);
}

// ------------- sensores (solo con el panel abierto; se cierran al plegar)
typedef int (*nvInit_t)(); typedef int (*nvShut_t)();
typedef int (*nvHandle_t)(unsigned, void**);
typedef int (*nvTemp_t)(void*, int, unsigned*);
struct nvUtil { unsigned gpu, mem; };
typedef int (*nvUtil_t)(void*, nvUtil*);
static HMODULE nv = nullptr; static void* nvDev = nullptr;
static nvTemp_t nvTemp; static nvUtil_t nvUtilF; static nvShut_t nvShut;
static PDH_HQUERY pq = nullptr; static PDH_HCOUNTER pc = nullptr;
static ULONGLONG lastIdle = 0, lastTotal = 0;
static bool sensorsOpen = false;

static ULONGLONG ft(FILETIME f) { return ((ULONGLONG)f.dwHighDateTime << 32) | f.dwLowDateTime; }

static void openSensors() {
    if (sensorsOpen) return;
    sensorsOpen = true;
    if (PdhOpenQueryW(nullptr, 0, &pq) == ERROR_SUCCESS) {
        if (PdhAddEnglishCounterW(pq, L"\\Thermal Zone Information(*)\\High Precision Temperature", 0, &pc) != ERROR_SUCCESS) pc = nullptr;
        PdhCollectQueryData(pq);
    }
    nv = LoadLibraryExW(L"nvml.dll", nullptr, LOAD_LIBRARY_SEARCH_SYSTEM32);
    if (!nv) nv = LoadLibraryW(L"C:\\Program Files\\NVIDIA Corporation\\NVSMI\\nvml.dll");
    if (nv) {
        auto init = (nvInit_t)GetProcAddress(nv, "nvmlInit_v2");
        auto hnd = (nvHandle_t)GetProcAddress(nv, "nvmlDeviceGetHandleByIndex_v2");
        nvTemp = (nvTemp_t)GetProcAddress(nv, "nvmlDeviceGetTemperature");
        nvUtilF = (nvUtil_t)GetProcAddress(nv, "nvmlDeviceGetUtilizationRates");
        nvShut = (nvShut_t)GetProcAddress(nv, "nvmlShutdown");
        if (!(init && hnd && nvTemp && init() == 0 && hnd(0, &nvDev) == 0)) { nvDev = nullptr; }
    }
    FILETIME i, k, u; GetSystemTimes(&i, &k, &u); lastIdle = ft(i); lastTotal = ft(k) + ft(u);
}
static void closeSensors() {
    if (!sensorsOpen) return;
    sensorsOpen = false;
    if (pq) { PdhCloseQuery(pq); pq = nullptr; pc = nullptr; }
    if (nv) { if (nvDev && nvShut) nvShut(); FreeLibrary(nv); nv = nullptr; nvDev = nullptr; }
}
static void pollStats() {
    StatsInfo s;
    FILETIME i, k, u; GetSystemTimes(&i, &k, &u);
    ULONGLONG id = ft(i), tot = ft(k) + ft(u);
    if (tot > lastTotal) s.cpuU = 100.f * (1.f - (float)(id - lastIdle) / (float)(tot - lastTotal));
    lastIdle = id; lastTotal = tot;
    MEMORYSTATUSEX ms{sizeof ms}; GlobalMemoryStatusEx(&ms); s.ram = (float)ms.dwMemoryLoad;
    if (pq && pc && PdhCollectQueryData(pq) == ERROR_SUCCESS) {
        DWORD sz = 0, n = 0;
        PdhGetFormattedCounterArrayW(pc, PDH_FMT_DOUBLE, &sz, &n, nullptr);
        if (sz) {
            std::vector<BYTE> buf(sz);
            auto* it = (PDH_FMT_COUNTERVALUE_ITEM_W*)buf.data();
            if (PdhGetFormattedCounterArrayW(pc, PDH_FMT_DOUBLE, &sz, &n, it) == ERROR_SUCCESS)
                for (DWORD j = 0; j < n; j++) {
                    double c = it[j].FmtValue.doubleValue / 10.0 - 273.15;
                    if (c > 5 && c < 125 && c > s.cpuT) s.cpuT = (float)c;
                }
        }
    }
    if (nvDev) {
        unsigned t = 0; if (nvTemp(nvDev, 0, &t) == 0) s.gpuT = (float)t;
        nvUtil ut{}; if (nvUtilF && nvUtilF(nvDev, &ut) == 0) s.gpuU = (float)ut.gpu;
    }
    { std::lock_guard<std::mutex> lk(gMx); gStatsShared = s; }
    PostMessage(gHwnd, WM_APP_STATS, 0, 0);
}

// ------------- calendario (direcciones iCal, p. ej. la "dirección secreta" de Google Calendar)
static bool httpGet(std::wstring url, std::string& out) {
    if (url.rfind(L"webcal://", 0) == 0) url = L"https://" + url.substr(9);
    URL_COMPONENTS uc{}; uc.dwStructSize = sizeof uc;
    wchar_t host[256], path[4096], extra[4096];
    uc.lpszHostName = host; uc.dwHostNameLength = 256;
    uc.lpszUrlPath = path; uc.dwUrlPathLength = 4096;
    uc.lpszExtraInfo = extra; uc.dwExtraInfoLength = 4096;
    if (!WinHttpCrackUrl(url.c_str(), 0, 0, &uc)) return false;
    std::wstring full = std::wstring(path) + extra;
    bool ok = false;
    HINTERNET s = WinHttpOpen(L"islita/1.0", WINHTTP_ACCESS_TYPE_AUTOMATIC_PROXY, WINHTTP_NO_PROXY_NAME, WINHTTP_NO_PROXY_BYPASS, 0);
    if (!s) return false;
    WinHttpSetTimeouts(s, 5000, 5000, 10000, 15000);
    HINTERNET c = WinHttpConnect(s, host, uc.nPort, 0);
    HINTERNET r = c ? WinHttpOpenRequest(c, L"GET", full.c_str(), nullptr, WINHTTP_NO_REFERER, WINHTTP_DEFAULT_ACCEPT_TYPES,
                                         uc.nScheme == INTERNET_SCHEME_HTTPS ? WINHTTP_FLAG_SECURE : 0) : nullptr;
    if (r && WinHttpSendRequest(r, WINHTTP_NO_ADDITIONAL_HEADERS, 0, WINHTTP_NO_REQUEST_DATA, 0, 0, 0) && WinHttpReceiveResponse(r, nullptr)) {
        DWORD code = 0, sz = sizeof code;
        WinHttpQueryHeaders(r, WINHTTP_QUERY_STATUS_CODE | WINHTTP_QUERY_FLAG_NUMBER, nullptr, &code, &sz, nullptr);
        if (code == 200) {
            out.clear(); char buf[16384]; DWORD n = 0;
            while (WinHttpReadData(r, buf, sizeof buf, &n) && n) { out.append(buf, n); if (out.size() > 30000000) break; }
            ok = !out.empty();
        }
    }
    if (r) WinHttpCloseHandle(r);
    if (c) WinHttpCloseHandle(c);
    WinHttpCloseHandle(s);
    return ok;
}
static bool readAll(const std::wstring& p, std::string& out) {
    HANDLE f = CreateFileW(p.c_str(), GENERIC_READ, FILE_SHARE_READ, nullptr, OPEN_EXISTING, 0, nullptr);
    if (f == INVALID_HANDLE_VALUE) return false;
    out.clear(); char buf[65536]; DWORD n;
    while (ReadFile(f, buf, sizeof buf, &n, nullptr) && n) out.append(buf, n);
    CloseHandle(f); return true;
}
static void writeAll(const std::wstring& p, const std::string& s) {
    HANDLE f = CreateFileW(p.c_str(), GENERIC_WRITE, 0, nullptr, CREATE_ALWAYS, 0, nullptr);
    if (f == INVALID_HANDLE_VALUE) return;
    DWORD w; WriteFile(f, s.data(), (DWORD)s.size(), &w, nullptr); CloseHandle(f);
}
static std::wstring utf8(const std::string& s) {
    std::string u; u.reserve(s.size());
    for (size_t i = 0; i < s.size(); i++) {  // quitar escapes de iCal
        if (s[i] == '\\' && i + 1 < s.size()) { char n = s[++i]; u += (n == 'n' || n == 'N') ? ' ' : n; }
        else u += s[i];
    }
    int n = MultiByteToWideChar(CP_UTF8, 0, u.data(), (int)u.size(), nullptr, 0);
    std::wstring w(n, 0); if (n) MultiByteToWideChar(CP_UTF8, 0, u.data(), (int)u.size(), &w[0], n);
    return w;
}
struct DT { long day = 0; int min = 0; bool allDay = false, ok = false; };
static DT parseDT(const std::string& params, const std::string& v) {
    DT r; if (v.size() < 8) return r;
    int y = atoi(v.substr(0, 4).c_str()), mo = atoi(v.substr(4, 2).c_str()), d = atoi(v.substr(6, 2).c_str());
    if (mo < 1 || mo > 12 || d < 1 || d > 31) return r;
    if (v.size() >= 13 && v[8] == 'T' && params.find("VALUE=DATE;") == std::string::npos && params != "VALUE=DATE") {
        int H = atoi(v.substr(9, 2).c_str()), Mi = atoi(v.substr(11, 2).c_str());
        if (v.size() >= 16 && v[15] == 'Z') {  // UTC -> hora local
            SYSTEMTIME u{(WORD)y, (WORD)mo, 0, (WORD)d, (WORD)H, (WORD)Mi, 0, 0}, l;
            if (SystemTimeToTzSpecificLocalTime(nullptr, &u, &l)) { y = l.wYear; mo = l.wMonth; d = l.wDay; H = l.wHour; Mi = l.wMinute; }
        }
        r.min = H * 60 + Mi;
    } else r.allDay = true;
    r.day = daysFromCivil(y, mo, d); r.ok = true;
    return r;
}
static long long dkey(long day, int min) { return (long long)day * 1440 + min; }
struct VEv { std::string uid, rrule; std::wstring title, loc; DT s, e, rid; bool hasE = false, cancelled = false; std::vector<long long> ex; };

static void parseIcs(std::string& txt, D2D1_COLOR_F color, long w0, long w1, std::vector<CalEvent>& out) {
    std::vector<VEv> evs; VEv cur; bool in = false;
    std::string line;
    size_t p = 0, n = txt.size();
    while (p < n) {
        // línea lógica (las que empiezan por espacio continúan la anterior)
        line.clear();
        while (p < n) {
            size_t e = txt.find('\n', p); if (e == std::string::npos) e = n;
            size_t le = e; if (le > p && txt[le - 1] == '\r') le--;
            line.append(txt, p, le - p); p = e + 1;
            if (p < n && (txt[p] == ' ' || txt[p] == '\t')) { p++; continue; }
            break;
        }
        if (line == "BEGIN:VEVENT") { in = true; cur = VEv(); continue; }
        if (line == "END:VEVENT") { in = false; evs.push_back(std::move(cur)); continue; }
        if (!in) continue;
        size_t colon = line.find(':'); if (colon == std::string::npos) continue;
        size_t q = line.find('"');
        if (q != std::string::npos && q < colon) { size_t q2 = line.find('"', q + 1); if (q2 != std::string::npos) colon = line.find(':', q2); if (colon == std::string::npos) continue; }
        std::string head = line.substr(0, colon), val = line.substr(colon + 1);
        size_t sc = head.find(';');
        std::string name = head.substr(0, sc), params = sc == std::string::npos ? "" : head.substr(sc + 1);
        if (name == "DTSTART") cur.s = parseDT(params, val);
        else if (name == "DTEND") { cur.e = parseDT(params, val); cur.hasE = cur.e.ok; }
        else if (name == "SUMMARY") cur.title = utf8(val);
        else if (name == "LOCATION") cur.loc = utf8(val);
        else if (name == "UID") cur.uid = val;
        else if (name == "RRULE") cur.rrule = val;
        else if (name == "RECURRENCE-ID") cur.rid = parseDT(params, val);
        else if (name == "STATUS" && val == "CANCELLED") cur.cancelled = true;
        else if (name == "EXDATE") {
            size_t a = 0;
            while (a <= val.size()) {
                size_t c = val.find(',', a); if (c == std::string::npos) c = val.size();
                DT d = parseDT(params, val.substr(a, c - a));
                if (d.ok) cur.ex.push_back(dkey(d.day, d.allDay ? 0 : d.min));
                a = c + 1;
            }
        }
    }
    txt.clear(); txt.shrink_to_fit();

    std::set<std::string> overridden;  // ocurrencias movidas o canceladas de una serie
    for (auto& v : evs) if (v.rid.ok) overridden.insert(v.uid + "#" + std::to_string(dkey(v.rid.day, v.rid.allDay ? 0 : v.rid.min)));

    auto add = [&](const VEv& v, long day) {
        int span = 1;
        if (v.s.allDay && v.hasE && v.e.allDay) span = (int)std::clamp(v.e.day - v.s.day, 1L, 60L);
        for (int i = 0; i < span; i++) {
            long d = day + i;
            if (d < w0 || d > w1) continue;
            CalEvent c; c.day = d; c.start = v.s.allDay ? -1 : v.s.min; c.end = -1;
            if (!v.s.allDay && v.hasE) { long dur = (v.e.day - v.s.day) * 1440 + v.e.min - v.s.min; c.end = (int)std::min<long>(c.start + std::max(0L, dur), 1440); }
            c.title = v.title.empty() ? L"(Sin título)" : v.title; c.loc = v.loc; c.color = color;
            out.push_back(std::move(c));
        }
    };
    for (auto& v : evs) {
        if (!v.s.ok || v.cancelled) continue;
        if (v.rid.ok || v.rrule.empty()) { add(v, v.s.day); continue; }
        // RRULE
        std::string freq; int interval = 1, count = 0, bymd = 0; long untilDay = LONG_MAX;
        std::vector<std::pair<int, int>> byday;  // (ordinal, día 0=lunes)
        size_t a = 0;
        while (a < v.rrule.size()) {
            size_t c = v.rrule.find(';', a); if (c == std::string::npos) c = v.rrule.size();
            std::string kv = v.rrule.substr(a, c - a); a = c + 1;
            size_t eq = kv.find('='); if (eq == std::string::npos) continue;
            std::string k = kv.substr(0, eq), val = kv.substr(eq + 1);
            if (k == "FREQ") freq = val;
            else if (k == "INTERVAL") interval = std::max(1, atoi(val.c_str()));
            else if (k == "COUNT") count = atoi(val.c_str());
            else if (k == "UNTIL") { DT u = parseDT("", val); if (u.ok) untilDay = u.day; }
            else if (k == "BYMONTHDAY") bymd = atoi(val.c_str());
            else if (k == "BYDAY") {
                static const char* WD[] = {"MO", "TU", "WE", "TH", "FR", "SA", "SU"};
                size_t b = 0;
                while (b < val.size()) {
                    size_t c2 = val.find(',', b); if (c2 == std::string::npos) c2 = val.size();
                    std::string it = val.substr(b, c2 - b); b = c2 + 1;
                    if (it.size() < 2) continue;
                    int ord = it.size() > 2 ? atoi(it.substr(0, it.size() - 2).c_str()) : 0;
                    for (int i = 0; i < 7; i++) if (it.compare(it.size() - 2, 2, WD[i]) == 0) byday.push_back({ord, i});
                }
            }
        }
        std::set<long long> ex(v.ex.begin(), v.ex.end());
        int smin = v.s.allDay ? 0 : v.s.min;
        long emitted = 0;
        auto emit = [&](long day) -> bool {
            if (day > untilDay || day > w1) return false;
            if (count && emitted >= count) return false;
            emitted++;
            long long k = dkey(day, smin);
            if (ex.count(k) || overridden.count(v.uid + "#" + std::to_string(k))) return true;
            add(v, day); return true;
        };
        if (freq == "DAILY") {
            for (long d = v.s.day; ; d += interval) if (!emit(d)) break;
        } else if (freq == "WEEKLY") {
            std::vector<int> wds;
            for (auto& b : byday) wds.push_back(b.second);
            if (wds.empty()) wds.push_back(wdMon(v.s.day));
            std::sort(wds.begin(), wds.end());
            bool go = true;
            for (long ws = v.s.day - wdMon(v.s.day); go; ws += 7L * interval)
                for (int wd : wds) { long d = ws + wd; if (d < v.s.day) continue; if (!emit(d)) { go = false; break; } }
        } else if (freq == "MONTHLY" || freq == "YEARLY") {
            int y0, m0, d0; civilFromDays(v.s.day, y0, m0, d0);
            bool yearly = freq == "YEARLY";
            bool go = true;
            for (int i = 0; go && i < 1200; i += interval) {
                int yy, mm;
                if (yearly) { yy = y0 + i; mm = m0; } else { yy = y0 + (m0 - 1 + i) / 12; mm = (m0 - 1 + i) % 12 + 1; }
                long first = daysFromCivil(yy, mm, 1); int nd = dim(yy, mm);
                if (first > w1) break;
                std::vector<long> days;
                if (!byday.empty()) {
                    for (auto& b : byday) {
                        int ord = b.first ? b.first : 1;
                        long d;
                        if (ord > 0) d = first + (b.second - wdMon(first) + 7) % 7 + (ord - 1) * 7L;
                        else { long last = first + nd - 1; d = last - (wdMon(last) - b.second + 7) % 7 + (ord + 1) * 7L; }
                        if (d >= first && d < first + nd) days.push_back(d);
                    }
                } else {
                    int dd = bymd > 0 ? bymd : (bymd < 0 ? nd + bymd + 1 : d0);
                    if (dd >= 1 && dd <= nd) days.push_back(first + dd - 1);
                }
                std::sort(days.begin(), days.end());
                for (long d : days) { if (d < v.s.day) continue; if (!emit(d)) { go = false; break; } }
            }
        } else add(v, v.s.day);
    }
}

struct CalSrc { std::wstring url; bool holiday; };
static std::vector<CalSrc> readCalFile() {
    std::vector<CalSrc> r;
    if (GetFileAttributesW(gCalFile.c_str()) == INVALID_FILE_ATTRIBUTES) {
        writeAll(gCalFile,
            "# Calendarios de la isla: una linea por calendario con el formato\n"
            "#   Nombre | direccion iCal (.ics)\n"
            "# Tu Google Calendar: calendar.google.com > Configuracion > tu calendario >\n"
            "#   \"Integrar el calendario\" > \"Direccion secreta en formato iCal\". Copiala y pegala abajo.\n"
            "Festivos | https://calendar.google.com/calendar/ical/es.spain%23holiday%40group.v.calendar.google.com/public/basic.ics\n");
    }
    std::string raw; readAll(gCalFile, raw);
    size_t p = 0;
    while (p < raw.size()) {
        size_t e = raw.find('\n', p); if (e == std::string::npos) e = raw.size();
        std::string l = raw.substr(p, e - p); p = e + 1;
        while (!l.empty() && (l.back() == '\r' || l.back() == ' ')) l.pop_back();
        size_t s = l.find_first_not_of(" \t"); if (s == std::string::npos || l[s] == '#') continue;
        size_t bar = l.find('|'); std::string u = bar == std::string::npos ? l.substr(s) : l.substr(bar + 1);
        size_t a = u.find_first_not_of(" \t"); if (a == std::string::npos) continue; u = u.substr(a);
        if (u.rfind("http", 0) != 0 && u.rfind("webcal", 0) != 0) continue;
        r.push_back({utf8(u), u.find("holiday") != std::string::npos});
    }
    return r;
}
static FILETIME calStamp{};
static DWORD lastCalFetch = 0; static bool calEver = false, calFailed = false;
static void pollCalendar(bool expanded) {
    WIN32_FILE_ATTRIBUTE_DATA fa{}; GetFileAttributesExW(gCalFile.c_str(), GetFileExInfoStandard, &fa);
    bool changed = CompareFileTime(&fa.ftLastWriteTime, &calStamp) != 0;
    DWORD now = GetTickCount(), age = now - lastCalFetch;
    // sin red se reintenta cada 2 min (antes, con el panel abierto, reintentaba cada segundo y atascaba este hilo)
    DWORD every = calFailed ? 2u * 60000u : (expanded ? 3u : 15u) * 60000u;
    if (calEver && !changed && age < every) return;
    lastCalFetch = now; calEver = true;
    auto srcs = readCalFile();
    WIN32_FILE_ATTRIBUTE_DATA fb{}; GetFileAttributesExW(gCalFile.c_str(), GetFileExInfoStandard, &fb); calStamp = fb.ftLastWriteTime;
    static const D2D1_COLOR_F PAL[] = {{0.04f, 0.52f, 1.f, 1}, {0.75f, 0.35f, 0.95f, 1}, {0.19f, 0.82f, 0.35f, 1}, {1.f, 0.62f, 0.04f, 1}, {1.f, 0.22f, 0.37f, 1}, {0.39f, 0.82f, 1.f, 1}};
    long t = todayNum();
    std::vector<CalEvent> all; bool failed = false; int ci = 0;
    for (size_t i = 0; i < srcs.size(); i++) {
        std::string body; std::wstring cache = gCfgDir + L"\\cache_" + std::to_wstring(i) + L".ics";
        if (httpGet(srcs[i].url, body) && body.find("BEGIN:VCALENDAR") != std::string::npos) writeAll(cache, body);
        else { failed = true; body.clear(); readAll(cache, body); }
        D2D1_COLOR_F c = srcs[i].holiday ? D2D1_COLOR_F{1.f, 0.42f, 0.38f, 1} : PAL[ci++ % 6];
        parseIcs(body, c, t - 62, t + 400, all);
    }
    std::stable_sort(all.begin(), all.end(), [](const CalEvent& a, const CalEvent& b) { return a.day != b.day ? a.day < b.day : a.start < b.start; });
    calFailed = failed;  // sin red: reintentar en 2 min (mientras, la copia guardada)
    { std::lock_guard<std::mutex> lk(gMx); gEventsShared.swap(all); }
    PostMessage(gHwnd, WM_APP_CAL, 0, 0);
}

static void run() {
    // este hilo nunca tiene prisa: modo eficiencia (EcoQoS) y prioridad mínima
    { struct { ULONG Version, ControlMask, StateMask; } t{1, 1, 1}; SetThreadInformation(GetCurrentThread(), (THREAD_INFORMATION_CLASS)3 /*ThreadPowerThrottling*/, &t, sizeof t); }
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_LOWEST);
    RoInitialize(RO_INIT_MULTITHREADED);
    CoCreateInstance(CLSID_WICImagingFactory, nullptr, CLSCTX_INPROC_SERVER, IID_PPV_ARGS(&wic));
    DWORD collapsedAt = 0;
    while (!gQuit) {
        if (gPollSoon.exchange(false)) Sleep(280);
        bool vis = gVisibleA, exp = gExpandedA;
        if (vis) pollMedia();
        if (vis) pollCalendar(exp);
        if (exp) { collapsedAt = 0; openSensors(); pollStats(); }
        else if (sensorsOpen) {
            if (!collapsedAt) collapsedAt = GetTickCount();
            else if (GetTickCount() - collapsedAt > 8000) closeSensors();
        }
        // cada cuánto mirar la música: más a menudo solo si está sonando algo
        DWORD wait;
        { std::lock_guard<std::mutex> lk(gMx); wait = !gMediaShared.has ? 6000 : (gMediaShared.playing ? 2000 : 4000); }
        if (exp) wait = 1000; else if (!vis) wait = 10000;
        WaitForSingleObject(gWake, wait);
    }
    closeSensors();
    rel(mgr);
    SafeRelease(wic);
    RoUninitialize();
}
}  // namespace bg

// ================================================================ UI
static ID2D1Factory* d2d;
static IDWriteFactory* dw;
static IWICImagingFactory* wicUI;
static ID2D1DCRenderTarget* dcrt;
static ID2D1RenderTarget* rt;          // destino actual (la ventana o la caché)
static ID2D1BitmapRenderTarget* cacheRT; static bool cacheValid = false;
static ID2D1SolidColorBrush* br;
static ID2D1StrokeStyle* roundStroke;
static ID2D1StrokeStyle* dashStroke;
static IDWriteTypography* tnum;
static IDWriteTextFormat *fTime, *fSmall, *fTitle, *fBody, *fCalHead, *fCal, *fCalB, *fRing, *fTiny, *fApp, *fGlyph, *fIcon, *fIconL, *fBig, *fMid, *fTab;

static HDC memDC; static HBITMAP dib, oldBmp; static int dibW = 0, dibH = 0;
static float scale = 1; static UINT dpi = 96;
static RECT mon;

static MediaInfo media;            // copia de la UI
static StatsInfo stats;
static ID2D1Bitmap *artBmp, *artSBmp; static unsigned artVerUI = ~0u;

struct App { std::wstring name, target, icon, args; ID2D1Bitmap* bmp = nullptr; };
static std::vector<App> apps; static bool iconsLoaded = false; static FILETIME appsStamp{};
static std::wstring cfgDir, appsFile;

static std::vector<CalEvent> events;  // copia de la UI
static int selDay = 0;                // 0 = vista de mes; si no, día abierto en la agenda

// ---------------------------------------------------------------- ajustes
struct Settings { bool discreetOn = true, hoverOpen = false, hideFull = true, eq = true, battery = true, alerts = true, autostart = true; int alertMins = 60, size = 1, accent = 0, opacity = 1, transMode = 0; };  // transMode: 0 siempre, 1 con el ratón, 2 sin el ratón
static Settings cfg;
static const D2D1_COLOR_F ACCENTS[6] = {{1.f, 0.271f, 0.227f, 1}, {1.f, 0.624f, 0.04f, 1}, {0.188f, 0.82f, 0.345f, 1},
                                        {0.04f, 0.52f, 1.f, 1}, {0.75f, 0.35f, 0.95f, 1}, {1.f, 0.216f, 0.373f, 1}};
static D2D1_COLOR_F ACC() { return ACCENTS[cfg.accent % 6]; }
static const float SIZES[3] = {0.9f, 1.f, 1.12f};
static const float OPACITIES[3] = {1.f, 0.8f, 0.62f};  // sólido, translúcido, cristal
static float bgAlpha() { return OPACITIES[cfg.opacity % 3]; }
static const int ALERTS[3] = {15, 30, 60};

// ---------------------------------------------------------------- estado
static bool expanded = false, hovered = false, visible = true;
static int gFlushes = 0;  // DwmFlush por fotograma (según la frecuencia de la pantalla)
static int view = 0, lastTab = 0;  // 0 inicio, 1 herramientas, 2 ajustes
static int hoverId = H_NONE, pressId = H_NONE;
static int calY, calM;  // mes mostrado (m 1..12)
// temporizador: 0 parado, 1 en marcha, 2 en pausa
static int tmState = 0; static ULONGLONG tmDur = 5 * 60000, tmEnd = 0, tmLeft = 5 * 60000;
static bool alertOn = false; static ULONGLONG alertAt = 0;
// cronómetro
static bool swRun = false; static ULONGLONG swStart = 0, swAcc = 0; static std::vector<ULONGLONG> laps;
// controles
static bool caffeine = false;
// pomodoro: fase 0 concentración, 1 descanso
static bool pomo = false; static int pomoPhase = 0, pomoCount = 0; static bool alertPomo = false;
// ruleta del temporizador (horas, minutos, segundos); pickT es la posición continua (sin dar la vuelta)
static int pick[3] = {0, 5, 0}; static float pickT[3] = {0, 5, 0}; static float pickCy = 0;
// arrastres: 0 nada, 1 volumen, 2 brillo, 3 ruleta
static int dragKind = 0, dragCol = -1; static float dragY0 = 0, dragPos0 = 0, dragLastY = 0, dragVel = 0; static ULONGLONG dragLastT = 0; static bool dragMoved = false;
static D2D1_RECT_F briRect;
// vistas del panel
enum { V_HOME, V_TOOLS, V_SHELF, V_SET };
// bandeja de archivos (se guardan rutas, no copias)
struct ShelfItem { std::wstring path, name; ID2D1Bitmap* bmp = nullptr; bool tried = false; };
static std::vector<ShelfItem> shelf; static std::wstring shelfFile;
static bool dropHover = false, draggingOut = false, openedByDrag = false;
static float pressX = 0, pressY = 0;
static int nextY = 0, nextM = 0, nextD = 0;
static IAudioEndpointVolume* vol = nullptr; static D2D1_RECT_F volRect;

struct Spring { float x, v = 0, t; bool settled() const { return fabsf(x - t) < 0.25f && fabsf(v) < 0.5f; } };
static Spring sw{CW_IDLE, 0, CW_IDLE}, sh{CH, 0, CH}, sr{CH / 2, 0, CH / 2};
static LARGE_INTEGER qpf, lastTick; static bool animating = false; static int tickIv = 0;
static double eqTime = 0; static ULONGLONG lastTickMs = 0;

struct Hit { D2D1_RECT_F r; int id; };
static std::vector<Hit> hits; static bool hitsOn = true;

static const wchar_t* DOW[] = {L"dom", L"lun", L"mar", L"mié", L"jue", L"vie", L"sáb"};
static const wchar_t* MON[] = {L"ene", L"feb", L"mar", L"abr", L"may", L"jun", L"jul", L"ago", L"sep", L"oct", L"nov", L"dic"};
static const wchar_t* MONL[] = {L"Enero", L"Febrero", L"Marzo", L"Abril", L"Mayo", L"Junio", L"Julio", L"Agosto", L"Septiembre", L"Octubre", L"Noviembre", L"Diciembre"};

// ---------------------------------------------------------------- micro-animaciones (valores que persiguen su objetivo)
struct Tween { float x, t, k; };
static std::map<int, Tween> tweens;
static float tw(int key, float target, float k = 16) {
    auto it = tweens.find(key);
    if (it == tweens.end()) { tweens[key] = {target, target, k}; return target; }
    it->second.t = target; it->second.k = k;
    return it->second.x;
}
static void twSnap(int key, float v) { tweens[key] = {v, v, 16}; }
static void twFrom(int key, float from, float to, float k) { tweens[key] = {from, to, k}; }
static bool tweensActive() { for (auto& p : tweens) if (fabsf(p.second.x - p.second.t) > 0.002f) return true; return false; }
static void stepTweens(float dt) {
    for (auto& p : tweens) {
        Tween& t = p.second;
        t.x += (t.t - t.x) * (1 - expf(-dt * t.k));
        if (fabsf(t.x - t.t) < 0.002f) t.x = t.t;
    }
}
static float hv(int id) { return tw(100000 + id, hoverId == id ? 1.f : 0.f, 22); }
static float prs(int id) { return tw(150000 + id, pressId == id ? 1.f : 0.f, 34); }
static float easeOut(float t) { t = clampf(t, 0, 1); return 1 - (1 - t) * (1 - t) * (1 - t); }
static D2D1_COLOR_F mix(D2D1_COLOR_F a, D2D1_COLOR_F b, float t) { return {a.r + (b.r - a.r) * t, a.g + (b.g - a.g) * t, a.b + (b.b - a.b) * t, a.a + (b.a - a.a) * t}; }

// ---------------------------------------------------------------- eficiencia
static void setLowMemoryPriority() {
    struct { ULONG MemoryPriority; } m{2 /*MEMORY_PRIORITY_LOW*/};
    SetProcessInformation(GetCurrentProcess(), (PROCESS_INFORMATION_CLASS)0 /*ProcessMemoryPriority*/, &m, sizeof m);
}
static void setEco(bool on) {
    struct { ULONG Version, ControlMask, StateMask; } s{1, 1, on ? 1u : 0u};
    SetProcessInformation(GetCurrentProcess(), (PROCESS_INFORMATION_CLASS)4 /*ProcessPowerThrottling*/, &s, sizeof s);
}
static void trimMemory() { SetProcessWorkingSetSize(GetCurrentProcess(), (SIZE_T)-1, (SIZE_T)-1); }

// ---------------------------------------------------------------- registro
static const wchar_t* REGKEY = L"Software\\islita";
static const wchar_t* OLD_REGKEY = L"Software\\IslaDinamica";  // nombre anterior (se migra al arrancar)
static const wchar_t* RUNKEY = L"Software\\Microsoft\\Windows\\CurrentVersion\\Run";
static DWORD regGet(const wchar_t* name, DWORD def) {
    DWORD v = def, sz = sizeof v;
    RegGetValueW(HKEY_CURRENT_USER, REGKEY, name, RRF_RT_REG_DWORD, nullptr, &v, &sz);
    return v;
}
static void regSet(const wchar_t* name, DWORD v) {
    HKEY k; if (RegCreateKeyExW(HKEY_CURRENT_USER, REGKEY, 0, nullptr, 0, KEY_SET_VALUE, nullptr, &k, nullptr) == ERROR_SUCCESS) {
        RegSetValueExW(k, name, 0, REG_DWORD, (BYTE*)&v, sizeof v); RegCloseKey(k);
    }
}
static bool autostartOn() {
    return RegGetValueW(HKEY_CURRENT_USER, RUNKEY, L"islita", RRF_RT_REG_SZ, nullptr, nullptr, nullptr) == ERROR_SUCCESS;
}
static void setAutostart(bool on) {
    HKEY k; if (RegOpenKeyExW(HKEY_CURRENT_USER, RUNKEY, 0, KEY_SET_VALUE, &k) != ERROR_SUCCESS) return;
    if (on) {
        wchar_t p[MAX_PATH]; GetModuleFileNameW(nullptr, p, MAX_PATH);
        std::wstring v = L"\"" + std::wstring(p) + L"\"";
        RegSetValueExW(k, L"islita", 0, REG_SZ, (BYTE*)v.c_str(), (DWORD)((v.size() + 1) * 2));
    } else RegDeleteValueW(k, L"islita");
    RegCloseKey(k);
}
static void migrateFromIsla(const std::wstring& appdata) {
    HKEY k;
    if (RegOpenKeyExW(HKEY_CURRENT_USER, REGKEY, 0, KEY_READ, &k) == ERROR_SUCCESS) RegCloseKey(k);
    else if (RegOpenKeyExW(HKEY_CURRENT_USER, OLD_REGKEY, 0, KEY_READ, &k) == ERROR_SUCCESS) {
        HKEY nk;
        if (RegCreateKeyExW(HKEY_CURRENT_USER, REGKEY, 0, nullptr, 0, KEY_ALL_ACCESS, nullptr, &nk, nullptr) == ERROR_SUCCESS) {
            RegCopyTreeW(k, nullptr, nk); RegCloseKey(nk);
        }
        RegCloseKey(k);
        RegDeleteTreeW(HKEY_CURRENT_USER, OLD_REGKEY);
    }
    if (RegOpenKeyExW(HKEY_CURRENT_USER, RUNKEY, 0, KEY_READ | KEY_SET_VALUE, &k) == ERROR_SUCCESS) {
        if (RegGetValueW(k, nullptr, L"Isla", RRF_RT_REG_SZ, nullptr, nullptr, nullptr) == ERROR_SUCCESS) {
            RegDeleteValueW(k, L"Isla");
            RegCloseKey(k);
            setAutostart(true);  // apunta ya a islita.exe
        } else RegCloseKey(k);
    }
    std::wstring oldDir = appdata + L"\\Isla", newDir = appdata + L"\\islita";
    if (GetFileAttributesW(newDir.c_str()) == INVALID_FILE_ATTRIBUTES && GetFileAttributesW(oldDir.c_str()) != INVALID_FILE_ATTRIBUTES)
        MoveFileW(oldDir.c_str(), newDir.c_str());
}
static void loadSettings() {
    cfg.discreetOn = regGet(L"ModoDiscreto", 1); cfg.hoverOpen = regGet(L"AbrirAlPasar", 0); cfg.hideFull = regGet(L"OcultarPantallaCompleta", 1);
    cfg.eq = regGet(L"Ecualizador", 1); cfg.battery = regGet(L"Bateria", 1); cfg.alerts = regGet(L"Avisos", 1);
    cfg.alertMins = (int)regGet(L"AvisoMin", 60); cfg.size = (int)std::min<DWORD>(regGet(L"Tamano", 1), 2);
    cfg.accent = (int)std::min<DWORD>(regGet(L"Acento", 0), 5); cfg.autostart = autostartOn();
    cfg.opacity = (int)std::min<DWORD>(regGet(L"Opacidad", 1), 2);
    cfg.transMode = (int)std::min<DWORD>(regGet(L"TransparenteCuando", 0), 2);
}
static void saveSettings() {
    regSet(L"ModoDiscreto", cfg.discreetOn); regSet(L"AbrirAlPasar", cfg.hoverOpen); regSet(L"OcultarPantallaCompleta", cfg.hideFull); regSet(L"Ecualizador", cfg.eq);
    regSet(L"Bateria", cfg.battery); regSet(L"Avisos", cfg.alerts); regSet(L"AvisoMin", cfg.alertMins);
    regSet(L"Tamano", cfg.size); regSet(L"Acento", cfg.accent); regSet(L"Opacidad", cfg.opacity); regSet(L"TransparenteCuando", cfg.transMode);
}

// ---------------------------------------------------------------- atajos (atajos.txt)
static std::wstring expandEnv(const std::wstring& s) {
    wchar_t b[2048]; DWORD n = ExpandEnvironmentStringsW(s.c_str(), b, 2048);
    return (n && n < 2048) ? std::wstring(b) : s;
}
static std::wstring trim(const std::wstring& s) {
    size_t a = s.find_first_not_of(L" \t\r\n"), b = s.find_last_not_of(L" \t\r\n");
    return a == std::wstring::npos ? L"" : s.substr(a, b - a + 1);
}
static void writeDefaultApps() {
    std::string t =
        "# Atajos de la isla: hasta 6 líneas con el formato\n"
        "#   Nombre | programa, carpeta o enlace | icono (opcional) | argumentos (opcional)\n"
        "# Se admiten variables como %LOCALAPPDATA%. Guarda y vuelve a abrir la isla.\n";
    struct D { const char* line; const wchar_t* check; };
    D d[] = {
        {"Explorador | C:\\Windows\\explorer.exe", L"C:\\Windows\\explorer.exe"},
        {"Chrome | C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe", L"C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe"},
        {"VS Code | %LOCALAPPDATA%\\Programs\\Microsoft VS Code\\Code.exe", L"%LOCALAPPDATA%\\Programs\\Microsoft VS Code\\Code.exe"},
        {"Spotify | %APPDATA%\\Spotify\\Spotify.exe", L"%APPDATA%\\Spotify\\Spotify.exe"},
        {"Tareas | C:\\Windows\\System32\\Taskmgr.exe", L"C:\\Windows\\System32\\Taskmgr.exe"},
        {"Ajustes | ms-settings: | C:\\Windows\\ImmersiveControlPanel\\SystemSettings.exe", nullptr},
        {"Calculadora | calc.exe | C:\\Windows\\System32\\calc.exe", nullptr},
    };
    int n = 0;
    for (auto& x : d) {
        if (n >= 6) break;
        if (x.check && GetFileAttributesW(expandEnv(x.check).c_str()) == INVALID_FILE_ATTRIBUTES) continue;
        t += x.line; t += "\n"; n++;
    }
    HANDLE f = CreateFileW(appsFile.c_str(), GENERIC_WRITE, 0, nullptr, CREATE_NEW, 0, nullptr);
    if (f != INVALID_HANDLE_VALUE) { DWORD w; WriteFile(f, t.data(), (DWORD)t.size(), &w, nullptr); CloseHandle(f); }
}
static FILETIME fileStamp(const std::wstring& p) {
    WIN32_FILE_ATTRIBUTE_DATA a{}; GetFileAttributesExW(p.c_str(), GetFileExInfoStandard, &a); return a.ftLastWriteTime;
}
static void freeIcons() { for (auto& a : apps) SafeRelease(a.bmp); iconsLoaded = false; }
static void loadApps() {
    freeIcons(); apps.clear();
    if (GetFileAttributesW(appsFile.c_str()) == INVALID_FILE_ATTRIBUTES) writeDefaultApps();
    appsStamp = fileStamp(appsFile);
    std::string raw; if (!bg::readAll(appsFile, raw)) return;
    if (raw.size() >= 3 && (BYTE)raw[0] == 0xEF) raw = raw.substr(3);
    int n = MultiByteToWideChar(CP_UTF8, 0, raw.data(), (int)raw.size(), nullptr, 0);
    std::wstring w(n, 0); MultiByteToWideChar(CP_UTF8, 0, raw.data(), (int)raw.size(), &w[0], n);
    size_t p = 0;
    while (p < w.size() && apps.size() < 6) {
        size_t e = w.find(L'\n', p); if (e == std::wstring::npos) e = w.size();
        std::wstring line = trim(w.substr(p, e - p)); p = e + 1;
        if (line.empty() || line[0] == L'#') continue;
        std::vector<std::wstring> parts; size_t q = 0;
        while (true) { size_t bar = line.find(L'|', q); parts.push_back(trim(line.substr(q, bar == std::wstring::npos ? std::wstring::npos : bar - q))); if (bar == std::wstring::npos) break; q = bar + 1; }
        if (parts.size() < 2 || parts[1].empty()) continue;
        App a; a.name = parts[0]; a.target = expandEnv(parts[1]);
        if (parts.size() > 2) a.icon = expandEnv(parts[2]);
        if (parts.size() > 3) a.args = parts[3];
        apps.push_back(a);
    }
}

#ifndef SHIL_EXTRALARGE
#define SHIL_EXTRALARGE 2
#endif
#ifndef SHIL_JUMBO
#define SHIL_JUMBO 4
#endif
static const IID IID_IImageList_ = {0x46EB5926, 0x582E, 0x4017, {0x9F, 0xDF, 0xE8, 0x99, 0x8D, 0xAA, 0x09, 0x50}};

static HICON iconFor(const std::wstring& path, int list) {
    SHFILEINFOW fi{};
    if (!SHGetFileInfoW(path.c_str(), 0, &fi, sizeof fi, SHGFI_SYSICONINDEX)) return nullptr;
    void* il = nullptr;
    if (FAILED(SHGetImageList(list, IID_IImageList_, &il)) || !il) return nullptr;
    HICON h = ImageList_GetIcon((HIMAGELIST)il, fi.iIcon, ILD_TRANSPARENT);
    ((IUnknown*)il)->Release();
    return h;
}
static ID2D1Bitmap* bitmapFromIcon(HICON hi, UINT px, bool checkJumbo) {
    ID2D1Bitmap* out = nullptr;
    IWICBitmap* wb = nullptr;
    if (FAILED(wicUI->CreateBitmapFromHICON(hi, &wb))) return nullptr;
    UINT w, h; wb->GetSize(&w, &h);
    if (checkJumbo) {  // iconos sin versión de 256px vienen pequeños en una esquina: descartar
        std::vector<BYTE> px4(w * h * 4); wb->CopyPixels(nullptr, w * 4, (UINT)px4.size(), px4.data());
        UINT mx = 0, my = 0;
        for (UINT y = 0; y < h; y++) for (UINT x = 0; x < w; x++) if (px4[(y * w + x) * 4 + 3] > 16) { if (x > mx) mx = x; if (y > my) my = y; }
        if (mx < w / 2 && my < h / 2) { wb->Release(); return nullptr; }
    }
    IWICFormatConverter* cv = nullptr; IWICBitmapScaler* sc = nullptr;
    if (SUCCEEDED(wicUI->CreateFormatConverter(&cv)) &&
        SUCCEEDED(cv->Initialize(wb, GUID_WICPixelFormat32bppPBGRA, WICBitmapDitherTypeNone, nullptr, 0, WICBitmapPaletteTypeCustom)) &&
        SUCCEEDED(wicUI->CreateBitmapScaler(&sc)) && SUCCEEDED(sc->Initialize(cv, px, px, WICBitmapInterpolationModeFant))) {
        D2D1_BITMAP_PROPERTIES bp = D2D1::BitmapProperties(D2D1::PixelFormat(DXGI_FORMAT_B8G8R8A8_UNORM, D2D1_ALPHA_MODE_PREMULTIPLIED));
        rt->CreateBitmapFromWicBitmap(sc, &bp, &out);
    }
    SafeRelease(sc); SafeRelease(cv); wb->Release();
    return out;
}
static void loadIcons() {
    if (iconsLoaded) return;
    iconsLoaded = true;
    UINT px = (UINT)lroundf(36 * scale * 1.1f);
    for (auto& a : apps) {
        std::wstring src = a.icon.empty() ? a.target : a.icon;
        if (src.find(L'\\') == std::wstring::npos) { wchar_t full[MAX_PATH]; if (SearchPathW(nullptr, src.c_str(), nullptr, MAX_PATH, full, nullptr)) src = full; }
        if (GetFileAttributesW(src.c_str()) == INVALID_FILE_ATTRIBUTES) continue;
        HICON h = iconFor(src, SHIL_JUMBO);
        if (h) { a.bmp = bitmapFromIcon(h, px, true); DestroyIcon(h); }
        if (!a.bmp && (h = iconFor(src, SHIL_EXTRALARGE))) { a.bmp = bitmapFromIcon(h, px, false); DestroyIcon(h); }
    }
}

// ---------------------------------------------------------------- bandeja de archivos
static std::string toUtf8(const std::wstring& w) {
    int n = WideCharToMultiByte(CP_UTF8, 0, w.data(), (int)w.size(), nullptr, 0, nullptr, nullptr);
    std::string o(n, 0); if (n) WideCharToMultiByte(CP_UTF8, 0, w.data(), (int)w.size(), &o[0], n, nullptr, nullptr);
    return o;
}
static void saveShelf() { std::string o; for (auto& it : shelf) o += toUtf8(it.path) + "\n"; bg::writeAll(shelfFile, o); }
static void shelfAdd(const std::wstring& path) {
    for (auto& it : shelf) if (!_wcsicmp(it.path.c_str(), path.c_str())) return;
    if (shelf.size() >= 30) { SafeRelease(shelf.front().bmp); shelf.erase(shelf.begin()); }
    ShelfItem it; it.path = path; it.name = PathFindFileNameW(path.c_str());
    shelf.push_back(it);
}
static void shelfRemove(size_t i) { if (i < shelf.size()) { SafeRelease(shelf[i].bmp); shelf.erase(shelf.begin() + i); saveShelf(); } }
static void loadShelf() {
    std::string raw; if (!bg::readAll(shelfFile, raw)) return;
    size_t p = 0;
    while (p < raw.size()) {
        size_t e = raw.find('\n', p); if (e == std::string::npos) e = raw.size();
        std::string l = raw.substr(p, e - p); p = e + 1;
        if (l.empty()) continue;
        int n = MultiByteToWideChar(CP_UTF8, 0, l.data(), (int)l.size(), nullptr, 0);
        std::wstring w(n, 0); MultiByteToWideChar(CP_UTF8, 0, l.data(), (int)l.size(), &w[0], n);
        if (GetFileAttributesW(w.c_str()) != INVALID_FILE_ATTRIBUTES) shelfAdd(w);
    }
}
// miniatura del explorador (fotos y PDF con vista previa; el resto, su icono)
static ID2D1Bitmap* thumbFor(const std::wstring& path, UINT px) {
    IShellItemImageFactory* f = nullptr;
    if (FAILED(SHCreateItemFromParsingName(path.c_str(), nullptr, IID_PPV_ARGS(&f)))) return nullptr;
    HBITMAP hb = nullptr; SIZE sz{(LONG)px, (LONG)px};
    f->GetImage(sz, SIIGBF_BIGGERSIZEOK, &hb); f->Release();
    if (!hb) return nullptr;
    // las fotos suelen venir con alfa a 0: en ese caso ignorar el alfa
    bool hasAlpha = false; DIBSECTION ds{};
    if (GetObjectW(hb, sizeof ds, &ds) && ds.dsBm.bmBits && ds.dsBm.bmBitsPixel == 32) {
        const BYTE* b = (const BYTE*)ds.dsBm.bmBits; size_t n = (size_t)ds.dsBm.bmWidth * ds.dsBm.bmHeight;
        for (size_t i = 0; i < n && !hasAlpha; i++) if (b[i * 4 + 3]) hasAlpha = true;
    }
    ID2D1Bitmap* out = nullptr; IWICBitmap* wb = nullptr;
    if (SUCCEEDED(wicUI->CreateBitmapFromHBITMAP(hb, nullptr, hasAlpha ? WICBitmapUsePremultipliedAlpha : WICBitmapIgnoreAlpha, &wb))) {
        UINT w, h; wb->GetSize(&w, &h);
        float k = (float)px / (float)std::max(w, h);
        UINT tw_ = std::max(1u, (UINT)lroundf(w * k)), th = std::max(1u, (UINT)lroundf(h * k));
        IWICBitmapScaler* sc = nullptr; IWICFormatConverter* cv = nullptr;
        if (SUCCEEDED(wicUI->CreateFormatConverter(&cv)) &&
            SUCCEEDED(cv->Initialize(wb, GUID_WICPixelFormat32bppPBGRA, WICBitmapDitherTypeNone, nullptr, 0, WICBitmapPaletteTypeCustom)) &&
            SUCCEEDED(wicUI->CreateBitmapScaler(&sc)) && SUCCEEDED(sc->Initialize(cv, tw_, th, WICBitmapInterpolationModeFant))) {
            D2D1_BITMAP_PROPERTIES bp = D2D1::BitmapProperties(D2D1::PixelFormat(DXGI_FORMAT_B8G8R8A8_UNORM, D2D1_ALPHA_MODE_PREMULTIPLIED));
            rt->CreateBitmapFromWicBitmap(sc, &bp, &out);
        }
        SafeRelease(sc); SafeRelease(cv); wb->Release();
    }
    DeleteObject(hb);
    return out;
}

// ---------------------------------------------------------------- volumen (Core Audio, solo con la pestaña abierta)
static void volInit() {
    if (vol) return;
    IMMDeviceEnumerator* en = nullptr;
    if (FAILED(CoCreateInstance(__uuidof(MMDeviceEnumerator), nullptr, CLSCTX_ALL, __uuidof(IMMDeviceEnumerator), (void**)&en))) return;
    IMMDevice* d = nullptr;
    if (SUCCEEDED(en->GetDefaultAudioEndpoint(eRender, eConsole, &d))) { d->Activate(__uuidof(IAudioEndpointVolume), CLSCTX_ALL, nullptr, (void**)&vol); d->Release(); }
    en->Release();
}
static float volGet(bool* mute) {
    float v = 0; BOOL m = FALSE;
    if (vol) { vol->GetMasterVolumeLevelScalar(&v); vol->GetMute(&m); }
    if (mute) *mute = m;
    return v;
}

// ---------------------------------------------------------------- brillo (WMI en un hilo propio, solo con la pestaña abierta)
static std::atomic<int> briCur{-1}, briWant{-1};
static std::atomic<bool> briQuit{false}, briAvail{true};
static HANDLE briEvt = nullptr; static std::thread briThread; static bool briRunning = false;
static void briLoop() {
    CoInitializeEx(nullptr, COINIT_MULTITHREADED);
    IWbemLocator* loc = nullptr; IWbemServices* svc = nullptr;
    BSTR ns = SysAllocString(L"ROOT\\WMI");
    if (SUCCEEDED(CoCreateInstance(CLSID_WbemLocator, nullptr, CLSCTX_INPROC_SERVER, IID_IWbemLocator, (void**)&loc)) &&
        SUCCEEDED(loc->ConnectServer(ns, nullptr, nullptr, nullptr, 0, nullptr, nullptr, &svc)))
        CoSetProxyBlanket(svc, RPC_C_AUTHN_WINNT, RPC_C_AUTHZ_NONE, nullptr, RPC_C_AUTHN_LEVEL_CALL, RPC_C_IMP_LEVEL_IMPERSONATE, nullptr, EOAC_NONE);
    SysFreeString(ns);
    BSTR wql = SysAllocString(L"WQL");
    auto query = [&](const wchar_t* q) -> IWbemClassObject* {
        if (!svc) return nullptr;
        IEnumWbemClassObject* en = nullptr; IWbemClassObject* o = nullptr; ULONG n = 0;
        BSTR bq = SysAllocString(q);
        if (SUCCEEDED(svc->ExecQuery(wql, bq, WBEM_FLAG_FORWARD_ONLY | WBEM_FLAG_RETURN_IMMEDIATELY, nullptr, &en)) && en) { en->Next(2000, 1, &o, &n); en->Release(); }
        SysFreeString(bq);
        return n ? o : nullptr;
    };
    auto read = [&]() {
        IWbemClassObject* o = query(L"SELECT CurrentBrightness FROM WmiMonitorBrightness WHERE Active=TRUE");
        if (!o) { briAvail = false; PostMessage(gHwnd, WM_APP_STATS, 0, 0); return; }
        VARIANT v; VariantInit(&v);
        if (SUCCEEDED(o->Get(L"CurrentBrightness", 0, &v, nullptr, nullptr))) {
            int b = v.vt == VT_UI1 ? v.bVal : (v.vt == VT_I4 ? (int)v.lVal : -1);
            if (b >= 0 && b != briCur) { briCur = b; PostMessage(gHwnd, WM_APP_STATS, 0, 0); }
        }
        VariantClear(&v); o->Release();
    };
    auto write = [&](int b) {
        IWbemClassObject* inst = query(L"SELECT * FROM WmiMonitorBrightnessMethods WHERE Active=TRUE");
        if (!inst) return;
        VARIANT path; VariantInit(&path);
        IWbemClassObject *cls = nullptr, *inDef = nullptr, *in = nullptr;
        BSTR cn = SysAllocString(L"WmiMonitorBrightnessMethods"), mn = SysAllocString(L"WmiSetBrightness");
        if (SUCCEEDED(inst->Get(L"__PATH", 0, &path, nullptr, nullptr)) && SUCCEEDED(svc->GetObject(cn, 0, nullptr, &cls, nullptr)) &&
            SUCCEEDED(cls->GetMethod(mn, 0, &inDef, nullptr)) && SUCCEEDED(inDef->SpawnInstance(0, &in))) {
            VARIANT t; VariantInit(&t); t.vt = VT_I4; t.lVal = 0; in->Put(L"Timeout", 0, &t, 0);
            VARIANT bv; VariantInit(&bv); bv.vt = VT_UI1; bv.bVal = (BYTE)b; in->Put(L"Brightness", 0, &bv, 0);
            svc->ExecMethod(path.bstrVal, mn, 0, nullptr, in, nullptr, nullptr);
        }
        SysFreeString(cn); SysFreeString(mn); VariantClear(&path);
        if (in) in->Release();
        if (inDef) inDef->Release();
        if (cls) cls->Release();
        inst->Release();
    };
    read();
    while (!briQuit) {
        DWORD r = WaitForSingleObject(briEvt, 2000);
        if (briQuit) break;
        int w = briWant.exchange(-1);
        if (w >= 0) write(w);              // solo el último valor pedido (al arrastrar llegan muchos)
        else if (r == WAIT_TIMEOUT) read();  // por si se cambia con las teclas del portátil
    }
    SysFreeString(wql);
    if (svc) svc->Release();
    if (loc) loc->Release();
    CoUninitialize();
}
static void briStart() {
    if (briRunning) return;
    briRunning = true; briQuit = false; briAvail = true;  // vuelve a probar (p. ej. al cambiar de pantalla)
    if (!briEvt) briEvt = CreateEventW(nullptr, FALSE, FALSE, nullptr);
    briThread = std::thread(briLoop);
}
static void briStop() { if (!briRunning) return; briQuit = true; SetEvent(briEvt); briThread.join(); briRunning = false; }
static void briSet(int b) { b = std::clamp(b, 0, 100); briCur = b; briWant = b; SetEvent(briEvt); }

// ---------------------------------------------------------------- Claude Code
static void launchClaude() {
    wchar_t home[MAX_PATH]; GetEnvironmentVariableW(L"USERPROFILE", home, MAX_PATH);
    std::wstring args = L"-d \"" + std::wstring(home) + L"\" cmd /k claude";
    if ((INT_PTR)ShellExecuteW(nullptr, L"open", L"wt.exe", args.c_str(), nullptr, SW_SHOWNORMAL) <= 32)
        ShellExecuteW(nullptr, L"open", L"cmd.exe", L"/k claude", home, SW_SHOWNORMAL);
}

// ---------------------------------------------------------------- temporizador y cronómetro
static ULONGLONG nowMs() { return GetTickCount64(); }
static ULONGLONG tmRemaining() { if (tmState == 1) { ULONGLONG n = nowMs(); return tmEnd > n ? tmEnd - n : 0; } return tmLeft; }
static void tmStart() { if (tmState == 1) return; ULONGLONG left = tmState == 2 ? tmLeft : tmDur; tmEnd = nowMs() + left; tmState = 1; }
static void tmPause() { if (tmState != 1) return; tmLeft = tmRemaining(); tmState = 2; }
static void tmReset() { tmState = 0; tmLeft = tmDur; }
static void tmSet(ULONGLONG ms) { tmDur = tmLeft = ms; tmEnd = nowMs() + ms; tmState = 1; }
static void tmAdd(ULONGLONG ms) {
    if (tmState == 1) tmEnd += ms; else if (tmState == 2) tmLeft += ms; else tmLeft += ms;
    tmDur += ms;
}
static const int PICK_N[3] = {24, 60, 60};
static ULONGLONG pickMs() { return ((ULONGLONG)pick[0] * 3600 + pick[1] * 60 + pick[2]) * 1000; }
static void updatePick() {
    for (int c = 0; c < 3; c++) pick[c] = (((int)lroundf(pickT[c]) % PICK_N[c]) + PICK_N[c]) % PICK_N[c];
    if (!pomo && tmState == 0) tmDur = tmLeft = pickMs();
}
static void pomoArm(int phase) {
    pomoPhase = phase;
    int mins = phase == 0 ? 25 : (pomoCount > 0 && pomoCount % 4 == 0 ? 15 : 5);  // cada 4, descanso largo
    tmDur = tmLeft = (ULONGLONG)mins * 60000;
}
static void setPomo(bool on) {
    pomo = on; tmState = 0;
    if (on) { pomoCount = 0; pomoArm(0); } else tmDur = tmLeft = pickMs();
}
static ULONGLONG swElapsed() { return swAcc + (swRun ? nowMs() - swStart : 0); }
static std::wstring fmtClock(ULONGLONG ms, bool roundUp) {
    ULONGLONG s = roundUp ? (ms + 999) / 1000 : ms / 1000;
    wchar_t b[24];
    if (s >= 3600) swprintf(b, 24, L"%llu:%02llu:%02llu", s / 3600, (s / 60) % 60, s % 60);
    else swprintf(b, 24, L"%02llu:%02llu", s / 60, s % 60);
    return b;
}
static std::wstring fmtSW(ULONGLONG ms) {
    wchar_t b[24]; ULONGLONG s = ms / 1000;
    if (s >= 3600) swprintf(b, 24, L"%llu:%02llu:%02llu", s / 3600, (s / 60) % 60, s % 60);
    else swprintf(b, 24, L"%02llu:%02llu,%llu", s / 60, s % 60, (ms / 100) % 10);
    return b;
}

// ---------------------------------------------------------------- recursos de dibujo
static IDWriteTextFormat* mkFont(const wchar_t* fam, float size, DWRITE_FONT_WEIGHT w) {
    IDWriteTextFormat* f = nullptr;
    dw->CreateTextFormat(fam, nullptr, w, DWRITE_FONT_STYLE_NORMAL, DWRITE_FONT_STRETCH_NORMAL, size, L"es-es", &f);
    if (!f) return nullptr;
    f->SetWordWrapping(DWRITE_WORD_WRAPPING_NO_WRAP);
    f->SetParagraphAlignment(DWRITE_PARAGRAPH_ALIGNMENT_CENTER);
    DWRITE_TRIMMING tr{DWRITE_TRIMMING_GRANULARITY_CHARACTER, 0, 0};
    IDWriteInlineObject* ell = nullptr; dw->CreateEllipsisTrimmingSign(f, &ell);
    f->SetTrimming(&tr, ell); SafeRelease(ell);
    return f;
}
static void createResources() {
    D2D1CreateFactory(D2D1_FACTORY_TYPE_SINGLE_THREADED, __uuidof(ID2D1Factory), nullptr, (void**)&d2d);
    DWriteCreateFactory(DWRITE_FACTORY_TYPE_SHARED, __uuidof(IDWriteFactory), (IUnknown**)&dw);
    CoCreateInstance(CLSID_WICImagingFactory, nullptr, CLSCTX_INPROC_SERVER, IID_PPV_ARGS(&wicUI));
    const wchar_t* D = L"Segoe UI Variable Display"; const wchar_t* T = L"Segoe UI Variable Text"; const wchar_t* I = L"Segoe Fluent Icons";
    fTime = mkFont(D, 14.5f, DWRITE_FONT_WEIGHT_SEMI_BOLD);
    fSmall = mkFont(T, 12.5f, DWRITE_FONT_WEIGHT_NORMAL);
    fTitle = mkFont(D, 15.5f, DWRITE_FONT_WEIGHT_SEMI_BOLD);
    fBody = mkFont(T, 13, DWRITE_FONT_WEIGHT_NORMAL);
    fCalHead = mkFont(T, 11.5f, DWRITE_FONT_WEIGHT_BOLD);
    fCal = mkFont(T, 11.5f, DWRITE_FONT_WEIGHT_NORMAL);
    fCalB = mkFont(T, 11.5f, DWRITE_FONT_WEIGHT_SEMI_BOLD);
    fRing = mkFont(D, 15, DWRITE_FONT_WEIGHT_SEMI_BOLD);
    fTiny = mkFont(T, 10, DWRITE_FONT_WEIGHT_NORMAL);
    fApp = mkFont(T, 10, DWRITE_FONT_WEIGHT_NORMAL);
    fTab = mkFont(T, 12, DWRITE_FONT_WEIGHT_SEMI_BOLD);
    fBig = mkFont(D, 32, DWRITE_FONT_WEIGHT_SEMI_BOLD);
    fMid = mkFont(D, 20, DWRITE_FONT_WEIGHT_SEMI_BOLD);
    fGlyph = mkFont(I, 30, DWRITE_FONT_WEIGHT_NORMAL);
    fIcon = mkFont(I, 14, DWRITE_FONT_WEIGHT_NORMAL);
    fIconL = mkFont(I, 17, DWRITE_FONT_WEIGHT_NORMAL);
    D2D1_STROKE_STYLE_PROPERTIES sp = D2D1::StrokeStyleProperties(D2D1_CAP_STYLE_ROUND, D2D1_CAP_STYLE_ROUND, D2D1_CAP_STYLE_ROUND, D2D1_LINE_JOIN_ROUND);
    d2d->CreateStrokeStyle(&sp, nullptr, 0, &roundStroke);
    D2D1_STROKE_STYLE_PROPERTIES dp = D2D1::StrokeStyleProperties(D2D1_CAP_STYLE_ROUND, D2D1_CAP_STYLE_ROUND, D2D1_CAP_STYLE_ROUND, D2D1_LINE_JOIN_ROUND, 10, D2D1_DASH_STYLE_DASH, 0);
    d2d->CreateStrokeStyle(&dp, nullptr, 0, &dashStroke);
    dw->CreateTypography(&tnum);
    DWRITE_FONT_FEATURE ff{DWRITE_FONT_FEATURE_TAG_TABULAR_FIGURES, 1};
    if (tnum) tnum->AddFontFeature(ff);
}
static void createTarget() {
    SafeRelease(cacheRT); cacheValid = false;
    for (auto& it : shelf) { SafeRelease(it.bmp); it.tried = false; }
    SafeRelease(br); SafeRelease(dcrt); rt = nullptr; SafeRelease(artBmp); SafeRelease(artSBmp); artVerUI = ~0u; freeIcons();
    D2D1_RENDER_TARGET_PROPERTIES p = D2D1::RenderTargetProperties(D2D1_RENDER_TARGET_TYPE_SOFTWARE,
        D2D1::PixelFormat(DXGI_FORMAT_B8G8R8A8_UNORM, D2D1_ALPHA_MODE_PREMULTIPLIED), 0, 0);
    d2d->CreateDCRenderTarget(&p, &dcrt); rt = dcrt;
    rt->SetDpi(96 * scale, 96 * scale);
    rt->SetTextAntialiasMode(D2D1_TEXT_ANTIALIAS_MODE_GRAYSCALE);
    D2D1_COLOR_F c{1, 1, 1, 1}; rt->CreateSolidColorBrush(&c, nullptr, &br);
}
static void ensureDib() {
    int w = (int)ceilf((EW * 1.12f + 2 * M) * scale), h = (int)ceilf((EH * 1.15f + 2 * M) * scale);
    if (w <= dibW && h <= dibH && dib) return;
    if (dib) { SelectObject(memDC, oldBmp); DeleteObject(dib); }
    if (!memDC) memDC = CreateCompatibleDC(nullptr);
    BITMAPINFO bi{}; bi.bmiHeader = {sizeof(BITMAPINFOHEADER), w, -h, 1, 32, BI_RGB};
    void* bits; dib = CreateDIBSection(memDC, &bi, DIB_RGB_COLORS, &bits, nullptr, 0);
    oldBmp = (HBITMAP)SelectObject(memDC, dib);
    dibW = w; dibH = h;
}
static void updateMonitor() {
    HMONITOR hm = MonitorFromPoint(POINT{0, 0}, MONITOR_DEFAULTTOPRIMARY);
    MONITORINFO mi{sizeof mi}; GetMonitorInfoW(hm, &mi); mon = mi.rcMonitor;
    UINT dx = 96, dy = 96; GetDpiForMonitor(hm, MDT_EFFECTIVE_DPI, &dx, &dy);
    float s = dx / 96.f * SIZES[cfg.size];
    if (s != scale || !rt) {
        dpi = dx; scale = s;
        if (!rt) createTarget(); else { rt->SetDpi(96 * scale, 96 * scale); freeIcons(); SafeRelease(cacheRT); cacheValid = false; for (auto& it : shelf) { SafeRelease(it.bmp); it.tried = false; } }
        ensureDib();
        if (expanded) loadIcons();
    }
}

// ---------------------------------------------------------------- primitivas
static float gA = 1;  // opacidad global del contenido que se está pintando
static void col(float r, float g, float b, float a = 1) { D2D1_COLOR_F c{r, g, b, a * gA}; br->SetColor(&c); }
static void colC(D2D1_COLOR_F c, float a = 1) { c.a = a * gA; br->SetColor(&c); }
static void fillRR(float x, float y, float w, float h, float r) { D2D1_ROUNDED_RECT rr{{x, y, x + w, y + h}, r, r}; rt->FillRoundedRectangle(&rr, br); }
static void circle(float cx, float cy, float r) { D2D1_ELLIPSE e{{cx, cy}, r, r}; rt->FillEllipse(&e, br); }
static void text(const std::wstring& s, IDWriteTextFormat* f, float x, float y, float w, float h, DWRITE_TEXT_ALIGNMENT al = DWRITE_TEXT_ALIGNMENT_LEADING) {
    if (!f || s.empty()) return;
    f->SetTextAlignment(al);
    D2D1_RECT_F r{x, y, x + w, y + h};
    rt->DrawText(s.c_str(), (UINT32)s.size(), f, &r, br, D2D1_DRAW_TEXT_OPTIONS_CLIP, DWRITE_MEASURING_MODE_NATURAL);
}
// números con cifras de ancho fijo (para que los contadores no "bailen")
static void textN(const std::wstring& s, IDWriteTextFormat* f, float x, float y, float w, float h, DWRITE_TEXT_ALIGNMENT al = DWRITE_TEXT_ALIGNMENT_LEADING) {
    if (!f || s.empty()) return;
    f->SetTextAlignment(al);
    IDWriteTextLayout* l = nullptr;
    if (FAILED(dw->CreateTextLayout(s.c_str(), (UINT32)s.size(), f, w, h, &l))) return;
    if (tnum) { DWRITE_TEXT_RANGE r{0, (UINT32)s.size()}; l->SetTypography(tnum, r); }
    rt->DrawTextLayout(D2D1::Point2F(x, y), l, br, D2D1_DRAW_TEXT_OPTIONS_CLIP);
    l->Release();
}
static void glyph(const wchar_t* g, IDWriteTextFormat* f, float cx, float cy, float box = 30) { text(g, f, cx - box / 2, cy - box / 2, box, box, DWRITE_TEXT_ALIGNMENT_CENTER); }
static void line(float x0, float y0, float x1, float y1, float w) { rt->DrawLine(D2D1::Point2F(x0, y0), D2D1::Point2F(x1, y1), br, w, roundStroke); }
static void poly(const D2D1_POINT_2F* p, int n, float round) {
    ID2D1PathGeometry* g = nullptr; ID2D1GeometrySink* s = nullptr;
    d2d->CreatePathGeometry(&g); g->Open(&s);
    s->BeginFigure(p[0], D2D1_FIGURE_BEGIN_FILLED);
    for (int i = 1; i < n; i++) s->AddLine(p[i]);
    s->EndFigure(D2D1_FIGURE_END_CLOSED); s->Close(); s->Release();
    rt->FillGeometry(g, br, nullptr);
    if (round > 0) rt->DrawGeometry(g, br, round, roundStroke);  // esquinas suaves
    g->Release();
}
static void triangle(float x, float cy, float w, float h, bool right) {
    D2D1_POINT_2F p[3];
    if (right) { p[0] = {x, cy - h / 2}; p[1] = {x + w, cy}; p[2] = {x, cy + h / 2}; }
    else { p[0] = {x + w, cy - h / 2}; p[1] = {x, cy}; p[2] = {x + w, cy + h / 2}; }
    poly(p, 3, 2.2f);
}
static void playIcon(float cx, float cy, float s, bool playing) {
    if (playing) { fillRR(cx - s * 0.36f, cy - s / 2, s * 0.27f, s, s * 0.09f); fillRR(cx + s * 0.09f, cy - s / 2, s * 0.27f, s, s * 0.09f); }
    else triangle(cx - s * 0.32f, cy, s * 0.82f, s * 0.95f, true);
}
static void drawBitmapRounded(ID2D1Bitmap* b, float x, float y, float s, float r, float op) {
    if (!b) return;
    ID2D1BitmapBrush* bb = nullptr;
    rt->CreateBitmapBrush(b, nullptr, nullptr, &bb);
    if (!bb) return;
    D2D1_SIZE_F bs = b->GetSize();
    D2D1_MATRIX_3X2_F m{s / bs.width, 0, 0, s / bs.height, x, y};
    bb->SetTransform(&m); bb->SetOpacity(op * gA);
    bb->SetInterpolationMode(D2D1_BITMAP_INTERPOLATION_MODE_LINEAR);
    D2D1_ROUNDED_RECT rr{{x, y, x + s, y + s}, r, r};
    rt->FillRoundedRectangle(&rr, bb);
    bb->Release();
}
static void ring(float cx, float cy, float R, float frac, D2D1_COLOR_F c, float w) {
    col(1, 1, 1, 0.12f);
    D2D1_ELLIPSE e{{cx, cy}, R, R}; rt->DrawEllipse(&e, br, w, nullptr);
    frac = clampf(frac, 0, 1);
    if (frac <= 0.001f) return;
    colC(c);
    if (frac > 0.999f) { rt->DrawEllipse(&e, br, w, nullptr); return; }
    float a = (float)(-M_PI / 2 + 2 * M_PI * frac);
    ID2D1PathGeometry* g = nullptr; ID2D1GeometrySink* s = nullptr;
    d2d->CreatePathGeometry(&g); g->Open(&s);
    s->BeginFigure(D2D1::Point2F(cx, cy - R), D2D1_FIGURE_BEGIN_HOLLOW);
    D2D1_ARC_SEGMENT arc{{cx + R * cosf(a), cy + R * sinf(a)}, {R, R}, 0, D2D1_SWEEP_DIRECTION_CLOCKWISE, frac > 0.5f ? D2D1_ARC_SIZE_LARGE : D2D1_ARC_SIZE_SMALL};
    s->AddArc(&arc);
    s->EndFigure(D2D1_FIGURE_END_OPEN); s->Close(); s->Release();
    rt->DrawGeometry(g, br, w, roundStroke);
    g->Release();
}
static void addHit(float x, float y, float w, float h, int id) { if (hitsOn) hits.push_back({{x, y, x + w, y + h}, id}); }
static float textWidth(const std::wstring& s, IDWriteTextFormat* f) {
    IDWriteTextLayout* lay = nullptr; float w = 0;
    if (SUCCEEDED(dw->CreateTextLayout(s.c_str(), (UINT32)s.size(), f, 400, 20, &lay))) { DWRITE_TEXT_METRICS m; lay->GetMetrics(&m); w = m.width; lay->Release(); }
    return w;
}
static void chevron(float cx, float cy, bool right) {
    if (right) { line(cx - 2, cy - 4.5f, cx + 2.5f, cy, 1.7f); line(cx + 2.5f, cy, cx - 2, cy + 4.5f, 1.7f); }
    else { line(cx + 2, cy - 4.5f, cx - 2.5f, cy, 1.7f); line(cx - 2.5f, cy, cx + 2, cy + 4.5f, 1.7f); }
}

static const D2D1_COLOR_F RED{1.0f, 0.271f, 0.227f, 1}, GREEN{0.188f, 0.82f, 0.345f, 1}, ORANGE{1.0f, 0.624f, 0.04f, 1};
static const D2D1_COLOR_F TOMATO{1.0f, 0.39f, 0.28f, 1};
static D2D1_COLOR_F timerColor() { return !pomo ? ORANGE : (pomoPhase == 0 ? TOMATO : GREEN); }
static D2D1_MATRIX_3X2_F mmul(const D2D1_MATRIX_3X2_F& a, const D2D1_MATRIX_3X2_F& b) {  // primero a, luego b
    return {a._11 * b._11 + a._12 * b._21, a._11 * b._12 + a._12 * b._22,
            a._21 * b._11 + a._22 * b._21, a._21 * b._12 + a._22 * b._22,
            a._31 * b._11 + a._32 * b._21 + b._31, a._31 * b._12 + a._32 * b._22 + b._32};
}
static D2D1_COLOR_F tempColor(float t) { return t < 0 ? D2D1_COLOR_F{0.5f, 0.5f, 0.5f, 1} : t < 65 ? GREEN : t < 82 ? ORANGE : RED; }

static int dowOf(int y, int m, int d) {  // 0 = domingo
    static int t[] = {0, 3, 2, 5, 0, 3, 5, 1, 4, 6, 2, 4};
    if (m < 3) y -= 1;
    return (y + y / 4 - y / 100 + y / 400 + t[m - 1] + d) % 7;
}

// ---------------------------------------------------------------- controles estilo iOS
static void card(float x, float y, float w, float h) { col(1, 1, 1, 0.11f); fillRR(x, y, w, h, 22); }
static float gViewA = 1, gOpen = 1;
// aparición escalonada de las tarjetas al abrir
static void beginCard(int i, float& y) {
    float s = easeOut((gOpen - i * 0.07f) / (1 - 0.21f));
    gA = gViewA * s; y += (1 - s) * 10;
}
static void cardTitle(const wchar_t* t, float x, float y, D2D1_COLOR_F c, float a = 1) { colC(c, a); text(t, fCalHead, x + 16, y + 12, 160, 18); }
static void switchCtl(float x, float cy, bool on, int key, int id) {
    float t = tw(200000 + key, on ? 1.f : 0.f, 15), h = hv(id);
    D2D1_COLOR_F off{0.27f + 0.05f * h, 0.27f + 0.05f * h, 0.29f + 0.05f * h, 1};
    colC(mix(off, ACC(), easeOut(t))); fillRR(x, cy - 12, 42, 24, 12);
    col(0, 0, 0, 0.25f); circle(x + 12 + t * 18, cy + 0.8f, 10);
    col(1, 1, 1); circle(x + 12 + t * 18, cy, 10);
}
static void segmented(float x, float y, float w, float h, const wchar_t* const* labels, int n, int sel, int key, int baseId, float a = 1) {
    float ga = gA; gA *= a;
    col(1, 1, 1, 0.09f); fillRR(x, y, w, h, 9);
    float t = tw(300000 + key, (float)sel, 16), sw_ = (w - 4) / n;
    col(1, 1, 1, 0.2f); fillRR(x + 2 + t * sw_, y + 2, sw_, h - 4, 7);
    for (int i = 0; i < n; i++) {
        col(1, 1, 1, i == sel ? 1.f : 0.55f + 0.3f * hv(baseId + i));
        text(labels[i], fTiny, x + 2 + i * sw_, y, sw_, h, DWRITE_TEXT_ALIGNMENT_CENTER);
        addHit(x + 2 + i * sw_, y, sw_, h, baseId + i);
    }
    gA = ga;
}
static void button(float x, float y, float w, float h, const wchar_t* label, int id, D2D1_COLOR_F tc = {1, 1, 1, 1}) {
    float k = 1 - 0.04f * prs(id);
    float bw = w * k, bh = h * k, bx = x + (w - bw) / 2, by = y + (h - bh) / 2;
    col(1, 1, 1, 0.09f + 0.07f * hv(id)); fillRR(bx, by, bw, bh, 9);
    colC(tc); text(label, fSmall, bx, by, bw, bh, DWRITE_TEXT_ALIGNMENT_CENTER);
    addHit(x, y, w, h, id);
}
// botón redondo con fondo tintado (como los de Reloj en iOS)
static void roundBtn(float cx, float cy, float r, D2D1_COLOR_F tint, float bgA, int id) {
    float k = 1 - 0.08f * prs(id);
    colC(tint, bgA + 0.08f * hv(id)); circle(cx, cy, r * k);
    addHit(cx - r, cy - r, 2 * r, 2 * r, id);
}

// ---------------------------------------------------------------- píldora
enum { PM_IDLE, PM_MUSIC, PM_EVENT, PM_ALERT, PM_TIMER, PM_SW };
static const CalEvent* upcomingEvent(int* mins) {
    SYSTEMTIME st; GetLocalTime(&st);
    long t = daysFromCivil(st.wYear, st.wMonth, st.wDay); int now = st.wHour * 60 + st.wMinute;
    const CalEvent* best = nullptr;
    for (auto& e : events) {
        if (e.day < t) continue;
        if (e.day > t) break;
        if (e.start < 0) continue;
        int diff = e.start - now;
        if (diff >= -10 && diff <= cfg.alertMins && (e.end < 0 || now < e.end) && (!best || e.start < best->start)) best = &e;
    }
    if (best && mins) *mins = best->start - now;
    return best;
}
static int pillMode() {
    if (alertOn) return PM_ALERT;
    int m = 0; const CalEvent* e = cfg.alerts ? upcomingEvent(&m) : nullptr;
    if (e && m <= 15) return PM_EVENT;
    if (tmState) return PM_TIMER;
    if (swRun) return PM_SW;
    if (media.has && !media.title.empty()) return PM_MUSIC;
    if (e) return PM_EVENT;
    return PM_IDLE;
}
static std::wstring hhmm(int m) { wchar_t b[8]; swprintf(b, 8, L"%02d:%02d", m / 60, m % 60); return b; }

static void drawBattery(float x, float cy) {
    SYSTEM_POWER_STATUS ps; if (!GetSystemPowerStatus(&ps) || ps.BatteryFlag == 128 || ps.BatteryFlag == 255 || ps.BatteryLifePercent > 100) return;
    float pct = ps.BatteryLifePercent / 100.f; bool chg = ps.ACLineStatus == 1;
    col(1, 1, 1, 0.9f); textN(std::to_wstring(ps.BatteryLifePercent), fSmall, x - 34, cy - 9, 30, 18, DWRITE_TEXT_ALIGNMENT_TRAILING);
    col(1, 1, 1, 0.4f);
    D2D1_ROUNDED_RECT body{{x, cy - 5.5f, x + 22, cy + 5.5f}, 3.2f, 3.2f}; rt->DrawRoundedRectangle(&body, br, 1.1f, nullptr);
    fillRR(x + 23, cy - 2, 1.6f, 4, 0.8f);
    if (chg) colC(GREEN); else if (pct <= 0.2f) colC(RED); else col(1, 1, 1, 1);
    fillRR(x + 2, cy - 3.5f, 18 * clampf(pct, 0.06f, 1), 7, 1.6f);
}
static bool hasBattery() { SYSTEM_POWER_STATUS ps; return GetSystemPowerStatus(&ps) && ps.BatteryFlag != 128 && ps.BatteryFlag != 255 && ps.BatteryLifePercent <= 100; }

static void drawCollapsed(float px, float py, float pw, int mode) {
    SYSTEMTIME st; GetLocalTime(&st);
    std::wstring tm = hhmm(st.wHour * 60 + st.wMinute);
    float cy = py + CH / 2;
    if (mode == PM_ALERT) {
        float pulse = 0.5f + 0.5f * sinf((float)(nowMs() - alertAt) / 1000.f * 6.f);
        D2D1_COLOR_F acol = alertPomo ? timerColor() : ORANGE;
        colC(acol, 0.75f + 0.25f * pulse); circle(px + 19, cy, 11);
        col(0, 0, 0); glyph(L"\uE916", fIcon, px + 19, cy);
        col(1, 1, 1); text(alertPomo ? L"Pomodoro" : L"Temporizador", fTime, px + 38, cy - 10, 140, 20);
        colC(acol); text(alertPomo ? (pomoPhase == 1 ? L"Descanso" : L"A concentrarse") : L"¡Tiempo!", fTime, px + pw - 16 - 110, cy - 10, 110, 20, DWRITE_TEXT_ALIGNMENT_TRAILING);
    } else if (mode == PM_TIMER) {
        col(1, 1, 1); textN(tm, fTime, px + 16, cy - 10, 60, 20);
        ULONGLONG rem = tmRemaining();
        float a = tmState == 2 ? 0.5f : 1.f;
        float rx = px + pw - 16 - 8;
        float ga = gA; gA *= a;
        ring(rx, cy, 7.5f, tmDur ? (float)rem / tmDur : 0, timerColor(), 2.4f);
        colC(timerColor()); textN(fmtClock(rem, true), fTime, rx - 14 - 80, cy - 10, 80, 20, DWRITE_TEXT_ALIGNMENT_TRAILING);
        gA = ga;
    } else if (mode == PM_SW) {
        col(1, 1, 1); textN(tm, fTime, px + 16, cy - 10, 60, 20);
        colC(ORANGE); glyph(L"\uE916", fIcon, px + pw - 16 - 7, cy);
        col(1, 1, 1, 0.9f); textN(fmtClock(swElapsed(), false), fTime, px + pw - 16 - 20 - 80, cy - 10, 80, 20, DWRITE_TEXT_ALIGNMENT_TRAILING);
    } else if (mode == PM_EVENT) {
        int mins = 0; const CalEvent* e = upcomingEvent(&mins);
        if (!e) return;
        col(1, 1, 1); textN(tm, fTime, px + 16, cy - 10, 50, 20);
        colC(e->color); circle(px + 72, cy, 3.5f);
        col(1, 1, 1, 0.8f); text(e->title, fSmall, px + 82, cy - 9, pw - 82 - 78, 18);
        std::wstring when = mins <= 0 ? L"ahora" : L"en " + std::to_wstring(mins) + L" min";
        colC(e->color); text(when, fSmall, px + pw - 15 - 70, cy - 9, 70, 18, DWRITE_TEXT_ALIGNMENT_TRAILING);
    } else if (mode == PM_MUSIC) {
        float ax = px + 6;
        if (artSBmp) drawBitmapRounded(artSBmp, ax, cy - 11, 22, 6, 1);
        else { col(0.22f, 0.22f, 0.24f); fillRR(ax, cy - 11, 22, 22, 6); col(1, 1, 1, 0.7f); text(L"♪", fSmall, ax, cy - 11, 22, 22, DWRITE_TEXT_ALIGNMENT_CENTER); }
        col(1, 1, 1); textN(tm, fTime, ax + 30, cy - 10, 46, 20);
        col(1, 1, 1, 0.55f); text(media.title, fSmall, ax + 80, cy - 9, pw - 80 - 6 - 40, 18);
        float bx = px + pw - 14 - 19;
        for (int i = 0; i < 4; i++) {
            float hgt = 3.5f;
            if (media.playing) {
                double ph = eqTime * (5.1 + i * 1.7) + i * 1.3;
                hgt = 4 + 12 * (float)(0.5 + 0.5 * sin(ph) * (0.6 + 0.4 * sin(ph * 0.37 + i)));
            }
            colC(media.accent, media.playing ? 1 : 0.5f);
            fillRR(bx + i * 5.2f, cy - hgt / 2, 3, hgt, 1.5f);
        }
    } else {
        col(1, 1, 1); textN(tm, fTime, px + 16, cy - 10, 60, 20);
        if (!shelf.empty()) { col(1, 1, 1, 0.55f); glyph(L"", fIcon, px + 78, cy); textN(std::to_wstring(shelf.size()), fTiny, px + 88, cy - 8, 24, 16); }
        std::wstring d = std::wstring(DOW[st.wDayOfWeek]) + L" " + std::to_wstring(st.wDay) + L" " + MON[st.wMonth - 1];
        float right = px + pw - 15;
        if (cfg.battery && hasBattery()) { drawBattery(right - 24, cy); right -= 24 + 40; }
        float dwid = textWidth(d, fSmall);
        col(1, 1, 1, 0.55f); text(d, fSmall, right - 90, cy - 9, 90, 18, DWRITE_TEXT_ALIGNMENT_TRAILING);
        if (caffeine) { colC(ACC()); glyph(L"\uE706", fIcon, right - dwid - 14, cy); }
    }
}

// ---------------------------------------------------------------- pestaña Inicio
static void drawMusic(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    float ax = x + 16, ay = y + 16, as = 80;
    bool has = media.has && !media.title.empty();
    if (has && artBmp) drawBitmapRounded(artBmp, ax, ay, as, 16, 1);
    else {
        col(0.2f, 0.2f, 0.215f); fillRR(ax, ay, as, as, 16);
        col(1, 1, 1, 0.35f); text(L"\uE8D6", fGlyph, ax, ay, as, as, DWRITE_TEXT_ALIGNMENT_CENTER);
    }
    float tx = ax + as + 14, tw_ = x + w - 16 - tx;
    if (has) {
        col(1, 1, 1); text(media.title, fTitle, tx, ay + 14, tw_, 22);
        col(1, 1, 1, 0.55f); text(media.artist.empty() ? media.app : media.artist, fBody, tx, ay + 40, tw_, 18);
    } else {
        col(1, 1, 1, 0.9f); text(L"Nada sonando", fTitle, tx, ay + 20, tw_, 22);
        col(1, 1, 1, 0.45f); text(L"Pon música en cualquier app", fTiny, tx, ay + 44, tw_, 14);
    }
    float cx = x + w / 2, cy = y + 148;
    float op = has ? 1.f : 0.35f;
    struct B { int id; float x, r; } bs[3] = {{H_PREV, cx - 66, 22}, {H_PLAY, cx, 26}, {H_NEXT, cx + 66, 22}};
    for (auto& b : bs) {
        float hh = hv(b.id), pp = prs(b.id);
        if (hh > 0.01f || pp > 0.01f) { col(1, 1, 1, 0.1f * hh + 0.1f * pp); circle(b.x, cy, b.r * (1 - 0.06f * pp)); }
        addHit(b.x - b.r, cy - b.r, 2 * b.r, 2 * b.r, b.id);
    }
    col(1, 1, 1, op);
    float k = 1 - 0.14f * prs(H_PLAY);
    playIcon(cx, cy, 22 * k, media.playing);
    float kp = 1 - 0.14f * prs(H_PREV), kn = 1 - 0.14f * prs(H_NEXT);
    triangle(cx - 66 - 12 * kp, cy, 11 * kp, 14 * kp, false); triangle(cx - 66 - 1 * kp, cy, 11 * kp, 14 * kp, false);
    triangle(cx + 66 - 10 * kn, cy, 11 * kn, 14 * kn, true); triangle(cx + 66 + 1 * kn, cy, 11 * kn, 14 * kn, true);
    if (has) {
        col(1, 1, 1, 0.3f);
        text(media.playing ? L"Reproduciendo en " + media.app : L"En pausa", fTiny, x + 12, y + h - 26, w - 24, 14, DWRITE_TEXT_ALIGNMENT_CENTER);
    }
}

static void drawAgenda(float x, float y, float w, float h) {
    static const wchar_t* DOWL[] = {L"Domingo", L"Lunes", L"Martes", L"Miércoles", L"Jueves", L"Viernes", L"Sábado"};
    long day = daysFromCivil(calY, calM, selDay);
    float ay = y + 21;
    col(1, 1, 1, 0.1f * hv(H_CBACK)); circle(x + 22, ay, 11);
    col(1, 1, 1, 0.7f); chevron(x + 22, ay, false);
    addHit(x + 10, ay - 12, 26, 24, H_CBACK);
    std::wstring dn = DOWL[dowOf(calY, calM, selDay)], rest = std::to_wstring(selDay) + L" " + MON[calM - 1];
    float dnw = textWidth(dn, fCalHead);
    colC(ACC()); text(dn, fCalHead, x + 38, y + 12, 120, 18);
    col(1, 1, 1, 0.45f); text(rest, fCalHead, x + 38 + dnw + 5, y + 12, 70, 18);
    addHit(x + 36, y + 8, w - 46, 26, H_COPEN);
    std::vector<const CalEvent*> list;
    for (auto& e : events) if (e.day == day) list.push_back(&e);
    if (list.empty()) { col(1, 1, 1, 0.4f); text(L"Sin eventos", fBody, x, y + h / 2 - 9, w, 18, DWRITE_TEXT_ALIGNMENT_CENTER); return; }
    size_t maxRows = 4, show = list.size() > maxRows ? maxRows - 1 : list.size();
    float ry = y + 40;
    for (size_t i = 0; i < show; i++, ry += 40) {
        const CalEvent& e = *list[i];
        int id = H_EVT + (int)i;
        col(1, 1, 1, 0.07f * hv(id)); fillRR(x + 8, ry, w - 16, 38, 10);
        colC(e.color); fillRR(x + 14, ry + 5, 3.5f, 28, 1.75f);
        col(1, 1, 1); text(e.title, fBody, x + 25, ry + 3, w - 38, 17);
        std::wstring sub = e.start < 0 ? L"Todo el día" : hhmm(e.start) + (e.end >= 0 ? L" - " + hhmm(e.end) : L"");
        if (!e.loc.empty()) sub += L"   " + e.loc;
        col(1, 1, 1, 0.5f); text(sub, fTiny, x + 25, ry + 21, w - 38, 14);
        addHit(x + 8, ry, w - 16, 38, id);
    }
    if (show < list.size()) {
        int id = H_EVT + 99;
        col(1, 1, 1, 0.45f + 0.35f * hv(id));
        text(L"y " + std::to_wstring(list.size() - show) + L" más", fTiny, x + 25, ry + 4, w - 38, 16);
        addHit(x + 8, ry, w - 16, 24, id);
    }
}

static void drawCalendar(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    // la agenda entra deslizándose sobre el mes
    float t = easeOut(tw(8, selDay ? 1.f : 0.f, 14));
    float ga = gA;
    D2D1_RECT_F clip{x, y, x + w, y + h};
    rt->PushAxisAlignedClip(&clip, D2D1_ANTIALIAS_MODE_PER_PRIMITIVE);
    bool hs = hitsOn;
    if (t < 0.999f) {
        gA = ga * (1 - t); hitsOn = hs && !selDay;
        float ox = -t * 30;
        SYSTEMTIME st; GetLocalTime(&st);
        float mx = x + ox;
        colC(ACC()); text(MONL[calM - 1], fCalHead, mx + 16, y + 12, 120, 18);
        float mw = textWidth(MONL[calM - 1], fCalHead);
        col(1, 1, 1, 0.45f); text(std::to_wstring(calY), fCalHead, mx + 16 + mw + 5, y + 12, 50, 18);
        addHit(mx + 10, y + 8, mw + 60, 26, H_CTITLE);
        float ay = y + 21;
        for (int i = 0; i < 2; i++) {
            float cx = mx + w - 44 + i * 24; int id = i ? H_CNEXT : H_CPREV;
            col(1, 1, 1, 0.1f * hv(id) + 0.1f * prs(id)); circle(cx, ay, 11);
            col(1, 1, 1, 0.7f); chevron(cx, ay, i == 1);
            addHit(cx - 11, ay - 11, 22, 22, id);
        }
        const wchar_t* L7[] = {L"L", L"M", L"X", L"J", L"V", L"S", L"D"};
        float gx = mx + 10, cw = (w - 20) / 7.f;
        for (int i = 0; i < 7; i++) { col(1, 1, 1, i >= 5 ? 0.3f : 0.45f); text(L7[i], fTiny, gx + i * cw, y + 38, cw, 14, DWRITE_TEXT_ALIGNMENT_CENTER); }
        int first = (dowOf(calY, calM, 1) + 6) % 7;
        int nd = dim(calY, calM);
        long m0 = daysFromCivil(calY, calM, 1);
        D2D1_COLOR_F dots[32][3]; int nDots[32] = {};
        for (auto& e : events) {
            if (e.day < m0) continue;
            if (e.day >= m0 + nd) break;
            int d = (int)(e.day - m0) + 1;
            if (nDots[d] < 3) dots[d][nDots[d]++] = e.color;
        }
        float rh = 24, gy = y + 56;
        for (int d = 1; d <= nd; d++) {
            int cell = first + d - 1, c = cell % 7, r = cell / 7;
            float cx = gx + c * cw + cw / 2, cyy = gy + r * rh + rh / 2;
            bool today = calY == st.wYear && calM == st.wMonth && d == st.wDay;
            int id = H_DAY + d;
            if (today) { colC(ACC()); circle(cx, cyy, 10.5f); }
            else { float hh = hv(id); if (hh > 0.01f) { col(1, 1, 1, 0.12f * hh); circle(cx, cyy, 10.5f); } }
            if (today) col(1, 1, 1); else col(1, 1, 1, c >= 5 ? 0.5f : 0.9f);
            float ty = nDots[d] ? cyy - 10.5f : cyy - 9;
            text(std::to_wstring(d), today ? fCalB : fCal, cx - 12, ty, 24, 18, DWRITE_TEXT_ALIGNMENT_CENTER);
            for (int i = 0; i < nDots[d]; i++) {
                if (today) col(1, 1, 1, 0.9f); else colC(dots[d][i]);
                circle(cx + (i - (nDots[d] - 1) / 2.f) * 4.5f, cyy + 6.5f, 1.6f);
            }
            addHit(cx - cw / 2, cyy - rh / 2, cw, rh, id);
        }
    }
    if (t > 0.001f && selDay) {
        gA = ga * t; hitsOn = hs;
        drawAgenda(x + (1 - t) * 30, y, w, h);
    }
    hitsOn = hs; gA = ga;
    rt->PopAxisAlignedClip();
}

static void drawStats(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    auto one = [&](float cy, float t, float use, const wchar_t* lbl, int key) {
        float cx = x + w / 2;
        float ft = t < 0 ? 0 : t / 100.f; (void)key;
        ring(cx, cy, 27, ft, tempColor(t), 5.5f);
        wchar_t b[16];
        if (t < 0) wcscpy(b, L"--"); else swprintf(b, 16, L"%d°", (int)lroundf(t));
        col(1, 1, 1); textN(b, fRing, cx - 26, cy - 13, 52, 20, DWRITE_TEXT_ALIGNMENT_CENTER);
        if (use >= 0) { swprintf(b, 16, L"%d%%", (int)lroundf(use)); col(1, 1, 1, 0.45f); textN(b, fTiny, cx - 26, cy + 5, 52, 12, DWRITE_TEXT_ALIGNMENT_CENTER); }
        col(1, 1, 1, 0.55f); text(lbl, fTiny, x, cy + 31, w, 14, DWRITE_TEXT_ALIGNMENT_CENTER);
    };
    one(y + 46, stats.cpuT, stats.cpuU, L"CPU", 20);
    one(y + 126, stats.gpuT, stats.gpuU, L"GPU", 21);
    if (stats.ram >= 0) {
        wchar_t b[24]; swprintf(b, 24, L"RAM %d%%", (int)lroundf(stats.ram));
        col(1, 1, 1, 0.4f); textN(b, fTiny, x, y + h - 22, w, 14, DWRITE_TEXT_ALIGNMENT_CENTER);
    }
}

static void drawApps(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    float is = 36, gap = 12, colW = is + gap;
    float x0 = x + (w - (2 * is + gap)) / 2;
    for (size_t i = 0; i < apps.size(); i++) {
        int c = (int)i % 2, r = (int)i / 2;
        float ix = x0 + c * colW, iy = y + 14 + r * 66;
        int id = H_APP + (int)i;
        float k = 1 + 0.1f * hv(id) - 0.12f * prs(id);
        float s = is * k, ox = ix - (s - is) / 2, oy = iy - (s - is) / 2 - 2 * hv(id);
        if (apps[i].bmp) {
            D2D1_RECT_F d{ox, oy, ox + s, oy + s};
            rt->DrawBitmap(apps[i].bmp, &d, gA, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR, nullptr);
        } else {
            col(0.25f, 0.25f, 0.27f); fillRR(ox, oy, s, s, 10);
            col(1, 1, 1, 0.9f); text(apps[i].name.substr(0, 1), fTitle, ox, oy, s, s, DWRITE_TEXT_ALIGNMENT_CENTER);
        }
        col(1, 1, 1, 0.55f + 0.4f * hv(id));
        text(apps[i].name, fApp, ix - gap / 2, iy + is + 3, colW, 14, DWRITE_TEXT_ALIGNMENT_CENTER);
        addHit(ix - gap / 2, iy - 4, colW, is + 22, id);
    }
    if (apps.empty()) { col(1, 1, 1, 0.4f); text(L"Sin atajos", fTiny, x, y + h / 2 - 7, w, 14, DWRITE_TEXT_ALIGNMENT_CENTER); }
}

// ---------------------------------------------------------------- pestaña Herramientas
static void drawPicker(float x, float cy, float w) {
    static const wchar_t* LBL[3] = {L"h", L"min", L"s"};
    const float RH = 26, colW = 64, x0 = x + (w - 3 * colW) / 2;
    pickCy = cy;
    col(1, 1, 1, 0.1f); fillRR(x0 - 4, cy - 15, 3 * colW + 8, 30, 9);  // franja de selección
    D2D1_RECT_F clip{x + 4, cy - 2.2f * RH, x + w - 4, cy + 2.2f * RH};
    rt->PushAxisAlignedClip(&clip, D2D1_ANTIALIAS_MODE_PER_PRIMITIVE);
    D2D1_MATRIX_3X2_F base; rt->GetTransform(&base);
    for (int c = 0; c < 3; c++) {
        float pos = tw(700 + c, pickT[c], 14);
        float cx = x0 + c * colW + colW / 2 - 6;
        int b0 = (int)floorf(pos);
        for (int k = -3; k <= 4; k++) {
            int i = b0 + k; float d = i - pos, ang = d * 0.40f;
            if (fabsf(ang) > 1.45f) continue;
            float yy = cy + sinf(ang) * (RH / 0.40f), sc = cosf(ang);  // como un cilindro que gira
            int val = ((i % PICK_N[c]) + PICK_N[c]) % PICK_N[c];
            float sel = clampf(1 - fabsf(d), 0, 1);
            col(1, 1, 1, (0.32f + 0.68f * sel) * sc * sc);
            D2D1_MATRIX_3X2_F sy{1, 0, 0, sc, 0, yy - sc * yy};
            D2D1_MATRIX_3X2_F m = mmul(sy, base);
            rt->SetTransform(&m);
            textN(std::to_wstring(val), fMid, cx - 26, yy - 13, 44, 26, DWRITE_TEXT_ALIGNMENT_TRAILING);
        }
        rt->SetTransform(&base);
        col(1, 1, 1, 0.9f); text(LBL[c], fSmall, cx + 21, cy - 9, 30, 18);
        addHit(x0 + c * colW, cy - 2.2f * RH, colW, 4.4f * RH, H_PICK + c);
    }
    rt->PopAxisAlignedClip();
}
static void drawTimer(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    D2D1_COLOR_F tc = timerColor();
    colC(tc); text(pomo ? L"Pomodoro" : L"Temporizador", fCalHead, x + 16, y + 12, 100, 18);
    static const wchar_t* MODES[] = {L"Normal", L"Pomodoro"};
    segmented(x + w - 14 - 120, y + 9, 120, 22, MODES, 2, pomo ? 1 : 0, 2, H_TM_MODE);
    float cx = x + w / 2, cy = y + 96;
    // parado en modo normal: ruleta; si no, anillo (con fundido entre ambos)
    float showRing = easeOut(tw(13, (pomo || tmState) ? 1.f : 0.f, 14));
    float ga = gA; bool hs = hitsOn;
    if (showRing < 0.999f) { gA = ga * (1 - showRing); hitsOn = hs && showRing < 0.01f; drawPicker(x, cy, w); hitsOn = hs; }
    if (showRing > 0.001f) {
        gA = ga * showRing;
        float R = 40 * (0.85f + 0.15f * showRing);
        ULONGLONG rem = tmRemaining();
        ring(cx, cy - 4, R, tmDur ? (float)rem / tmDur : 0, tc, 6);
        col(1, 1, 1, tmState == 2 ? 0.6f : 1); textN(fmtClock(rem, true), fMid, cx - 40, cy - 19, 80, 26, DWRITE_TEXT_ALIGNMENT_CENTER);
        const wchar_t* sub = pomo ? (pomoPhase == 0 ? L"Enfoque" : L"Descanso") : (tmState == 2 ? L"En pausa" : L"Quedan");
        col(1, 1, 1, 0.45f); text(sub, fTiny, cx - 44, cy + 6, 88, 14, DWRITE_TEXT_ALIGNMENT_CENTER);
        if (pomo) {  // pomodoros hechos en la tanda de 4
            int done = pomoCount % 4; if (pomoCount && !done) done = 4;
            for (int i = 0; i < 4; i++) { if (i < done) colC(TOMATO); else col(1, 1, 1, 0.18f); circle(cx - 15 + i * 10, cy + 47, 3); }
        }
    }
    gA = ga;
    float by = y + 178;
    bool canReset = tmState != 0 || (pomo && (pomoCount > 0 || pomoPhase != 0));
    float bReset = pomo ? cx - 50 : cx - 30, bPlay = pomo ? cx : cx + 30;
    roundBtn(bReset, by, 18, {1, 1, 1, 1}, 0.12f, H_TM_RESET);
    col(1, 1, 1, canReset ? 0.9f : 0.35f); glyph(L"\uE72C", fIcon, bReset, by);
    bool canStart = pomo || tmState || pickMs() > 0;
    roundBtn(bPlay, by, 20, tc, 0.22f, H_TM_PLAY);
    colC(tc, canStart ? 1.f : 0.4f); playIcon(bPlay + (tmState == 1 ? 0 : 1.5f), by, 13 * (1 - 0.12f * prs(H_TM_PLAY)), tmState == 1);
    if (pomo) {
        roundBtn(cx + 50, by, 18, {1, 1, 1, 1}, 0.12f, H_TM_SKIP);
        col(1, 1, 1, 0.9f); glyph(L"\uE893", fIcon, cx + 50, by);
    }
}
static int examKind(const std::wstring& t) {  // 1 examen, 2 entrega
    std::wstring l; for (auto c : t) l += (wchar_t)towlower(c);
    const wchar_t* ex[] = {L"examen", L"exam", L"parcial", L"midterm", L"final", L"ec1", L"ec2", L"pc1", L"pc2", L"pc3", L"prueba", L"quiz", L"test"};
    for (auto k : ex) if (l.find(k) != std::wstring::npos) return 1;
    if (l.find(L"entrega") != std::wstring::npos || l.find(L"deadline") != std::wstring::npos) return 2;
    return 0;
}
static std::wstring fmtDur(int m) {
    if (m < 60) return std::to_wstring(std::max(m, 1)) + L" min";
    return std::to_wstring(m / 60) + L" h" + (m % 60 ? L" " + std::to_wstring(m % 60) + L" min" : L"");
}
static std::wstring dayLabel(long day, long today) {
    if (day == today) return L"Hoy";
    if (day == today + 1) return L"Mañana";
    int y, m, d; civilFromDays(day, y, m, d);
    return std::wstring(DOW[dowOf(y, m, d)]) + L" " + std::to_wstring(d) + L" " + MON[m - 1];
}
static void drawNextEvent(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    SYSTEMTIME st; GetLocalTime(&st);
    long t = daysFromCivil(st.wYear, st.wMonth, st.wDay); int now = st.wHour * 60 + st.wMinute;
    const CalEvent* ev[2] = {}; int n = 0;
    for (auto& e : events) {  // siguientes eventos con hora (los de todo el día, como festivos, no cuentan)
        if (e.start < 0 || e.day < t) continue;
        if (e.day == t && (e.end >= 0 ? e.end <= now : e.start < now)) continue;
        ev[n++] = &e; if (n == 2) break;
    }
    col(1, 1, 1, 0.5f); text(L"Próximo", fCalHead, x + 16, y + 12, 100, 18);
    if (!ev[0]) {
        col(1, 1, 1, 0.3f); glyph(L"", fGlyph, x + w / 2, y + 74, 44);
        col(1, 1, 1, 0.75f); text(L"Nada a la vista", fBody, x, y + 100, w, 18, DWRITE_TEXT_ALIGNMENT_CENTER);
        col(1, 1, 1, 0.4f); text(L"Conecta el calendario de la uni", fTiny, x, y + 120, w, 14, DWRITE_TEXT_ALIGNMENT_CENTER);
        button(x + 14, y + h - 44, w - 28, 28, L"Conectar calendario", H_EDIT_CAL);
        return;
    }
    const CalEvent& e = *ev[0];
    int kind = examKind(e.title);
    if (kind) {
        D2D1_COLOR_F kc = kind == 1 ? RED : ORANGE; const wchar_t* kt = kind == 1 ? L"Examen" : L"Entrega";
        colC(kc, 0.2f); fillRR(x + w - 14 - 58, y + 10, 58, 20, 10);
        colC(kc); text(kt, fTiny, x + w - 14 - 58, y + 10, 58, 20, DWRITE_TEXT_ALIGNMENT_CENTER);
    }
    colC(e.color); fillRR(x + 16, y + 40, 3.5f, 36, 1.75f);
    col(1, 1, 1); text(e.title, fTitle, x + 26, y + 37, w - 40, 21);
    std::wstring when = dayLabel(e.day, t) + L", " + hhmm(e.start) + (e.end >= 0 ? L" - " + hhmm(e.end) : L"");
    col(1, 1, 1, 0.55f); text(when, fSmall, x + 26, y + 58, w - 40, 18);
    if (!e.loc.empty()) {
        col(1, 1, 1, 0.45f); glyph(L"", fIcon, x + 23, y + 88, 16);
        text(e.loc, fSmall, x + 33, y + 79, w - 47, 18);
    }
    int mins = (int)(e.day - t) * 1440 + e.start - now;
    bool ongoing = mins <= 0;
    std::wstring big, lbl;
    if (ongoing) { big = L"Ahora"; lbl = e.end >= 0 ? L"Termina en " + fmtDur(e.end - now) : L"Ha empezado"; }
    else if (mins >= 1440 && e.day - t >= 1) { lbl = L"Faltan"; big = e.day - t == 1 ? L"Mañana" : std::to_wstring(e.day - t) + L" días"; }
    else { lbl = L"Empieza en"; big = fmtDur(mins); }
    col(1, 1, 1, 0.45f); text(lbl, fTiny, x + 16, y + 106, w - 32, 14);
    if (kind == 1) colC(RED); else col(1, 1, 1);
    textN(big, fBig, x + 14, y + 118, w - 28, 40);
    if (ongoing && e.end > e.start) {
        float fr = clampf((float)(now - e.start) / (e.end - e.start), 0, 1);
        col(1, 1, 1, 0.12f); fillRR(x + 16, y + 160, w - 32, 4, 2);
        colC(e.color); fillRR(x + 16, y + 160, (w - 32) * fr, 4, 2);
    }
    if (ev[1]) {
        col(1, 1, 1, 0.08f); fillRR(x + 16, y + h - 32, w - 32, 1, 0.5f);
        col(1, 1, 1, 0.45f);
        text(L"Después: " + ev[1]->title + L", " + dayLabel(ev[1]->day, t) + L" " + hhmm(ev[1]->start), fTiny, x + 16, y + h - 26, w - 32, 16);
    }
    civilFromDays(e.day, nextY, nextM, nextD);
    addHit(x, y, w, h, H_NEXTEV);
}

static void slider(float x, float y, float w, float h, float v, const wchar_t* g, int id, int key, bool dragging, bool enabled) {
    float fv = dragging ? v : tw(key, v, 20);
    float ga = gA; if (!enabled) gA *= 0.4f;
    col(1, 1, 1, 0.12f + 0.04f * hv(id)); fillRR(x, y, w, h, 11);
    D2D1_RECT_F cl{x, y, x + w * fv, y + h};
    rt->PushAxisAlignedClip(&cl, D2D1_ANTIALIAS_MODE_PER_PRIMITIVE);
    col(1, 1, 1, 0.92f); fillRR(x, y, w, h, 11);
    rt->PopAxisAlignedClip();
    if (fv * w > 26) col(0.15f, 0.15f, 0.16f); else col(1, 1, 1, 0.8f);
    glyph(g, fIcon, x + 15, y + h / 2);
    if (fv < 0.82f) col(1, 1, 1, 0.55f); else col(0.15f, 0.15f, 0.16f, 0.7f);
    textN(enabled ? std::to_wstring((int)lroundf(v * 100)) + L"%" : L"--", fTiny, x, y, w - 12, h, DWRITE_TEXT_ALIGNMENT_TRAILING);
    if (enabled) addHit(x, y, w, h, id);
    gA = ga;
}
static void drawControls(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    cardTitle(L"Controles", x, y, {1, 1, 1, 1}, 0.5f);
    volInit(); briStart();
    bool mute = false; float v = volGet(&mute);
    float vx = x + 14, vw = w - 28;
    volRect = {vx, y + 36, vx + vw, y + 66};
    slider(vx, y + 36, vw, 30, mute ? 0 : v, mute || v < 0.01f ? L"\uE74F" : L"\uE767", H_VOL, 11, dragKind == 1, true);
    int b = briCur;
    briRect = {vx, y + 72, vx + vw, y + 102};
    slider(vx, y + 72, vw, 30, b < 0 ? 0 : b / 100.f, L"\uE793", H_BRI, 14, dragKind == 2, briAvail && b >= 0);
    struct Q { const wchar_t* g; const wchar_t* l; bool on; } q[4] = {
        {L"\uEC32", L"Cafeína", caffeine}, {mute ? L"\uE74F" : L"\uE767", L"Silencio", mute}, {L"\uE722", L"Captura", false}, {L"\uE72E", L"Bloquear", false}};
    float qy = y + 140, step = (vw - 40) / 3.f;
    for (int i = 0; i < 4; i++) {
        float cx = vx + 20 + i * step; int id = H_Q + i;
        float on = tw(12 + i * 100, q[i].on ? 1.f : 0.f, 14);
        float k = 1 - 0.08f * prs(id), hh = hv(id);
        colC(mix({0.2f + 0.07f * hh, 0.2f + 0.07f * hh, 0.215f + 0.07f * hh, 1}, ACC(), on)); circle(cx, qy, 19 * k);
        col(1, 1, 1); glyph(q[i].g, fIcon, cx, qy);
        col(1, 1, 1, 0.6f); text(q[i].l, fTiny, cx - 30, qy + 22, 60, 14, DWRITE_TEXT_ALIGNMENT_CENTER);
        addHit(cx - 21, qy - 21, 42, 57, id);
    }
    if (caffeine) { colC(ACC(), 0.9f); text(L"La pantalla no se apagará", fTiny, x, y + h - 20, w, 14, DWRITE_TEXT_ALIGNMENT_CENTER); }
}

// ---------------------------------------------------------------- pestaña Ajustes
static void drawGeneral(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    cardTitle(L"General", x, y, {1, 1, 1, 1}, 0.5f);
    struct R { const wchar_t* l; bool on; int id; } r[6] = {
        {L"Iniciar con Windows", cfg.autostart, H_SET}, {L"Abrir al pasar el ratón", cfg.hoverOpen, H_SET + 1},
        {L"Rayita si hay una ventana debajo", cfg.discreetOn, H_SET + 6}, {L"Ocultar en pantalla completa", cfg.hideFull, H_SET + 2},
        {L"Animar ecualizador", cfg.eq, H_SET + 3}, {L"Mostrar batería", cfg.battery, H_SET + 4}};
    for (int i = 0; i < 6; i++) {
        float ry = y + 47 + i * 27;
        col(1, 1, 1, 0.9f); text(r[i].l, fSmall, x + 16, ry - 9, w - 78, 18);
        switchCtl(x + w - 16 - 42, ry, r[i].on, r[i].id - H_SET, r[i].id);
        addHit(x + 8, ry - 13, w - 16, 26, r[i].id);
    }
}
static void drawCalSettings(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    cardTitle(L"Calendario", x, y, {1, 1, 1, 1}, 0.5f);
    float ry = y + 52;
    col(1, 1, 1, 0.9f); text(L"Avisos en la isla", fSmall, x + 16, ry - 9, w - 80, 18);
    switchCtl(x + w - 16 - 42, ry, cfg.alerts, 5, H_SET + 5);
    addHit(x + 8, ry - 15, w - 16, 30, H_SET + 5);
    col(1, 1, 1, 0.45f); text(L"Avisar con antelación", fTiny, x + 16, y + 74, w - 32, 14);
    static const wchar_t* L3[] = {L"15 min", L"30 min", L"1 h"};
    int sel = cfg.alertMins <= 15 ? 0 : cfg.alertMins <= 30 ? 1 : 2;
    segmented(x + 14, y + 92, w - 28, 26, L3, 3, sel, 0, H_SEG_ALERT, cfg.alerts ? 1.f : 0.4f);
    button(x + 14, y + 132, w - 28, 28, L"Editar calendarios", H_EDIT_CAL);
    button(x + 14, y + 166, w - 28, 28, L"Editar atajos", H_EDIT_APPS);
}
static void drawLook(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    cardTitle(L"Aspecto", x, y, {1, 1, 1, 1}, 0.5f);
    static const wchar_t* S3[] = {L"Pequeña", L"Normal", L"Grande"};
    static const wchar_t* O3[] = {L"Sólido", L"Medio", L"Cristal"};
    static const wchar_t* T3[] = {L"Siempre", L"Con el ratón", L"Sin el ratón"};
    col(1, 1, 1, 0.45f); text(L"Tamaño", fTiny, x + 16, y + 31, w - 32, 13);
    segmented(x + 14, y + 44, w - 28, 22, S3, 3, cfg.size, 1, H_SEG_SIZE);
    col(1, 1, 1, 0.45f); text(L"Fondo", fTiny, x + 16, y + 69, w - 32, 13);
    segmented(x + 14, y + 82, w - 28, 22, O3, 3, cfg.opacity, 3, H_SEG_OPA);
    col(1, 1, 1, 0.45f); text(L"Transparente", fTiny, x + 16, y + 107, w - 32, 13);
    segmented(x + 14, y + 120, w - 28, 22, T3, 3, cfg.transMode, 4, H_SEG_TMODE, cfg.opacity ? 1.f : 0.4f);
    float step = (w - 40) / 5.f, cyc = y + 160;
    float rx = tw(4, (float)cfg.accent, 16);
    col(1, 1, 1, 0.9f);
    D2D1_ELLIPSE e{{x + 20 + rx * step, cyc}, 12.5f, 12.5f}; rt->DrawEllipse(&e, br, 2, nullptr);
    for (int i = 0; i < 6; i++) {
        float cx = x + 20 + i * step; int id = H_ACC + i;
        colC(ACCENTS[i]); circle(cx, cyc, 8.5f + 1.2f * hv(id) - 1.5f * prs(id));
        addHit(cx - 12, cyc - 12, 24, 24, id);
    }
    button(x + 14, y + 180, w - 28, 22, L"Salir de la isla", H_QUIT, RED);
}

// ---------------------------------------------------------------- pestaña Bandeja
static void drawShelf(float x, float y, float w, float h) {
    beginCard(0, y); card(x, y, w, h);
    float dh = tw(15, dropHover ? 1.f : 0.f, 16);
    col(1, 1, 1, 0.5f); text(L"Bandeja", fCalHead, x + 16, y + 12, 80, 18);
    if (!shelf.empty()) {
        col(1, 1, 1, 0.35f); textN(std::to_wstring(shelf.size()) + (shelf.size() == 1 ? L" archivo" : L" archivos"), fTiny, x + 76, y + 12, 120, 18);
        float bw = 76, bx = x + w - 14 - bw;
        col(1, 1, 1, 0.08f + 0.07f * hv(H_SHELF_CLEAR)); fillRR(bx, y + 9, bw, 24, 9);
        col(1, 1, 1, 0.8f); glyph(L"", fIcon, bx + 15, y + 21, 16); text(L"Vaciar", fTiny, bx + 24, y + 9, bw - 28, 24);
        addHit(bx, y + 9, bw, 24, H_SHELF_CLEAR);
    }
    float ga = gA;
    // archivos
    if (!shelf.empty()) {
        gA = ga * (1 - 0.85f * dh);
        const float tw_ = 90, th = 78, gap = 4;
        int cols = (int)((w - 28 + gap) / (tw_ + gap));
        float x0 = x + 14 + ((w - 28) - (cols * tw_ + (cols - 1) * gap)) / 2, y0 = y + 40;
        int maxShow = cols * 2;
        int show = (int)std::min<size_t>(shelf.size(), maxShow);
        bool more = (int)shelf.size() > maxShow;
        if (more) show = maxShow - 1;
        bool hs = hitsOn; if (dh > 0.01f) hitsOn = false;
        for (int i = 0; i < show; i++) {
            ShelfItem& it = shelf[i];
            float tx = x0 + (i % cols) * (tw_ + gap), ty = y0 + (i / cols) * (th + gap);
            int id = H_SHELF + i, did = H_SHELF_DEL + i;
            float hh = std::max(hv(id), hv(did)), pp = prs(id);
            col(1, 1, 1, 0.07f * hh + 0.05f * pp); fillRR(tx, ty, tw_, th, 12);
            if (!it.bmp && !it.tried) { it.tried = true; it.bmp = thumbFor(it.path, (UINT)lroundf(48 * scale)); }
            float s = 46 * (1 - 0.06f * pp), cx = tx + tw_ / 2, cy = ty + 6 + 23;
            if (it.bmp) {
                D2D1_SIZE_F bs = it.bmp->GetSize(); float k = s / std::max(bs.width, bs.height);
                D2D1_RECT_F d{cx - bs.width * k / 2, cy - bs.height * k / 2, cx + bs.width * k / 2, cy + bs.height * k / 2};
                rt->DrawBitmap(it.bmp, &d, gA, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR, nullptr);
            } else { col(1, 1, 1, 0.4f); glyph(L"", fGlyph, cx, cy, 46); }
            col(1, 1, 1, 0.55f + 0.4f * hh); text(it.name, fTiny, tx + 4, ty + th - 22, tw_ - 8, 16, DWRITE_TEXT_ALIGNMENT_CENTER);
            if (hh > 0.01f) {  // quitar de la bandeja
                float dx = tx + tw_ - 12, dy = ty + 12;
                col(0.3f + 0.15f * hv(did), 0.3f + 0.15f * hv(did), 0.32f + 0.15f * hv(did), hh); circle(dx, dy, 8);
                col(1, 1, 1, hh); line(dx - 2.8f, dy - 2.8f, dx + 2.8f, dy + 2.8f, 1.4f); line(dx + 2.8f, dy - 2.8f, dx - 2.8f, dy + 2.8f, 1.4f);
                addHit(dx - 9, dy - 9, 18, 18, did);
            }
            addHit(tx, ty, tw_, th, id);
        }
        if (more) {
            float tx = x0 + (show % cols) * (tw_ + gap), ty = y0 + (show / cols) * (th + gap);
            col(1, 1, 1, 0.5f); text(L"+" + std::to_wstring(shelf.size() - show), fTitle, tx, ty, tw_, th, DWRITE_TEXT_ALIGNMENT_CENTER);
        }
        hitsOn = hs;
        gA = ga;
    }
    // zona para soltar
    if (shelf.empty() || dh > 0.01f) {
        float za = shelf.empty() ? 1.f : dh;
        gA = ga * za;
        float zx = x + 14, zy = y + 38, zw = w - 28, zh = h - 52;
        colC(ACC(), 0.1f * dh); fillRR(zx, zy, zw, zh, 16);
        colC(mix({1, 1, 1, 0.22f}, ACC(), dh));
        D2D1_ROUNDED_RECT rr{{zx, zy, zx + zw, zy + zh}, 16, 16}; rt->DrawRoundedRectangle(&rr, br, 1.6f, dashStroke);
        float cy = zy + zh / 2 - 14 - 5 * dh;
        colC(mix({1, 1, 1, 0.45f}, ACC(), dh)); glyph(L"", fGlyph, x + w / 2, cy, 44);
        col(1, 1, 1, 0.9f); text(dh > 0.5f ? L"Suelta para guardar" : L"Arrastra archivos aquí", fTitle, x, cy + 22, w, 22, DWRITE_TEXT_ALIGNMENT_CENTER);
        col(1, 1, 1, 0.4f);
        text(L"Se quedan aquí para soltarlos luego en otra carpeta, en Chrome o en Aula Global", fTiny, x, cy + 44, w, 16, DWRITE_TEXT_ALIGNMENT_CENTER);
        gA = ga;
    }
}

// ---------------------------------------------------------------- panel
static void drawHeader(float ox, float oy) {
    float hy = oy + 10, hh = 26, tx = ox + 16;
    const float tws[3] = {70, 112, 94}, sts[3] = {0, 70, 182};
    const wchar_t* T[3] = {L"Inicio", L"Herramientas", L"Bandeja"};
    col(1, 1, 1, 0.08f); fillRR(tx, hy, tws[0] + tws[1] + tws[2] + 4, hh, 13);
    float ti = tw(1, (float)(view == V_SET ? lastTab : view), 15), ia = tw(5, view == V_SET ? 0.25f : 1.f, 15);
    int i0 = std::min(1, std::max(0, (int)floorf(ti))); float fi = ti - i0;
    float ix = tx + 2 + sts[i0] + (sts[i0 + 1] - sts[i0]) * fi, iw = tws[i0] + (tws[i0 + 1] - tws[i0]) * fi;
    col(1, 1, 1, 0.18f * ia); fillRR(ix, hy + 2, iw, hh - 4, 11);
    float sx = tx + 2;
    for (int i = 0; i < 3; i++) {
        int id = i < 2 ? H_TAB0 + i : H_TAB2;
        col(1, 1, 1, view == i ? 1.f : 0.5f + 0.4f * hv(id));
        float lw = i == 2 && !shelf.empty() ? 14.f : 0.f;
        text(T[i], fTab, sx - lw / 2, hy, tws[i], hh, DWRITE_TEXT_ALIGNMENT_CENTER);
        if (lw > 0) {  // número de archivos en la bandeja
            float bx = sx + tws[i] / 2 + textWidth(T[i], fTab) / 2 + 4;
            colC(ACC()); circle(bx + 3, hy + hh / 2, 8);
            col(1, 1, 1); textN(std::to_wstring(std::min<size_t>(shelf.size(), 99)), fTiny, bx - 5, hy, 16, hh, DWRITE_TEXT_ALIGNMENT_CENTER);
        }
        addHit(sx, hy, tws[i], hh, id);
        sx += tws[i];
    }
    // engranaje (gira al entrar en ajustes)
    float gx = ox + EW - 16 - 13, gcy = hy + hh / 2;
    float on = tw(6, view == V_SET ? 1.f : 0.f, 12);
    float k = 1 - 0.1f * prs(H_GEAR);
    col(1, 1, 1, 0.08f + 0.08f * hv(H_GEAR) + 0.12f * on); circle(gx, gcy, 13 * k);
    D2D1_MATRIX_3X2_F base; rt->GetTransform(&base);
    float a = on * (float)M_PI / 2, c = cosf(a), s = sinf(a);
    D2D1_MATRIX_3X2_F rot{c, s, -s, c, gx - c * gx + s * gcy, gcy - s * gx - c * gcy};
    D2D1_MATRIX_3X2_F m{rot._11 * base._11 + rot._12 * base._21, rot._11 * base._12 + rot._12 * base._22,
                        rot._21 * base._11 + rot._22 * base._21, rot._21 * base._12 + rot._22 * base._22,
                        rot._31 * base._11 + rot._32 * base._21 + base._31, rot._31 * base._12 + rot._32 * base._22 + base._32};
    rt->SetTransform(&m);
    col(1, 1, 1, 0.75f + 0.25f * on); glyph(L"\uE713", fIcon, gx, gcy);
    rt->SetTransform(&base);
    addHit(gx - 14, gcy - 14, 28, 28, H_GEAR);
    // Claude Code: destello naranja que gira un poco al pasar el ratón
    float qx = gx - 34, ch = hv(H_CLAUDE), kc = 1 - 0.1f * prs(H_CLAUDE);
    col(1, 1, 1, 0.08f + 0.08f * ch); circle(qx, gcy, 13 * kc);
    colC({0.851f, 0.467f, 0.341f, 1});
    for (int i = 0; i < 12; i++) {
        float a = i * (float)M_PI / 6 + ch * 0.5f, len = (i % 2 ? 5.6f : 7.4f) * kc;
        line(qx + cosf(a) * 1.6f, gcy + sinf(a) * 1.6f, qx + cosf(a) * len, gcy + sinf(a) * len, 1.6f);
    }
    addHit(qx - 14, gcy - 14, 28, 28, H_CLAUDE);
    float lx = qx - 20 - 90;
    if (ch > 0.01f) { col(1, 1, 1, 0.75f * ch); text(L"Claude Code", fTiny, lx, hy, 90, hh, DWRITE_TEXT_ALIGNMENT_TRAILING); }
    // temporizador en marcha visible desde cualquier pestaña
    else if (tmState == 1 && view != 1) {
        colC(timerColor()); textN(fmtClock(tmRemaining(), true), fTab, lx, hy, 90, hh, DWRITE_TEXT_ALIGNMENT_TRAILING);
    } else if (swRun && view != 1) {
        colC(ORANGE); textN(fmtClock(swElapsed(), false), fTab, lx, hy, 90, hh, DWRITE_TEXT_ALIGNMENT_TRAILING);
    }
}
static void drawView(int v, float ox, float y) {
    float h = EH - 44 - 12, x = ox + 12;
    if (v == 0) {
        drawMusic(x, y, 252, h, 0); x += 262;
        drawCalendar(x, y, 202, h, 1); x += 212;
        drawStats(x, y, 110, h, 2); x += 120;
        drawApps(x, y, ox + EW - 12 - x, h, 3);
    } else if (v == V_TOOLS) {
        drawTimer(x, y, 250, h, 0); x += 260;
        drawNextEvent(x, y, 210, h, 1); x += 220;
        drawControls(x, y, ox + EW - 12 - x, h, 2);
    } else if (v == V_SHELF) {
        drawShelf(x, y, EW - 24, h);
    } else {
        drawGeneral(x, y, 250, h, 0); x += 260;
        drawCalSettings(x, y, 210, h, 1); x += 220;
        drawLook(x, y, ox + EW - 12 - x, h, 2);
    }
}

// ---------------------------------------------------------------- render + ventana por capas
static bool springsSettled() { return sw.settled() && sh.settled() && sr.settled(); }
static void startAnim() {
    if (animating) return;
    animating = true; QueryPerformanceCounter(&lastTick); setEco(false);
}
static bool eqActive() { return visible && cfg.eq && !expanded && media.playing && pillMode() == PM_MUSIC; }
static int wantTick() {
    if (alertOn) return 33;
    if (!visible) return tmState == 1 ? 250 : 0;
    if (expanded && view == 1 && swRun) return 50;
    if (expanded && view == 1 && tmState == 1) return 100;
    if (eqActive()) return 70;
    if (tmState == 1 || swRun) return 250;
    return 0;
}
static void updateTick() {
    int w = wantTick();
    if (w != tickIv) {
        if (w >= 250) SetCoalescableTimer(gHwnd, T_TICK, w, nullptr, 40);  // contadores de la píldora: algo de holgura
        else if (w) SetTimer(gHwnd, T_TICK, w, nullptr);
        else KillTimer(gHwnd, T_TICK);
        tickIv = w; lastTickMs = nowMs();
    }
}
static int lastMode = -1;
static int shownView = 0, prevView = 0;
static bool discreet = false, peeking = false;  // rayita cuando hay una ventana debajo; Ctrl para ver a través  // transición solo entre la vista anterior y la nueva
static void buildCache() {
    if (!cacheRT) {
        D2D1_SIZE_F sz{EW, EH};
        if (FAILED(dcrt->CreateCompatibleRenderTarget(&sz, nullptr, nullptr, D2D1_COMPATIBLE_RENDER_TARGET_OPTIONS_NONE, &cacheRT))) { cacheRT = nullptr; return; }
        cacheRT->SetTextAntialiasMode(D2D1_TEXT_ANTIALIAS_MODE_GRAYSCALE);
    }
    ID2D1RenderTarget* saved = rt; rt = cacheRT;
    bool hs = hitsOn; float ga = gA;
    rt->BeginDraw();
    D2D1_COLOR_F clear{0, 0, 0, 0}; rt->Clear(&clear);
    D2D1_MATRIX_3X2_F I{1, 0, 0, 1, 0, 0}; rt->SetTransform(&I);
    hitsOn = false; gOpen = 1; gA = 1; gViewA = 1;
    drawHeader(0, 0);
    drawView(view, 0, 44);
    rt->EndDraw();
    rt = saved; hitsOn = hs; gA = ga;
    cacheValid = true;
}

static void render() {
    if (!visible || !rt) { updateTick(); return; }
    float w = sw.x, h = sh.x, r = clampf(sr.x, std::min(4.f, h / 2), h / 2);
    int W = (int)ceilf((w + 2 * M) * scale), H = (int)ceilf((h + 2 * M) * scale);
    if (W > dibW) W = dibW; if (H > dibH) H = dibH;
    RECT rc{0, 0, W, H};
    dcrt->BindDC(memDC, &rc);
    rt->BeginDraw();
    D2D1_COLOR_F clear{0, 0, 0, 0}; rt->Clear(&clear);
    D2D1_MATRIX_3X2_F I{1, 0, 0, 1, 0, 0}; rt->SetTransform(&I);
    hits.clear();
    float p = clampf((h - CH) / (EH - CH), 0, 1.2f);
    float px = M, py = M;
    if (p > 0.01f) {  // sombra solo al abrir: así la píldora no bloquea clics alrededor
        float sp = clampf(p, 0, 1);
        for (int i = 4; i >= 1; i--) {
            gA = 1; col(0, 0, 0, 0.06f * sp);
            float g = i * 3.4f;
            D2D1_ROUNDED_RECT rr{{px - g, py - g + 4, px + w + g, py + h + g + 4}, r + g, r + g};
            rt->FillRoundedRectangle(&rr, br);
        }
    }
    {
        bool over = hovered || dragKind != 0;
        bool trans = cfg.transMode == 0 || (cfg.transMode == 1 ? over : !over);
        gA = 1; col(0, 0, 0, tw(16, trans ? bgAlpha() : 1.f, 9));
    }
    D2D1_ROUNDED_RECT pill{{px, py, px + w, py + h}, r, r};
    rt->FillRoundedRectangle(&pill, br);
    if (alertOn && !expanded) {
        float pulse = 0.5f + 0.5f * sinf((float)(nowMs() - alertAt) / 1000.f * 6.f);
        colC(alertPomo ? timerColor() : ORANGE, 0.35f + 0.45f * pulse); rt->DrawRoundedRectangle(&pill, br, 1.5f, nullptr);
    } else {
        float dsc = clampf((CH - h) / (CH - 5), 0, 1);  // 1 = rayita
        col(1, 1, 1, 0.07f + 0.28f * dsc); rt->DrawRoundedRectangle(&pill, br, 1.0f, nullptr);
        if (dsc > 0.5f) {
            // temporizador en marcha: la rayita se rellena con su color
            if (tmState && tmDur) { colC(timerColor(), 0.9f); fillRR(px + 1, py + 1, (w - 2) * (float)tmRemaining() / tmDur, h - 2, (h - 2) / 2); }
        }
    }
    // franja casi invisible (pero que recibe el ratón) entre el borde de arriba de la pantalla y la isla.
    // En modo rayita sirve para alcanzarla; con el ratón encima o el panel abierto evita que, al llevar
    // el ratón arriba del todo, la isla crea que se ha salido y se abra y se cierre en bucle.
    if (discreet || hovered || expanded || dragKind) {
        float dsc = clampf((CH - h) / (CH - 5), 0, 1), ext = dsc > 0.5f ? 40.f : 0.f;
        gA = 1; col(0, 0, 0, 0.004f);
        D2D1_RECT_F hz{px - ext, M - TOPGAP, px + w + ext, py + std::min(h, 6.f) + (dsc > 0.5f ? 6.f : 0.f)};
        rt->FillRectangle(&hz, br);
    }

    D2D1_RECT_F clip{px, py, px + w, py + h};
    rt->PushAxisAlignedClip(&clip, D2D1_ANTIALIAS_MODE_PER_PRIMITIVE);
    float ac = clampf(1 - p * 3.f, 0, 1) * clampf((h - 16) / 14, 0, 1);
    if (ac > 0) {
        int mode = pillMode();
        if (mode != lastMode) { twFrom(7, lastMode < 0 ? 1.f : 0.f, 1.f, 9); lastMode = mode; }
        float mf = easeOut(tw(7, 1.f, 9));
        gA = ac * mf;
        hitsOn = false;
        drawCollapsed(px, py + (1 - mf) * 4, w, mode);
    }
    float ae = easeOut(clampf((p - 0.4f) / 0.6f, 0, 1));
    if (ae > 0) {
        float s = 0.94f + 0.06f * ae, cx = px + w / 2;
        D2D1_MATRIX_3X2_F base{s, 0, 0, s, cx - s * cx, py - s * py};
        float ox = cx - EW / 2;
        // abriendo o cerrando: el contenido se dibuja una vez en una imagen y solo se escala y difumina
        if (view != shownView) { prevView = shownView; shownView = view; twFrom(2, 0.f, 1.f, 11); }
        bool inTransition = tw(2, 1.f, 11) < 0.999f;
        bool useCache = !springsSettled() && !inTransition;
        if (useCache && !cacheValid) buildCache();
        if (useCache && cacheRT) {
            rt->SetTransform(&base);
            ID2D1Bitmap* cb = nullptr; cacheRT->GetBitmap(&cb);
            D2D1_RECT_F d{ox, py, ox + EW, py + EH};
            if (cb) { rt->DrawBitmap(cb, &d, ae, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR, nullptr); cb->Release(); }
            rt->SetTransform(&I);
        } else {
        rt->SetTransform(&base);
        gOpen = ae;
        bool canHit = expanded && ae > 0.85f;
        hitsOn = canHit; gA = ae;
        drawHeader(ox, py);
        // la vista anterior sale hacia un lado y la nueva entra desde el otro; las de en medio no aparecen
        float t = easeOut(tw(2, 1.f, 11));
        float dir = view > prevView ? 1.f : -1.f;
        if (prevView != view && t < 1.f) {
            float a = clampf(1 - t * 1.8f, 0, 1);
            if (a > 0.01f) { gViewA = a; hitsOn = false; drawView(prevView, ox - dir * 36 * t, py + 44); }
        }
        float a = prevView == view ? 1.f : clampf((t - 0.2f) / 0.8f, 0, 1);
        if (a > 0.01f) {
            gViewA = a;
            hitsOn = canHit && t > 0.6f;
            drawView(view, ox + dir * 36 * (1 - t), py + 44);
        }
        rt->SetTransform(&I);
        }
    }
    hitsOn = true;
    rt->PopAxisAlignedClip();
    gA = 1;
    if (rt->EndDraw() == D2DERR_RECREATE_TARGET) { createTarget(); return; }

    POINT dst{(mon.left + mon.right) / 2 - W / 2, mon.top + (int)lroundf((TOPGAP - M) * scale)};
    SIZE sz{W, H}; POINT src{0, 0};
    BLENDFUNCTION bf{AC_SRC_OVER, 0, (BYTE)lroundf(255 * tw(17, peeking ? 0.06f : 1.f, 20)), AC_SRC_ALPHA};
    UpdateLayeredWindow(gHwnd, nullptr, &dst, &sz, memDC, &src, 0, &bf, ULW_ALPHA);
    if (!animating && (!springsSettled() || tweensActive())) startAnim();
    updateTick();
}

// ---------------------------------------------------------------- animación (al ritmo de la pantalla)
static void collapsedTargets() {
    int mode = pillMode();
    int em = 0; bool soon = cfg.alerts && upcomingEvent(&em) && em <= 15;
    if (discreet && !hovered && !alertOn && !soon && !peeking) { sw.t = 120; sh.t = 5; sr.t = 2.5f; return; }
    float w = mode == PM_EVENT ? CW_EVENT : mode == PM_MUSIC ? CW_PLAY : mode == PM_ALERT ? 300.f : CW_IDLE, h = CH;
    if (mode == PM_IDLE && !shelf.empty()) w += 30;
    if (hovered) { w += 10; h += 3; }
    sw.t = w; sh.t = h; sr.t = h / 2;
}
static void step(Spring& s, float dt, float k, float z) {
    float c = 2 * z * sqrtf(k);
    for (int i = 0; i < 8; i++) {  // sub-pasos para estabilidad
        float d = dt / 8, a = k * (s.t - s.x) - c * s.v;
        s.v += a * d; s.x += s.v * d;
    }
    if (s.settled()) { s.x = s.t; s.v = 0; }
}
static void onSettled() {
    cacheValid = false;
    if (!expanded) {
        for (auto it = tweens.begin(); it != tweens.end();) { if (it->first >= 100000 && it->first < 200000) it = tweens.erase(it); else ++it; }
        SafeRelease(vol); briStop(); SafeRelease(cacheRT); cacheValid = false;
        setEco(true); SetCoalescableTimer(gHwnd, T_TRIM, 30000, nullptr, 5000);
    }
}
static void frame() {
    LARGE_INTEGER now; QueryPerformanceCounter(&now);
    float dt = clampf((float)(now.QuadPart - lastTick.QuadPart) / qpf.QuadPart, 0.001f, 1 / 30.f);
    lastTick = now;
    float k = expanded ? 200.f : 270.f, z = expanded ? 0.7f : 0.88f;
    step(sw, dt, k, z); step(sh, dt, k, z); step(sr, dt, k, z);
    stepTweens(dt);
    if (eqActive()) eqTime += dt;
    render();
    if (springsSettled() && !tweensActive()) { animating = false; onSettled(); }
}
static void setExpanded(bool e, int v = -1) {
    if (e == expanded) { if (e && v >= 0 && v != view) { view = v; if (v < V_SET) lastTab = v; render(); } return; }
    expanded = e; cacheValid = false;
    KillTimer(gHwnd, T_COLLAPSE); KillTimer(gHwnd, T_HOVER);
    if (e) {
        gExpandedA = true;
        view = v >= 0 ? v : lastTab; if (view < V_SET) lastTab = view;
        twSnap(1, (float)(view == V_SET ? lastTab : view)); twSnap(2, 1.f); shownView = prevView = view; twSnap(5, view == V_SET ? 0.25f : 1.f); twSnap(6, view == V_SET ? 1.f : 0.f);
        SYSTEMTIME st; GetLocalTime(&st); calY = st.wYear; calM = st.wMonth; selDay = 0; twSnap(8, 0);
        FILETIME fs = fileStamp(appsFile);
        if (CompareFileTime(&fs, &appsStamp) != 0) loadApps();
        loadIcons();
        sw.t = EW; sh.t = EH; sr.t = ER;
        SetEvent(gWake);
    } else {
        gExpandedA = false;
        hoverId = pressId = H_NONE; dragKind = 0; dropHover = false; openedByDrag = false; collapsedTargets();
    }
    startAnim();
}

// ---------------------------------------------------------------- pantalla completa
static bool foregroundIsFullscreen() {
    HWND fg = GetForegroundWindow();
    if (!fg || fg == GetDesktopWindow() || fg == GetShellWindow() || fg == gHwnd) return false;
    wchar_t cls[64]; GetClassNameW(fg, cls, 64);
    if (!wcscmp(cls, L"WorkerW") || !wcscmp(cls, L"Progman") || !wcscmp(cls, L"Shell_TrayWnd")) return false;
    RECT r; if (!GetWindowRect(fg, &r)) return false;
    return r.left <= mon.left && r.top <= mon.top && r.right >= mon.right && r.bottom >= mon.bottom;
}
static bool foregroundUnderIsland() {
    HWND fg = GetForegroundWindow();
    if (!fg || fg == GetDesktopWindow() || fg == GetShellWindow() || fg == gHwnd || IsIconic(fg) || !IsWindowVisible(fg)) return false;
    wchar_t cls[64]; GetClassNameW(fg, cls, 64);
    if (!wcscmp(cls, L"WorkerW") || !wcscmp(cls, L"Progman") || !wcscmp(cls, L"Shell_TrayWnd")) return false;
    RECT r;
    if (FAILED(DwmGetWindowAttribute(fg, DWMWA_EXTENDED_FRAME_BOUNDS, &r, sizeof r)) && !GetWindowRect(fg, &r)) return false;
    int cx = (mon.left + mon.right) / 2, half = (int)(CW_EVENT / 2 * scale);
    int bottom = mon.top + (int)((TOPGAP + CH + 4) * scale);
    return r.left < cx + half && r.right > cx - half && r.top < bottom && r.bottom > mon.top;
}
static void updateDiscreet() {
    bool d = cfg.discreetOn && foregroundUnderIsland();
    if (d == discreet) return;
    discreet = d;
    if (!expanded) { collapsedTargets(); startAnim(); }
}
static void checkFullscreen() {
    updateDiscreet();
    bool hide = cfg.hideFull && !alertOn && foregroundIsFullscreen();
    if (hide == !visible) return;
    visible = !hide; gVisibleA = visible;
    if (hide) { setExpanded(false); ShowWindow(gHwnd, SW_HIDE); }
    else { ShowWindow(gHwnd, SW_SHOWNOACTIVATE); render(); SetEvent(gWake); }
}
static RECT pillScreenRect() {
    RECT r; GetWindowRect(gHwnd, &r);
    int m = (int)(M * scale);
    r.left += m - 4; r.right -= m - 4; r.top += m - 6; r.bottom -= m - 4;
    return r;
}
static void endPeek() {
    if (!peeking) return;
    peeking = false;
    SetWindowLongPtrW(gHwnd, GWL_EXSTYLE, GetWindowLongPtrW(gHwnd, GWL_EXSTYLE) & ~WS_EX_TRANSPARENT);
    POINT pt; GetCursorPos(&pt); RECT r = pillScreenRect();
    if (PtInRect(&r, pt)) {
        // el ratón sigue encima: se queda "dentro" y se sigue vigilando Ctrl, para poder repetir sin moverlo
        hovered = true;
        TRACKMOUSEEVENT t{sizeof t, TME_LEAVE, gHwnd, 0}; TrackMouseEvent(&t);  // el aviso de salida se perdió al ver a través
    } else {
        hovered = false; hoverId = H_NONE;
        if (expanded) SetTimer(gHwnd, T_COLLAPSE, 450, nullptr);
    }
    if (!expanded) collapsedTargets();
    render();
}
static void peekTick() {
    bool ctrl = (GetAsyncKeyState(VK_CONTROL) & 0x8000) != 0;
    POINT pt; GetCursorPos(&pt); RECT r = pillScreenRect();
    bool inside = PtInRect(&r, pt) != 0;
    if (!peeking && ctrl && inside) {
        peeking = true;
        KillTimer(gHwnd, T_COLLAPSE); KillTimer(gHwnd, T_HOVER);
        // deja pasar los clics a lo que hay debajo
        SetWindowLongPtrW(gHwnd, GWL_EXSTYLE, GetWindowLongPtrW(gHwnd, GWL_EXSTYLE) | WS_EX_TRANSPARENT);
        render();
    } else if (peeking && (!ctrl || !inside)) endPeek();
    if ((!inside || !visible) && !peeking) KillTimer(gHwnd, T_PEEK);
}
static void ensureTopmost() {
    RECT me; GetWindowRect(gHwnd, &me);
    for (HWND a = GetWindow(gHwnd, GW_HWNDPREV); a; a = GetWindow(a, GW_HWNDPREV)) {
        if (!IsWindowVisible(a) || !(GetWindowLongPtrW(a, GWL_EXSTYLE) & WS_EX_TOPMOST)) continue;
        RECT r, x; GetWindowRect(a, &r);
        if (IntersectRect(&x, &r, &me)) { SetWindowPos(gHwnd, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE); return; }
    }
}
static void CALLBACK winEvent(HWINEVENTHOOK, DWORD, HWND, LONG, LONG, DWORD, DWORD) { checkFullscreen(); }

static void scheduleClock() {
    SYSTEMTIME st; GetLocalTime(&st);
    SetCoalescableTimer(gHwnd, T_CLOCK, (60 - st.wSecond) * 1000 - st.wMilliseconds + 30, nullptr, 250);
}

// ---------------------------------------------------------------- acciones
static void mediaKey(WORD vk) {
    INPUT in[2] = {};
    in[0].type = INPUT_KEYBOARD; in[0].ki.wVk = vk; in[0].ki.dwFlags = KEYEVENTF_EXTENDEDKEY;
    in[1] = in[0]; in[1].ki.dwFlags |= KEYEVENTF_KEYUP;
    SendInput(2, in, sizeof(INPUT));
    gPollSoon = true; SetEvent(gWake);
}
static void openCalendarDay(int y, int m, int d) {
    wchar_t u[128]; swprintf(u, 128, L"https://calendar.google.com/calendar/r/day/%d/%d/%d", y, m, d);
    ShellExecuteW(nullptr, L"open", u, nullptr, nullptr, SW_SHOWNORMAL);
    setExpanded(false);
}
static void finishTimer() {
    alertOn = true; alertAt = nowMs(); alertPomo = pomo;
    if (pomo) {  // la siguiente fase empieza sola, con un aviso corto
        if (pomoPhase == 0) { pomoCount++; pomoArm(1); } else pomoArm(0);
        tmEnd = nowMs() + tmDur; tmState = 1;
        PlaySoundW(L"C:\\Windows\\Media\\Windows Notify Calendar.wav", nullptr, SND_FILENAME | SND_ASYNC | SND_NODEFAULT);
    } else {
        tmState = 0; tmLeft = tmDur;
        PlaySoundW(L"C:\\Windows\\Media\\Alarm01.wav", nullptr, SND_FILENAME | SND_ASYNC | SND_LOOP | SND_NODEFAULT);
    }
    if (!visible) { visible = true; gVisibleA = true; ShowWindow(gHwnd, SW_SHOWNOACTIVATE); }
    if (!expanded) { collapsedTargets(); sw.v += 700; startAnim(); }  // saltito
}
static void dismissAlert() {
    if (!alertOn) return;
    alertOn = false; PlaySoundW(nullptr, nullptr, 0);
    if (!expanded) { collapsedTargets(); startAnim(); }
}
static void setCaffeine(bool on) {
    caffeine = on;
    SetThreadExecutionState(on ? (ES_CONTINUOUS | ES_SYSTEM_REQUIRED | ES_DISPLAY_REQUIRED) : ES_CONTINUOUS);
}
static void applySize() { updateMonitor(); ensureDib(); }

static void click(int id) {
    if (id == H_TAB0 || id == H_TAB1) { view = lastTab = id - H_TAB0; }
    else if (id == H_TAB2) { view = lastTab = V_SHELF; }
    else if (id == H_GEAR) { view = view == V_SET ? lastTab : V_SET; }
    else if (id == H_NEXTEV) { openCalendarDay(nextY, nextM, nextD); return; }
    else if (id == H_SHELF_CLEAR) { for (auto& it : shelf) SafeRelease(it.bmp); shelf.clear(); saveShelf(); }
    else if (id >= H_SHELF_DEL && id < H_SHELF_DEL + 30) shelfRemove(id - H_SHELF_DEL);
    else if (id >= H_SHELF && id < H_SHELF + 30) {
        size_t i = id - H_SHELF;
        if (i < shelf.size()) {
            if (GetFileAttributesW(shelf[i].path.c_str()) == INVALID_FILE_ATTRIBUTES) shelfRemove(i);
            else { ShellExecuteW(nullptr, L"open", shelf[i].path.c_str(), nullptr, nullptr, SW_SHOWNORMAL); setExpanded(false); return; }
        }
    }
    else if (id == H_PLAY) { mediaKey(VK_MEDIA_PLAY_PAUSE); if (media.has) media.playing = !media.playing; }
    else if (id == H_NEXT) mediaKey(VK_MEDIA_NEXT_TRACK);
    else if (id == H_PREV) mediaKey(VK_MEDIA_PREV_TRACK);
    else if (id == H_CPREV) { if (--calM < 1) { calM = 12; calY--; } }
    else if (id == H_CNEXT) { if (++calM > 12) { calM = 1; calY++; } }
    else if (id == H_CTITLE) { SYSTEMTIME st; GetLocalTime(&st); calY = st.wYear; calM = st.wMonth; }
    else if (id > H_DAY && id < H_DAY + 32) selDay = id - H_DAY;
    else if (id == H_CBACK) selDay = 0;
    else if (id == H_COPEN || (id >= H_EVT && id < H_EVT + 100)) { openCalendarDay(calY, calM, selDay); return; }
    else if (id >= H_APP && id < H_APP + (int)apps.size()) {
        App& a = apps[id - H_APP];
        ShellExecuteW(nullptr, L"open", a.target.c_str(), a.args.empty() ? nullptr : a.args.c_str(), nullptr, SW_SHOWNORMAL);
        setExpanded(false); return;
    }
    else if (id == H_TM_MODE || id == H_TM_MODE + 1) { dismissAlert(); setPomo(id == H_TM_MODE + 1); }
    else if (id == H_TM_PLAY) {
        dismissAlert();
        if (tmState == 1) tmPause();
        else {
            if (!pomo && tmState == 0) { tmDur = tmLeft = pickMs(); if (!tmDur) { render(); return; } }
            tmStart();
        }
    }
    else if (id == H_TM_RESET) { dismissAlert(); if (pomo) { pomoCount = 0; pomoArm(0); tmState = 0; } else { tmState = 0; tmDur = tmLeft = pickMs(); } }
    else if (id == H_TM_SKIP) {
        if (pomo) { if (pomoPhase == 0) { pomoCount++; pomoArm(1); } else pomoArm(0); if (tmState) { tmEnd = nowMs() + tmDur; tmState = 1; } }
    }
    else if (id == H_CLAUDE) { setExpanded(false); launchClaude(); return; }
    else if (id == H_SW_R) { if (swRun) { swAcc = swElapsed(); swRun = false; } else { swStart = nowMs(); swRun = true; } }
    else if (id == H_SW_L) { if (swRun) { laps.push_back(swElapsed()); if (laps.size() > 99) laps.erase(laps.begin()); } else { swAcc = 0; laps.clear(); } }
    else if (id == H_Q) setCaffeine(!caffeine);
    else if (id == H_Q + 1) { volInit(); if (vol) { BOOL m = FALSE; vol->GetMute(&m); vol->SetMute(!m, nullptr); } }
    else if (id == H_Q + 2) { setExpanded(false); ShellExecuteW(nullptr, L"open", L"ms-screenclip:", nullptr, nullptr, SW_SHOWNORMAL); return; }
    else if (id == H_Q + 3) { setExpanded(false); LockWorkStation(); return; }
    else if (id == H_SET) { cfg.autostart = !cfg.autostart; setAutostart(cfg.autostart); }
    else if (id == H_SET + 1) cfg.hoverOpen = !cfg.hoverOpen;
    else if (id == H_SET + 2) cfg.hideFull = !cfg.hideFull;
    else if (id == H_SET + 3) cfg.eq = !cfg.eq;
    else if (id == H_SET + 4) cfg.battery = !cfg.battery;
    else if (id == H_SET + 6) { cfg.discreetOn = !cfg.discreetOn; updateDiscreet(); }
    else if (id == H_SET + 5) cfg.alerts = !cfg.alerts;
    else if (id >= H_SEG_ALERT && id < H_SEG_ALERT + 3) cfg.alertMins = ALERTS[id - H_SEG_ALERT];
    else if (id >= H_SEG_SIZE && id < H_SEG_SIZE + 3) { cfg.size = id - H_SEG_SIZE; saveSettings(); applySize(); }
    else if (id >= H_SEG_OPA && id < H_SEG_OPA + 3) cfg.opacity = id - H_SEG_OPA;
    else if (id >= H_SEG_TMODE && id < H_SEG_TMODE + 3) { cfg.transMode = id - H_SEG_TMODE; if (cfg.transMode && cfg.opacity == 0) cfg.opacity = 1; }
    else if (id >= H_ACC && id < H_ACC + 6) cfg.accent = id - H_ACC;
    else if (id == H_EDIT_CAL) { ShellExecuteW(nullptr, L"open", L"notepad.exe", gCalFile.c_str(), nullptr, SW_SHOWNORMAL); setExpanded(false); return; }
    else if (id == H_EDIT_APPS) { ShellExecuteW(nullptr, L"open", L"notepad.exe", appsFile.c_str(), nullptr, SW_SHOWNORMAL); setExpanded(false); return; }
    else if (id == H_QUIT) { DestroyWindow(gHwnd); return; }
    if (id >= H_SET && id < H_ACC + 6) saveSettings();
    render();
}
static int hitAt(LPARAM lp) {
    float x = (short)LOWORD(lp) / scale, y = (short)HIWORD(lp) / scale;
    for (auto& h : hits) if (x >= h.r.left && x < h.r.right && y >= h.r.top && y < h.r.bottom) return h.id;
    return H_NONE;
}
static void dragMove(LPARAM lp) {
    float x = (short)LOWORD(lp) / scale, y = (short)HIWORD(lp) / scale;
    if (dragKind == 1 || dragKind == 2) {
        D2D1_RECT_F r = dragKind == 1 ? volRect : briRect;
        float f = clampf((x - r.left) / (r.right - r.left), 0, 1);
        if (dragKind == 1) { if (vol) { vol->SetMasterVolumeLevelScalar(f, nullptr); if (f > 0) vol->SetMute(FALSE, nullptr); } twSnap(11, f); }
        else { briSet((int)lroundf(f * 100)); twSnap(14, f); }
        render();
    } else if (dragKind == 3) {
        float dy = y - dragY0;
        if (fabsf(dy) > 3) dragMoved = true;
        float pos = dragPos0 - dy / 26.f;
        ULONGLONG n = nowMs(); float dt = std::max(1.f, (float)(n - dragLastT)) / 1000.f;
        float v = -(y - dragLastY) / 26.f / dt;
        dragVel = 0.6f * dragVel + 0.4f * v; dragLastY = y; dragLastT = n;
        pickT[dragCol] = pos; twSnap(700 + dragCol, pos);
        render();
    }
}
static void dragEnd(LPARAM lp) {
    if (dragKind == 3) {
        float y = (short)HIWORD(lp) / scale, cur = pickT[dragCol];
        if (!dragMoved) cur = roundf(cur) + (float)lroundf((y - pickCy) / 26.f);  // clic en un número de arriba o abajo
        else {
            if (nowMs() - dragLastT > 90) dragVel = 0;
            cur = roundf(cur + clampf(dragVel, -30, 30) * 0.15f);  // inercia
        }
        pickT[dragCol] = cur; updatePick();
    }
    dragKind = 0;
}
static void openFromPill() {
    if (alertOn) { dismissAlert(); setExpanded(true, 1); return; }
    int mode = pillMode();
    if (mode == PM_TIMER || mode == PM_SW) setExpanded(true, 1);
    else if (mode == PM_EVENT) {
        setExpanded(true, 0);
        SYSTEMTIME st; GetLocalTime(&st); selDay = st.wDay;
    } else setExpanded(true, lastTab);
}

// ---------------------------------------------------------------- arrastrar y soltar
static const GUID BHID_DataObject_ = {0xb8c0bd9f, 0xed24, 0x455c, {0x83, 0xe6, 0xd5, 0x39, 0x0c, 0x4f, 0xe8, 0xc4}};
// origen del arrastre: suelta al levantar el botón, cancela con Esc
struct DragSource : IDropSource {
    HRESULT STDMETHODCALLTYPE QueryInterface(REFIID r, void** pp) override {
        if (r == IID_IUnknown || r == IID_IDropSource) { *pp = this; return S_OK; }
        *pp = nullptr; return E_NOINTERFACE;
    }
    ULONG STDMETHODCALLTYPE AddRef() override { return 2; }
    ULONG STDMETHODCALLTYPE Release() override { return 1; }
    HRESULT STDMETHODCALLTYPE QueryContinueDrag(BOOL esc, DWORD ks) override {
        if (esc) return DRAGDROP_S_CANCEL;
        if (!(ks & MK_LBUTTON)) return DRAGDROP_S_DROP;
        return S_OK;
    }
    HRESULT STDMETHODCALLTYPE GiveFeedback(DWORD) override { return DRAGDROP_S_USEDEFAULTCURSORS; }
};
static DragSource dragSource;
// miniatura bajo el cursor mientras se arrastra
static void setDragImage(IDataObject* dob, const std::wstring& path) {
    IDragSourceHelper* dsh = nullptr;
    if (FAILED(CoCreateInstance(CLSID_DragDropHelper, nullptr, CLSCTX_INPROC_SERVER, IID_IDragSourceHelper, (void**)&dsh))) return;
    IShellItemImageFactory* f = nullptr; HBITMAP hb = nullptr;
    if (SUCCEEDED(SHCreateItemFromParsingName(path.c_str(), nullptr, IID_PPV_ARGS(&f)))) {
        SIZE sz{(LONG)lroundf(72 * scale), (LONG)lroundf(72 * scale)};
        f->GetImage(sz, SIIGBF_BIGGERSIZEOK, &hb); f->Release();
    }
    DIBSECTION ds{};
    if (hb && GetObjectW(hb, sizeof ds, &ds) && ds.dsBm.bmBits && ds.dsBm.bmBitsPixel == 32) {
        BYTE* b = (BYTE*)ds.dsBm.bmBits; size_t n = (size_t)ds.dsBm.bmWidth * ds.dsBm.bmHeight; bool any = false;
        for (size_t i = 0; i < n && !any; i++) if (b[i * 4 + 3]) any = true;
        if (!any) for (size_t i = 0; i < n; i++) b[i * 4 + 3] = 255;  // fotos sin alfa: hacerlas opacas
        SHDRAGIMAGE di{};
        di.sizeDragImage = {ds.dsBm.bmWidth, ds.dsBm.bmHeight};
        di.ptOffset = {ds.dsBm.bmWidth / 2, ds.dsBm.bmHeight / 2};
        di.hbmpDragImage = hb; di.crColorKey = CLR_NONE;
        if (FAILED(dsh->InitializeFromBitmap(&di, dob))) DeleteObject(hb);
    } else if (hb) DeleteObject(hb);
    dsh->Release();
}
static void shelfDragOut(size_t i) {
    if (i >= shelf.size()) return;
    std::wstring path = shelf[i].path;
    IShellItem* si = nullptr; IDataObject* dob = nullptr;
    if (SUCCEEDED(SHCreateItemFromParsingName(path.c_str(), nullptr, IID_PPV_ARGS(&si)))) { si->BindToHandler(nullptr, BHID_DataObject_, IID_IDataObject, (void**)&dob); si->Release(); }
    ReleaseCapture(); pressId = H_NONE;
    if (!dob) { shelfRemove(i); render(); return; }
    setDragImage(dob, path);
    draggingOut = true;
    DWORD eff = 0;
    // solo copiar o enlazar: al soltarlo en una carpeta se copia y el original no se mueve nunca
    DoDragDrop(dob, &dragSource, DROPEFFECT_COPY | DROPEFFECT_LINK, &eff);
    draggingOut = false; dob->Release();
    render();
}
static IDropTargetHelper* dropHelper = nullptr;
struct DropTarget : IDropTarget {
    bool ok = false;
    FORMATETC fe{CF_HDROP, nullptr, DVASPECT_CONTENT, -1, TYMED_HGLOBAL};
    HRESULT STDMETHODCALLTYPE QueryInterface(REFIID riid, void** pp) override {
        if (riid == IID_IUnknown || riid == IID_IDropTarget) { *pp = this; return S_OK; }
        *pp = nullptr; return E_NOINTERFACE;
    }
    ULONG STDMETHODCALLTYPE AddRef() override { return 2; }
    ULONG STDMETHODCALLTYPE Release() override { return 1; }
    HRESULT STDMETHODCALLTYPE DragEnter(IDataObject* d, DWORD, POINTL pt, DWORD* eff) override {
        ok = !draggingOut && d->QueryGetData(&fe) == S_OK;
        *eff = ok ? DROPEFFECT_COPY : DROPEFFECT_NONE;
        POINT p{pt.x, pt.y}; if (dropHelper) dropHelper->DragEnter(gHwnd, d, &p, *eff);
        if (ok) {
            dropHover = true; twSnap(15, 1.f); KillTimer(gHwnd, T_COLLAPSE);
            if (!expanded) { openedByDrag = true; setExpanded(true, V_SHELF); }
            else { view = lastTab = V_SHELF; render(); }
        }
        return S_OK;
    }
    HRESULT STDMETHODCALLTYPE DragOver(DWORD, POINTL pt, DWORD* eff) override {
        *eff = ok ? DROPEFFECT_COPY : DROPEFFECT_NONE;
        POINT p{pt.x, pt.y}; if (dropHelper) dropHelper->DragOver(&p, *eff);
        if (ok) KillTimer(gHwnd, T_COLLAPSE);
        return S_OK;
    }
    HRESULT STDMETHODCALLTYPE DragLeave() override {
        if (dropHelper) dropHelper->DragLeave();
        if (ok) { ok = false; dropHover = false; SetTimer(gHwnd, T_COLLAPSE, openedByDrag && shelf.empty() ? 350 : 900, nullptr); render(); }
        return S_OK;
    }
    HRESULT STDMETHODCALLTYPE Drop(IDataObject* d, DWORD, POINTL pt, DWORD* eff) override {
        POINT p{pt.x, pt.y};
        *eff = ok ? DROPEFFECT_COPY : DROPEFFECT_NONE;
        if (dropHelper) dropHelper->Drop(d, &p, *eff);
        STGMEDIUM stg{};
        if (ok && SUCCEEDED(d->GetData(&fe, &stg))) {
            HDROP hd = (HDROP)GlobalLock(stg.hGlobal);
            if (hd) {
                UINT n = DragQueryFileW(hd, 0xFFFFFFFF, nullptr, 0);
                for (UINT i = 0; i < n; i++) {
                    UINT len = DragQueryFileW(hd, i, nullptr, 0);
                    std::wstring f(len, 0); DragQueryFileW(hd, i, &f[0], len + 1);
                    shelfAdd(f);
                }
                GlobalUnlock(stg.hGlobal);
            }
            ReleaseStgMedium(&stg);
            saveShelf();
        }
        ok = false; dropHover = false; openedByDrag = false;
        SetTimer(gHwnd, T_COLLAPSE, 1500, nullptr);  // si no se mueve el ratón, se pliega sola
        render();
        return S_OK;
    }
};
static DropTarget dropTarget;

// ---------------------------------------------------------------- ventana
static const GUID GUID_BATT = {0xA7AD8041, 0xB45A, 0x4CAE, {0x87, 0xA3, 0xEE, 0xCB, 0xB4, 0x68, 0xA9, 0xE1}};
static const GUID GUID_ACDC = {0x5D3E9A59, 0xE9D5, 0x4B00, {0xA6, 0xBD, 0xFF, 0x34, 0xFF, 0x51, 0x65, 0x48}};

static LRESULT CALLBACK WndProc(HWND h, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_TIMER:
        if (wp == T_TICK) {
            ULONGLONG n = nowMs();
            if (eqActive()) eqTime += (n - lastTickMs) / 1000.0;
            lastTickMs = n;
            if (tmState == 1 && tmRemaining() == 0) finishTimer();
            if (alertOn && n - alertAt > (alertPomo ? 6000u : 30000u)) dismissAlert();
            // solo redibujar si cambia lo que se ve (el segundo del contador)
            static ULONGLONG lastShown = ~0ull;
            bool cont = alertOn || eqActive() || (expanded && view == 1 && (swRun || tmState == 1));
            ULONGLONG shown = (tmRemaining() + 999) / 1000 * 100003 + swElapsed() / 1000 + (expanded ? 7 : 0);
            if (!animating && (cont || shown != lastShown)) { lastShown = shown; render(); }
        } else if (wp == T_CLOCK) { scheduleClock(); if (!expanded) collapsedTargets(); if (!animating) render(); }
        else if (wp == T_POLL) {
            checkFullscreen();
            if (visible) ensureTopmost();
        } else if (wp == T_COLLAPSE) { KillTimer(h, T_COLLAPSE); setExpanded(false); }
        else if (wp == T_PEEK) peekTick();
        else if (wp == T_HOVER) { KillTimer(h, T_HOVER); if (hovered && !expanded) openFromPill(); }
        else if (wp == T_TRIM) { KillTimer(h, T_TRIM); if (!expanded) trimMemory(); }
        return 0;
    case WM_SETCURSOR:
        if (LOWORD(lp) == HTCLIENT) { SetCursor(LoadCursor(nullptr, (!expanded || hoverId) ? IDC_HAND : IDC_ARROW)); return TRUE; }
        break;
    case WM_MOUSEMOVE: {
        if (!hovered) {
            hovered = true;
            TRACKMOUSEEVENT t{sizeof t, TME_LEAVE, h, 0}; TrackMouseEvent(&t);
            if (!expanded) {
                collapsedTargets(); startAnim();
                if (cfg.hoverOpen && !alertOn) SetTimer(h, T_HOVER, 260, nullptr);
            }
            SetTimer(h, T_PEEK, 40, nullptr);  // vigila Ctrl solo mientras el ratón está encima
            {
            }
        }
        KillTimer(h, T_COLLAPSE);
        if (dragKind) { dragMove(lp); return 0; }
        if (pressId >= H_SHELF && pressId < H_SHELF + 30 && GetCapture() == h) {
            float mx = (short)LOWORD(lp) / scale, my = (short)HIWORD(lp) / scale;
            if (fabsf(mx - pressX) + fabsf(my - pressY) > 6) { shelfDragOut(pressId - H_SHELF); return 0; }
        }
        int id = expanded ? hitAt(lp) : H_NONE;
        if (id != hoverId) { hoverId = id; if (!animating) render(); }
        return 0;
    }
    case WM_MOUSELEAVE:
        if (peeking) return 0;  // al ver a través el ratón "sale"; lo gestiona peekTick
        hovered = false; hoverId = H_NONE; KillTimer(h, T_HOVER);
        if (expanded) SetTimer(h, T_COLLAPSE, 450, nullptr);
        else collapsedTargets();
        if (!animating) render();
        return 0;
    case WM_LBUTTONDOWN:
        pressId = expanded ? hitAt(lp) : H_NONE;
        pressX = (short)LOWORD(lp) / scale; pressY = (short)HIWORD(lp) / scale;
        SetCapture(h);
        if (pressId == H_VOL || pressId == H_BRI) { dragKind = pressId == H_VOL ? 1 : 2; dragMove(lp); }
        else if (pressId >= H_PICK && pressId < H_PICK + 3 && !pomo && tmState == 0) {
            dragKind = 3; dragCol = pressId - H_PICK; dragMoved = false; dragVel = 0;
            dragY0 = dragLastY = (short)HIWORD(lp) / scale; dragLastT = nowMs();
            dragPos0 = tw(700 + dragCol, pickT[dragCol], 14);
            pickT[dragCol] = dragPos0; twSnap(700 + dragCol, dragPos0);
        }
        else if (!animating) render();
        return 0;
    case WM_LBUTTONUP: {
        ReleaseCapture();
        if (dragKind) { dragEnd(lp); pressId = H_NONE; render(); return 0; }
        int id = expanded ? hitAt(lp) : H_NONE, was = pressId;
        pressId = H_NONE;
        if (!expanded) openFromPill();
        else if (id && id == was) click(id);
        else if (!animating) render();
        return 0;
    }
    case WM_MOUSEWHEEL: {
        if (!expanded) break;
        POINT pt{(short)LOWORD(lp), (short)HIWORD(lp)}; ScreenToClient(h, &pt);
        LPARAM cl = MAKELPARAM(pt.x, pt.y);
        int id = hitAt(cl), d = GET_WHEEL_DELTA_WPARAM(wp) > 0 ? -1 : 1;
        if (id >= H_PICK && id < H_PICK + 3 && !pomo && tmState == 0) {
            int c = id - H_PICK; auto it = tweens.find(700 + c);
            pickT[c] = roundf(it != tweens.end() ? it->second.t : pickT[c]) + d; updatePick();
        } else if (id == H_VOL && vol) {
            float v = clampf(volGet(nullptr) - d * 0.05f, 0, 1); vol->SetMasterVolumeLevelScalar(v, nullptr); if (v > 0) vol->SetMute(FALSE, nullptr);
        } else if (id == H_BRI && briCur >= 0) briSet(briCur - d * 5);
        render();
        return 0;
    }
    case WM_RBUTTONUP: if (!expanded) setExpanded(true, V_SET); else { view = V_SET; render(); } return 0;
    case WM_MOUSEACTIVATE: return MA_NOACTIVATE;
    case WM_APP_MEDIA: {
        { std::lock_guard<std::mutex> lk(gMx); media.has = gMediaShared.has; media.playing = gMediaShared.playing; media.title = gMediaShared.title;
          media.artist = gMediaShared.artist; media.app = gMediaShared.app; media.accent = gMediaShared.accent;
          if (gMediaShared.artVer != artVerUI) {
              artVerUI = gMediaShared.artVer; SafeRelease(artBmp); SafeRelease(artSBmp);
              D2D1_BITMAP_PROPERTIES bp = D2D1::BitmapProperties(D2D1::PixelFormat(DXGI_FORMAT_B8G8R8A8_UNORM, D2D1_ALPHA_MODE_PREMULTIPLIED));
              if (!gMediaShared.art.empty()) rt->CreateBitmap(D2D1::SizeU(gMediaShared.artPx, gMediaShared.artPx), gMediaShared.art.data(), gMediaShared.artPx * 4, &bp, &artBmp);
              if (!gMediaShared.artSmall.empty()) rt->CreateBitmap(D2D1::SizeU(gMediaShared.artSPx, gMediaShared.artSPx), gMediaShared.artSmall.data(), gMediaShared.artSPx * 4, &bp, &artSBmp);
          } }
        if (!expanded) collapsedTargets();
        if (!animating) render();
        return 0;
    }
    case WM_APP_CAL:
        { std::lock_guard<std::mutex> lk(gMx); events.swap(gEventsShared); std::vector<CalEvent>().swap(gEventsShared); }
        if (!expanded) collapsedTargets();
        if (!animating) render();
        return 0;
    case WM_APP_STATS:
        { std::lock_guard<std::mutex> lk(gMx); stats = gStatsShared; }
        if (expanded && !animating) render();
        return 0;
    case WM_POWERBROADCAST:
        if (wp == PBT_APMRESUMEAUTOMATIC || wp == PBT_APMRESUMESUSPEND) { scheduleClock(); SetEvent(gWake); }
        if (!animating) render();
        return TRUE;
    case WM_TIMECHANGE: scheduleClock(); if (!animating) render(); return 0;
    case WM_DISPLAYCHANGE: case WM_DPICHANGED: case WM_SETTINGCHANGE:
        if (msg == WM_DISPLAYCHANGE) gFlushes = 0;  // otra pantalla u otra frecuencia: recalcular
        updateMonitor(); render(); return 0;
    case WM_DESTROY:
        PlaySoundW(nullptr, nullptr, 0); setCaffeine(false); briStop(); RevokeDragDrop(h);
        PostQuitMessage(0); return 0;
    }
    return DefWindowProcW(h, msg, wp, lp);
}

// Si islita se arrancó desde una terminal de Claude Code, hereda sus variables (NO_COLOR, CLAUDECODE...)
// y el Claude que abre el botón saldría sin colores y creyéndose una sesión hija: se quitan.
static void cleanInheritedEnv() {
    if (!GetEnvironmentVariableW(L"CLAUDECODE", nullptr, 0)) return;
    std::vector<std::wstring> names;
    if (wchar_t* env = GetEnvironmentStringsW()) {
        for (wchar_t* p = env; *p; p += wcslen(p) + 1) {
            std::wstring kv = p; size_t eq = kv.find(L'=', 1);
            if (eq != std::wstring::npos && _wcsnicmp(kv.c_str(), L"CLAUDE", 6) == 0) names.push_back(kv.substr(0, eq));
        }
        FreeEnvironmentStringsW(env);
    }
    names.push_back(L"NO_COLOR"); names.push_back(L"GIT_TERMINAL_PROMPT");
    for (auto& n : names) SetEnvironmentVariableW(n.c_str(), nullptr);
}

int WINAPI wWinMain(HINSTANCE hi, HINSTANCE, LPWSTR, int) {
    HANDLE mx = CreateMutexW(nullptr, TRUE, L"Local\\islita");
    if (GetLastError() == ERROR_ALREADY_EXISTS) return 0;
    cleanInheritedEnv();
    SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2);
    SetPriorityClass(GetCurrentProcess(), BELOW_NORMAL_PRIORITY_CLASS);
    setLowMemoryPriority();
    OleInitialize(nullptr);
    QueryPerformanceFrequency(&qpf);

    wchar_t ad[MAX_PATH]; GetEnvironmentVariableW(L"APPDATA", ad, MAX_PATH);
    migrateFromIsla(ad);
    cfgDir = std::wstring(ad) + L"\\islita"; CreateDirectoryW(cfgDir.c_str(), nullptr);
    gCfgDir = cfgDir; gCalFile = cfgDir + L"\\calendarios.txt";
    appsFile = cfgDir + L"\\atajos.txt";
    shelfFile = cfgDir + L"\\bandeja.txt";
    if (!regGet(L"Configurado", 0)) { setAutostart(true); regSet(L"Configurado", 1); }
    loadSettings();
    loadApps();
    loadShelf();

    createResources();
    WNDCLASSW wc{}; wc.lpfnWndProc = WndProc; wc.hInstance = hi; wc.lpszClassName = L"islita"; wc.hIcon = LoadIconW(hi, MAKEINTRESOURCEW(1)); wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
    RegisterClassW(&wc);
    gHwnd = CreateWindowExW(WS_EX_LAYERED | WS_EX_TOPMOST | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE, wc.lpszClassName, L"islita", WS_POPUP,
                            0, 0, 10, 10, nullptr, nullptr, hi, nullptr);
    updateMonitor();
    // entrada: la píldora aparece desde un punto
    sw.x = 40; sh.x = 20; sr.x = 10; collapsedTargets();
    render();
    ShowWindow(gHwnd, SW_SHOWNOACTIVATE);
    startAnim();

    CoCreateInstance(CLSID_DragDropHelper, nullptr, CLSCTX_INPROC_SERVER, IID_IDropTargetHelper, (void**)&dropHelper);
    RegisterDragDrop(gHwnd, &dropTarget);
    RegisterPowerSettingNotification(gHwnd, &GUID_BATT, DEVICE_NOTIFY_WINDOW_HANDLE);
    RegisterPowerSettingNotification(gHwnd, &GUID_ACDC, DEVICE_NOTIFY_WINDOW_HANDLE);
    SetWinEventHook(EVENT_SYSTEM_FOREGROUND, EVENT_SYSTEM_FOREGROUND, nullptr, winEvent, 0, 0, WINEVENT_OUTOFCONTEXT | WINEVENT_SKIPOWNPROCESS);
    scheduleClock();
    SetCoalescableTimer(gHwnd, T_POLL, 1500, nullptr, 600);

    gWake = CreateEventW(nullptr, FALSE, FALSE, nullptr);
    std::thread worker(bg::run);

    // bucle: en reposo duerme en GetMessage; animando, un fotograma por refresco de pantalla (DwmFlush)
    MSG m;
    for (;;) {
        if (animating) {
            bool quit = false;
            while (PeekMessageW(&m, nullptr, 0, 0, PM_REMOVE)) {
                if (m.message == WM_QUIT) { quit = true; break; }
                TranslateMessage(&m); DispatchMessageW(&m);
            }
            if (quit) break;
            if (animating) {
                LARGE_INTEGER a, b; QueryPerformanceCounter(&a);
                frame();
                // a ~60-75 fotogramas por segundo aunque la pantalla vaya a 120/144 Hz: igual de fluido y la mitad de CPU
                int& flushes = gFlushes;
                if (!flushes) {
                    DWM_TIMING_INFO ti{}; ti.cbSize = sizeof ti;
                    double hz = SUCCEEDED(DwmGetCompositionTimingInfo(nullptr, &ti)) && ti.rateRefresh.uiDenominator ? (double)ti.rateRefresh.uiNumerator / ti.rateRefresh.uiDenominator : 60;
                    flushes = std::max(1, (int)lround(hz / 75.0));
                }
                for (int i = 0; i < flushes; i++) if (FAILED(DwmFlush())) { Sleep(8); break; }
                QueryPerformanceCounter(&b);
                if ((b.QuadPart - a.QuadPart) * 1000 / qpf.QuadPart < 3) Sleep(4);
            }
        } else {
            BOOL r = GetMessageW(&m, nullptr, 0, 0);
            if (r <= 0) break;
            TranslateMessage(&m); DispatchMessageW(&m);
        }
    }
    gQuit = true; SetEvent(gWake); worker.join();
    ReleaseMutex(mx);
    return 0;
}
