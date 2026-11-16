// islita: isla dinámica para Windows, estilo Apple.
// Win32 + Direct2D (render por software) + ventana por capas. Sin frameworks.
#ifndef UNICODE
#define UNICODE
#endif
#define _WIN32_WINNT 0x0A00
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <winsock2.h>
#include <ws2ipdef.h>
#include <iphlpapi.h>
#include <netioapi.h>
#include <wlanapi.h>
#include <setupapi.h>
#include <bluetoothapis.h>
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
#include <propsys.h>
#include <propvarutil.h>

// ---------------------------------------------------------------- constantes
static const float EW = 720, EH = 264, ER = 40;   // panel abierto
static const float CH = 34;                       // alto de la píldora
static const float CW_IDLE = 276, CW_PLAY = 304, CW_EVENT = 340;  // ancho de la píldora
static const float TOPGAP = 6;                    // separación con el borde superior
static const float M = 18;                        // margen para la sombra

enum { T_TICK = 1, T_CLOCK, T_POLL, T_COLLAPSE, T_TRIM, T_HOVER, T_PEEK, T_CARET, T_TILES, T_BTLIST, T_PREVIEW, T_EVSHOW };
enum { WM_APP_MEDIA = WM_APP + 1, WM_APP_STATS, WM_APP_CAL, WM_APP_APPS, WM_APP_NET, WM_APP_VOL, WM_APP_VOLDEV, WM_APP_TESTCHARGE, WM_APP_TRAY, WM_APP_BTLIST, WM_APP_RADIO };  // TESTCHARGE: ver la animación de carga sin desenchufar
enum { H_NONE = 0, H_PREV, H_PLAY, H_NEXT, H_CPREV, H_CNEXT, H_CTITLE, H_CBACK, H_COPEN,
       H_TAB0 = 10, H_TAB1, H_GEAR, H_TM_PLAY, H_TM_RESET, H_TM_ADD, H_SW_L, H_SW_R, H_VOL, H_EDIT_CAL, H_EDIT_APPS, H_QUIT, H_TM_SKIP, H_BRI, H_CLAUDE, H_NEXTEV, H_SHELF_CLEAR, H_TRAYBTN, H_DEV_BTN, H_DEV_BACK, H_NET_BTN, H_BT_BTN, H_NET_MORE, H_BT_MORE, H_NET_DISC, H_NET_TOG, H_BT_TOG,
       H_DAY = 100, H_APP = 200, H_EVT = 300, H_TM_PRE = 400, H_Q = 420, H_SET = 440, H_SEG_ALERT = 460, H_SEG_SIZE = 470, H_SEG_OPA = 475, H_ACC = 480, H_SEG_TMODE = 486, H_PICK = 490, H_TM_MODE = 495, H_TAB2 = 499, H_SHELF = 600, H_SHELF_DEL = 650,
       H_WIN = 730, H_APP_ADD = 731, H_SRCH = 740, H_SRCH_RES = 750, H_SRCH_PIN = 760, H_APPS_CARD = 789, H_APP_PAGE = 790, H_CTX_BG = 800, H_CTX = 801, H_TRAY = 900, H_DEV = 950, H_NET = 1000, H_BT = 1030, H_FOLD_BG = 1100, H_FOLD = 1101 };

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
static HWND gHwnd, dockHwnd;  // la isla y el dock
static void dockAppsChanged(); static void dockRefreshSoon(UINT ms); static void dockOnForeground(); static void dockDropBitmaps(); static void dockKick();
static bool dAnim = false;  // el dock está animándose
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
// GPU por D3DKMT (gdi32), como el Administrador de tareas: < 1 MB, frente a los ~19 MB que dejaba nvml.dll
namespace kmt {
typedef UINT HND;
struct AdapterInfo { HND hAdapter; LUID luid; ULONG sources; BOOL precise; };
struct EnumAdapters2 { ULONG n; AdapterInfo* p; };
struct QueryInfo { HND hAdapter; int type; void* data; UINT size; };
struct PerfData { UINT32 phys; ULONGLONG memFreq, maxMemFreq, maxMemFreqOC, memBw, pcieBw; ULONG fanRPM, power, temperature; UCHAR pso; };
struct RegInfo { WCHAR adapter[MAX_PATH], bios[MAX_PATH], dac[MAX_PATH], chip[MAX_PATH]; };
struct CloseAdapter { HND hAdapter; };
typedef LONG(WINAPI* fnEnum2)(EnumAdapters2*);
typedef LONG(WINAPI* fnQAI)(QueryInfo*);
typedef LONG(WINAPI* fnQS)(void*);
typedef LONG(WINAPI* fnClose)(CloseAdapter*);
static fnQAI qai; static fnQS qs; static fnClose closeA;
static bool ok = false; static HND hGpu = 0; static LUID luid{}; static ULONG nodes = 0;
static std::vector<ULONGLONG> lastRun; static ULONGLONG lastAt = 0;
// D3DKMT_QUERYSTATISTICS: tipo (0 adaptador, 5 nodo) en 0, LUID en 4, resultado en 24, NodeId en 800
static bool stats(int type, ULONG node, BYTE (&b)[1024]) {
    memset(b, 0, sizeof b); *(int*)b = type; memcpy(b + 4, &luid, 8); *(ULONG*)(b + 800) = node;
    return qs(b) == 0;
}
static void open() {
    HMODULE g = GetModuleHandleW(L"gdi32.dll");
    auto en = (fnEnum2)GetProcAddress(g, "D3DKMTEnumAdapters2");
    qai = (fnQAI)GetProcAddress(g, "D3DKMTQueryAdapterInfo"); qs = (fnQS)GetProcAddress(g, "D3DKMTQueryStatistics");
    closeA = (fnClose)GetProcAddress(g, "D3DKMTCloseAdapter");
    if (!en || !qai || !qs) return;
    AdapterInfo ad[16]; EnumAdapters2 e{16, ad};
    if (en(&e) != 0) return;
    int best = 0;
    for (ULONG i = 0; i < e.n && i < 16; i++) {  // la gráfica dedicada: NVIDIA > AMD/Intel con sensor
        RegInfo ri{}; QueryInfo q{ad[i].hAdapter, 8 /*registro*/, &ri, sizeof ri};
        PerfData pd{}; QueryInfo q2{ad[i].hAdapter, 62 /*perf*/, &pd, sizeof pd};
        if (qai(&q) != 0 || qai(&q2) != 0) continue;
        int sc = wcsstr(ri.adapter, L"NVIDIA") ? 3 : (wcsstr(ri.adapter, L" RX") || wcsstr(ri.adapter, L"Arc")) ? 2 : 1;
        if (sc > best) { best = sc; hGpu = ad[i].hAdapter; luid = ad[i].luid; }
    }
    for (ULONG i = 0; i < e.n && i < 16; i++) if (closeA && ad[i].hAdapter != hGpu) { CloseAdapter c{ad[i].hAdapter}; closeA(&c); }
    if (!best) return;
    BYTE b[1024];
    nodes = stats(0, 0, b) ? std::min<ULONG>(*(ULONG*)(b + 28), 64) : 0;
    lastRun.assign(nodes, 0); lastAt = 0; ok = true;
}
static void close() { if (ok && closeA) { CloseAdapter c{hGpu}; closeA(&c); } ok = false; hGpu = 0; nodes = 0; lastRun.clear(); }
static void poll(float& temp, float& use) {
    if (!ok) return;
    PerfData pd{}; QueryInfo q{hGpu, 62, &pd, sizeof pd};
    if (qai(&q) == 0 && pd.temperature > 0) temp = pd.temperature / 10.f;  // 0 = gráfica dormida
    // uso = el motor más ocupado (tiempo de ejecución en unidades de 100 ns)
    ULONGLONG now = GetTickCount64() * 10000, busiest = 0; BYTE b[1024];
    for (ULONG n = 0; n < nodes; n++) {
        if (!stats(5, n, b)) continue;
        ULONGLONG r = *(ULONGLONG*)(b + 24);
        if (lastAt && r >= lastRun[n]) busiest = std::max(busiest, r - lastRun[n]);
        lastRun[n] = r;
    }
    if (lastAt && now > lastAt) use = std::min(100.f, 100.f * (float)busiest / (float)(now - lastAt));
    lastAt = now;
}
}
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
    kmt::open();
    FILETIME i, k, u; GetSystemTimes(&i, &k, &u); lastIdle = ft(i); lastTotal = ft(k) + ft(u);
}
static void closeSensors() {
    if (!sensorsOpen) return;
    sensorsOpen = false;
    if (pq) { PdhCloseQuery(pq); pq = nullptr; pc = nullptr; }
    kmt::close();
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
    kmt::poll(s.gpuT, s.gpuU);
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
static IDWriteTextFormat *fTime, *fSmall, *fTitle, *fBody, *fCalHead, *fCal, *fCalB, *fRing, *fTiny, *fApp, *fGlyph, *fIcon, *fIconL, *fBig, *fMid, *fTab, *fSearch;

static HDC memDC; static HBITMAP dib, oldBmp; static int dibW = 0, dibH = 0;
static float scale = 1; static UINT dpi = 96;
static RECT mon;

static MediaInfo media;            // copia de la UI
static StatsInfo stats;
static ID2D1Bitmap *artBmp, *artSBmp; static unsigned artVerUI = ~0u;

struct App { std::wstring name, target, icon, args; ID2D1Bitmap* bmp = nullptr; bool resolved = false; std::wstring mExe, mExe2, mAumid; };  // m*: para reconocerla abierta
static const float ICON_DIP = 76;  // los iconos se cargan a este tamaño (el dock los agranda al pasar el ratón)
static std::vector<App> apps; static bool iconsLoaded = false; static FILETIME appsStamp{};
static const int MAX_APPS = 36;
static std::wstring cfgDir, appsFile;
// buscador de aplicaciones (botón con el logo de Windows): solo vive mientras está abierto
struct SApp { std::wstring name, id, key, ini, path; };  // id = nombre de análisis en shell:AppsFolder; path = programa al que apunta (si se sabe)
static std::vector<SApp> gAppsShared, sApps; static std::vector<int> sRes;
static std::wstring sQ, sMsg; static ULONGLONG sMsgAt = 0;
static bool sActive = false, sLoaded = false, sCaret = true; static int sSel = 0, sScroll = 0; static unsigned sGen = 0;
static HWND sPrevFg = nullptr;
static std::map<std::wstring, ID2D1Bitmap*> sIcons;
static void freeSearchIcons() { for (auto& p : sIcons) if (p.second) p.second->Release(); sIcons.clear(); }

static std::vector<CalEvent> events;  // copia de la UI
static int selDay = 0;                // 0 = vista de mes; si no, día abierto en la agenda

// ---------------------------------------------------------------- ajustes
struct Settings { bool hideTaskbar = false, discreetOn = true, hoverOpen = false, hideFull = true, eq = true, battery = true, alerts = true, autostart = true; int alertMins = 60, size = 1, accent = 0, opacity = 1, transMode = 0; };  // transMode: 0 siempre, 1 con el ratón, 2 sin el ratón
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
// rayo al enchufar el cargador (unos segundos en la píldora)
static bool chargeOn = false; static ULONGLONG chargeAt = 0; static int lastAC = -1;
static const ULONGLONG CHARGE_MS = 3200;
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
enum { V_HOME, V_TOOLS, V_SHELF, V_SET, V_SEARCH, V_TRAY };
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
static float easeOutBack(float t) { t = clampf(t, 0, 1) - 1; return 1 + 2.70158f * t * t * t + 1.70158f * t * t; }
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
    cfg.hideTaskbar = regGet(L"OcultarBarra", 0);
}
static void saveSettings() {
    regSet(L"ModoDiscreto", cfg.discreetOn); regSet(L"AbrirAlPasar", cfg.hoverOpen); regSet(L"OcultarPantallaCompleta", cfg.hideFull); regSet(L"Ecualizador", cfg.eq);
    regSet(L"Bateria", cfg.battery); regSet(L"Avisos", cfg.alerts); regSet(L"AvisoMin", cfg.alertMins);
    regSet(L"Tamano", cfg.size); regSet(L"Acento", cfg.accent); regSet(L"Opacidad", cfg.opacity); regSet(L"TransparenteCuando", cfg.transMode);
    regSet(L"OcultarBarra", cfg.hideTaskbar);
}


// ---------------------------------------------------------------- ocultar la barra de tareas de Windows
// Se pone en "ocultar automáticamente" (así las ventanas maximizadas usan toda la pantalla) y además se esconde.
// Al desactivarlo o cerrar islita vuelve tal y como estaba.
static UINT WM_TASKBARCREATED = 0;
static HWINEVENTHOOK trayHook = nullptr;
static bool isTray(HWND h) {
    wchar_t c[32]; if (!GetClassNameW(h, c, 32)) return false;
    return !wcscmp(c, L"Shell_TrayWnd") || !wcscmp(c, L"Shell_SecondaryTrayWnd");
}
static HWND realTray() {
    for (HWND h = nullptr; (h = FindWindowExW(nullptr, h, L"Shell_TrayWnd", nullptr));) {
        DWORD p = 0; GetWindowThreadProcessId(h, &p);
        if (p != GetCurrentProcessId()) return h;
    }
    return nullptr;
}
static void showTrays(bool show) {
    HWND t = realTray();
    if (t && (IsWindowVisible(t) != 0) != show) ShowWindow(t, show ? SW_SHOWNA : SW_HIDE);
    for (HWND s2 = nullptr; (s2 = FindWindowExW(nullptr, s2, L"Shell_SecondaryTrayWnd", nullptr));)
        if ((IsWindowVisible(s2) != 0) != show) ShowWindow(s2, show ? SW_SHOWNA : SW_HIDE);
}
static void CALLBACK trayShown(HWINEVENTHOOK, DWORD, HWND h, LONG obj, LONG, DWORD, DWORD) {
    if (obj == OBJID_WINDOW && cfg.hideTaskbar && h && isTray(h)) ShowWindow(h, SW_HIDE);  // Windows la ha vuelto a enseñar
}
static void setAutoHide(bool on) {
    APPBARDATA ab{sizeof ab}; ab.hWnd = realTray();
    if (!ab.hWnd) return;
    UINT st = (UINT)SHAppBarMessage(ABM_GETSTATE, &ab);
    if (((st & ABS_AUTOHIDE) != 0) == on) return;
    ab.lParam = on ? (st | ABS_AUTOHIDE) : (st & ~ABS_AUTOHIDE);
    SHAppBarMessage(ABM_SETSTATE, &ab);
}
static void applyTaskbar() {
    HWND t = realTray();
    if (trayHook) { UnhookWinEvent(trayHook); trayHook = nullptr; }
    if (cfg.hideTaskbar) {
        if (!t) return;
        if (regGet(L"BarraAutoAntes", 99) == 99) {  // recordar cómo estaba para dejarla igual
            APPBARDATA ab{sizeof ab}; ab.hWnd = t;
            regSet(L"BarraAutoAntes", (SHAppBarMessage(ABM_GETSTATE, &ab) & ABS_AUTOHIDE) ? 1 : 0);
        }
        setAutoHide(true);
        showTrays(false);
        DWORD pid = 0; GetWindowThreadProcessId(t, &pid);
        trayHook = SetWinEventHook(EVENT_OBJECT_SHOW, EVENT_OBJECT_SHOW, nullptr, trayShown, pid, 0, WINEVENT_OUTOFCONTEXT);
    } else {
        showTrays(true);
        DWORD before = regGet(L"BarraAutoAntes", 99);
        if (before != 99) { setAutoHide(before == 1); regSet(L"BarraAutoAntes", 99); }
    }
}
static void restoreTaskbarOnExit() {  // sin cambiar el ajuste: al volver a abrir islita se oculta otra vez
    if (!cfg.hideTaskbar) return;
    bool keep = cfg.hideTaskbar; cfg.hideTaskbar = false; applyTaskbar(); cfg.hideTaskbar = keep;
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
        "# Atajos de la isla: hasta 36 líneas (6 por página) con el formato\n"
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
    while (p < w.size() && (int)apps.size() < MAX_APPS) {
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
static ID2D1Bitmap* thumbFor(const std::wstring& path, UINT px, int flags = SIIGBF_BIGGERSIZEOK);
static void loadIcons() {
    if (iconsLoaded) return;
    iconsLoaded = true;
    UINT px = (UINT)lroundf(ICON_DIP * scale);
    for (auto& a : apps) {
        std::wstring src = a.icon.empty() ? a.target : a.icon;
        if (!_wcsnicmp(src.c_str(), L"shell:", 6)) { a.bmp = thumbFor(src, px, SIIGBF_ICONONLY | SIIGBF_BIGGERSIZEOK); continue; }  // apps del menú Inicio
        if (src.find(L'\\') == std::wstring::npos) { wchar_t full[MAX_PATH]; if (SearchPathW(nullptr, src.c_str(), nullptr, MAX_PATH, full, nullptr)) src = full; }
        if (GetFileAttributesW(src.c_str()) == INVALID_FILE_ATTRIBUTES) continue;
        HICON h = iconFor(src, SHIL_JUMBO);
        if (h) { a.bmp = bitmapFromIcon(h, px, true); DestroyIcon(h); }
        if (!a.bmp && (h = iconFor(src, SHIL_EXTRALARGE))) { a.bmp = bitmapFromIcon(h, px, false); DestroyIcon(h); }
    }
}


// ---------------------------------------------------------------- apps abiertas (como la barra de tareas) delante de los atajos
struct RunApp { std::wstring key, exe, aumid; std::vector<HWND> wins; };
struct Tile { int pin = -1, run = -1; };  // índice en apps (atajo) y/o en running (abierta)
static std::vector<RunApp> running; static std::vector<std::wstring> runOrder; static std::vector<Tile> tiles; static int nPinnedTiles = 0;
static std::map<std::wstring, ID2D1Bitmap*> runIcons; static std::map<std::wstring, std::wstring> runNames;
static HWND fgAtOpen = nullptr;
static std::map<HWND, unsigned> winSeq; static unsigned winSeqN = 0;  // orden de llegada de cada ventana: numeración estable en la carpeta
static const int MAX_TILES = 59;
static const PROPERTYKEY PKEY_AUMID_ = {{0x9F4C2855, 0x9F79, 0x4B39, {0xA8, 0xD0, 0xE1, 0xD4, 0x2D, 0xE1, 0xD5, 0xF3}}, 5};
static const PROPERTYKEY PKEY_LinkTarget_ = {{0xB9B4B3FC, 0x2B51, 0x4A42, {0xB5, 0xD8, 0x32, 0x41, 0x46, 0xAF, 0xCF, 0x25}}, 2};
static void freeRunIcons() { for (auto& p : runIcons) if (p.second) p.second->Release(); runIcons.clear(); }
static std::wstring lowerW(std::wstring s) { if (!s.empty()) CharLowerBuffW(&s[0], (DWORD)s.size()); return s; }
static bool endsWithI(const std::wstring& s, const wchar_t* e) { size_t n = wcslen(e); return s.size() >= n && !_wcsicmp(s.c_str() + s.size() - n, e); }
static std::wstring exeOfPid(DWORD pid) {
    HANDLE h = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
    if (!h) return L"";
    wchar_t b[MAX_PATH * 2]; DWORD n = MAX_PATH * 2; std::wstring r;
    if (QueryFullProcessImageNameW(h, 0, b, &n)) r.assign(b, n);
    CloseHandle(h); return r;
}
// identificador de app de un proceso empaquetado (solo si su programa está dentro de WindowsApps)
static std::wstring aumidOfPid(DWORD pid, const std::wstring& exe) {
    if (exe.empty() || !wcsstr(lowerW(exe).c_str(), L"\\windowsapps\\")) return L"";
    typedef LONG(WINAPI* GAUMI)(HANDLE, UINT32*, PWSTR);
    static GAUMI f = (GAUMI)GetProcAddress(GetModuleHandleW(L"kernel32.dll"), "GetApplicationUserModelId");
    if (!f) return L"";
    HANDLE ph = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, pid);
    if (!ph) return L"";
    wchar_t b[256]; UINT32 n = 256; std::wstring r;
    if (f(ph, &n, b) == ERROR_SUCCESS) r = b;
    CloseHandle(ph); return r;
}
static std::wstring aumidOf(HWND h) {
    std::wstring r; IPropertyStore* ps = nullptr;
    if (SUCCEEDED(SHGetPropertyStoreForWindow(h, IID_PPV_ARGS(&ps))) && ps) {
        PROPVARIANT v; PropVariantInit(&v);
        if (SUCCEEDED(ps->GetValue(PKEY_AUMID_, &v)) && v.vt == VT_LPWSTR && v.pwszVal) r = v.pwszVal;
        PropVariantClear(&v); ps->Release();
    }
    return r;
}
// ventanas que saldrían en la barra de tareas
static bool isTaskWindow(HWND h) {
    if (h == gHwnd || !IsWindowVisible(h)) return false;
    LONG_PTR ex = GetWindowLongPtrW(h, GWL_EXSTYLE);
    if (!(ex & WS_EX_APPWINDOW) && (GetWindow(h, GW_OWNER) || (ex & (WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE)))) return false;
    int cloaked = 0; DwmGetWindowAttribute(h, DWMWA_CLOAKED, &cloaked, sizeof cloaked);
    if (cloaked || GetWindowTextLengthW(h) == 0) return false;
    wchar_t c[64]; GetClassNameW(h, c, 64);
    return wcscmp(c, L"Progman") && wcscmp(c, L"WorkerW") && !isTray(h);
}
static BOOL CALLBACK enumTaskWin(HWND h, LPARAM lp) { if (isTaskWindow(h)) ((std::vector<HWND>*)lp)->push_back(h); return TRUE; }
struct ChildPid { DWORD frame, found; };
static BOOL CALLBACK enumUwpChild(HWND h, LPARAM lp) {
    auto* c = (ChildPid*)lp; DWORD pid = 0; GetWindowThreadProcessId(h, &pid);
    if (pid && pid != c->frame) { c->found = pid; return FALSE; }
    return TRUE;
}
static void refreshRunning() {
    std::vector<HWND> ws; EnumWindows(enumTaskWin, (LPARAM)&ws);
    for (auto it = winSeq.begin(); it != winSeq.end();) { if (IsWindow(it->first)) ++it; else it = winSeq.erase(it); }
    for (auto it = ws.rbegin(); it != ws.rend(); ++it) if (!winSeq.count(*it)) winSeq[*it] = ++winSeqN;  // las de atrás primero
    std::map<std::wstring, RunApp> m; std::vector<std::wstring> seen;
    for (HWND h : ws) {
        DWORD pid = 0; GetWindowThreadProcessId(h, &pid);
        std::wstring exe = exeOfPid(pid);
        if (endsWithI(exe, L"\\ApplicationFrameHost.exe")) {  // apps de la Store: el proceso de verdad es el de dentro
            ChildPid c{pid, 0}; EnumChildWindows(h, enumUwpChild, (LPARAM)&c);
            if (c.found) exe = exeOfPid(c.found);
        }
        std::wstring au = aumidOf(h);
        if (au.empty()) au = aumidOfPid(pid, exe);  // apps de la Tienda que no lo ponen en la ventana (p. ej. Terminal)
        if (exe.empty() && au.empty()) continue;
        std::wstring key = au.empty() ? L"e:" + lowerW(exe) : L"a:" + lowerW(au);
        auto it = m.find(key);
        if (it == m.end()) { RunApp r; r.key = key; r.exe = exe; r.aumid = au; it = m.emplace(key, r).first; seen.push_back(key); }
        it->second.wins.push_back(h);
    }
    // orden estable: las que ya estaban no se mueven; las nuevas van al final
    std::vector<std::wstring> order;
    for (auto& k : runOrder) if (m.count(k)) order.push_back(k);
    for (auto& k : seen) if (std::find(order.begin(), order.end(), k) == order.end()) order.push_back(k);
    runOrder = order;
    running.clear(); for (auto& k : order) running.push_back(m[k]);
    HWND fg = GetForegroundWindow(); if (fg != gHwnd && fg != dockHwnd) fgAtOpen = fg;
}
static std::wstring exeDescription(const std::wstring& exe) {
    DWORD hnd = 0, sz = GetFileVersionInfoSizeW(exe.c_str(), &hnd);
    std::wstring r;
    if (sz) {
        std::vector<BYTE> b(sz);
        struct LC { WORD l, c; }* tr = nullptr; UINT n = 0;
        if (GetFileVersionInfoW(exe.c_str(), 0, sz, b.data()) && VerQueryValueW(b.data(), L"\\VarFileInfo\\Translation", (void**)&tr, &n) && n >= sizeof(LC)) {
            wchar_t q[64]; swprintf(q, 64, L"\\StringFileInfo\\%04x%04x\\FileDescription", tr->l, tr->c);
            wchar_t* d = nullptr; UINT dl = 0;
            if (VerQueryValueW(b.data(), q, (void**)&d, &dl) && d && dl > 1) r = trim(d);
        }
    }
    if (r.empty()) { r = PathFindFileNameW(exe.c_str()); if (endsWithI(r, L".exe")) r.resize(r.size() - 4); }
    return r;
}
static std::wstring runName(const RunApp& r) {
    auto it = runNames.find(r.key); if (it != runNames.end()) return it->second;
    std::wstring n;
    if (!r.aumid.empty()) {
        IShellItem* si = nullptr; LPWSTR dn = nullptr;
        if (SUCCEEDED(SHCreateItemFromParsingName((L"shell:AppsFolder\\" + r.aumid).c_str(), nullptr, IID_PPV_ARGS(&si)))) {
            if (SUCCEEDED(si->GetDisplayName(SIGDN_NORMALDISPLAY, &dn)) && dn) { n = dn; CoTaskMemFree(dn); }
            si->Release();
        }
    }
    if (n.empty() && !r.exe.empty()) n = exeDescription(r.exe);
    runNames[r.key] = n; return n;
}
static ID2D1Bitmap* runIcon(const RunApp& r) {
    auto it = runIcons.find(r.key); if (it != runIcons.end()) return it->second;
    UINT px = (UINT)lroundf(ICON_DIP * scale); ID2D1Bitmap* b = nullptr;
    if (!r.aumid.empty()) b = thumbFor(L"shell:AppsFolder\\" + r.aumid, px, SIIGBF_ICONONLY | SIIGBF_BIGGERSIZEOK);
    if (!b && !r.exe.empty()) {
        HICON h = iconFor(r.exe, SHIL_JUMBO);
        if (h) { b = bitmapFromIcon(h, px, true); DestroyIcon(h); }
        if (!b && (h = iconFor(r.exe, SHIL_EXTRALARGE))) { b = bitmapFromIcon(h, px, false); DestroyIcon(h); }
    }
    runIcons[r.key] = b; return b;
}

// ---------------------------------------------------------------- apps en segundo plano (iconos de la bandeja del sistema)
// Con la barra oculta no se llega a la flechita "^" de al lado de la hora. islita pone su propia ventana
// "Shell_TrayWnd" por delante de la del explorador: las apps le mandan sus iconos (Shell_NotifyIcon llega como
// WM_COPYDATA) y ella se los reenvía tal cual al explorador, así que la barra de Windows no pierde nada.
// Al arrancar se pide a todas las apps que vuelvan a registrar sus iconos (mensaje TaskbarCreated).
struct NID32 { DWORD cbSize, hWnd; UINT uID, uFlags, uCallbackMessage; DWORD hIcon; WCHAR szTip[128]; DWORD dwState, dwStateMask; WCHAR szInfo[256]; UINT uVersion; WCHAR szInfoTitle[64]; DWORD dwInfoFlags; GUID guidItem; DWORD hBalloonIcon; };
struct TrayMsg { DWORD sig, msg; NID32 nid; };
struct TrayIcon { HWND hwnd = nullptr; UINT uid = 0, cb = 0, ver = 0; bool hasGuid = false, hidden = false; GUID guid{}; HICON icon = nullptr; std::wstring tip; int gen = 0; };
static std::mutex trayMx; static std::vector<TrayIcon> trayIcons;  // los toca el hilo de la bandeja: siempre con trayMx
static HWND trayWnd = nullptr; static ULONGLONG trayBroadcastAt = 0; static int trayGen = 0;
static HWND h32(DWORD v) { return (HWND)(LONG_PTR)(LONG)v; }
static void trayParse(const COPYDATASTRUCT* cds) {
    if (cds->cbData < offsetof(TrayMsg, nid) + offsetof(NID32, szTip)) return;
    TrayMsg m{}; memcpy(&m, cds->lpData, std::min<size_t>(cds->cbData, sizeof m));
    if (m.sig != 0x34753423) return;
    NID32& n = m.nid;
    bool g = (n.uFlags & NIF_GUID) && n.cbSize >= offsetof(NID32, hBalloonIcon);
    bool changed = false;
    {
        std::lock_guard<std::mutex> lk(trayMx);
        auto it = std::find_if(trayIcons.begin(), trayIcons.end(), [&](const TrayIcon& t) {
            return g ? (t.hasGuid && IsEqualGUID(t.guid, n.guidItem)) : (!t.hasGuid && t.hwnd == h32(n.hWnd) && t.uid == n.uID);
        });
        if (m.msg == NIM_DELETE) {
            if (it != trayIcons.end()) { if (it->icon) DestroyIcon(it->icon); trayIcons.erase(it); changed = true; }
        } else if (m.msg == NIM_ADD || m.msg == NIM_MODIFY || m.msg == NIM_SETVERSION) {
            if (it == trayIcons.end() && m.msg == NIM_ADD) {
                TrayIcon t; t.hasGuid = g; if (g) t.guid = n.guidItem; t.hwnd = h32(n.hWnd); t.uid = n.uID;
                trayIcons.push_back(t); it = trayIcons.end() - 1;
            }
            if (it != trayIcons.end()) {
                TrayIcon& t = *it;
                if (n.hWnd) t.hwnd = h32(n.hWnd);
                if (m.msg == NIM_SETVERSION) t.ver = n.uVersion;
                else {
                    if (n.uFlags & NIF_MESSAGE) t.cb = n.uCallbackMessage;
                    if ((n.uFlags & NIF_ICON) && n.hIcon) {
                        HICON c = CopyIcon((HICON)(LONG_PTR)(LONG)n.hIcon);
                        if (c) { if (t.icon) DestroyIcon(t.icon); t.icon = c; t.gen = ++trayGen; }
                    }
                    if (n.uFlags & NIF_TIP) { n.szTip[127] = 0; t.tip = n.szTip; }
                    if ((n.uFlags & NIF_STATE) && (n.dwStateMask & NIS_HIDDEN)) t.hidden = (n.dwState & NIS_HIDDEN) != 0;
                }
                changed = true;
            }
        }
    }
    if (changed && gHwnd) PostMessageW(gHwnd, WM_APP_TRAY, 0, 0);
}
// por delante de la barra del explorador y en su mismo sitio (hay programas que miran dónde está la barra
// con GetWindowRect); asíncrono para que la isla no espere nunca a ese hilo
static void trayTopmost() {
    if (!trayWnd) return;
    RECT r{}; HWND t = realTray(); if (t) GetWindowRect(t, &r);
    SetWindowPos(trayWnd, HWND_TOPMOST, r.left, r.top, r.right - r.left, r.bottom - r.top, SWP_NOACTIVATE | SWP_ASYNCWINDOWPOS);
}
static void trayBroadcast() { trayBroadcastAt = GetTickCount64(); if (WM_TASKBARCREATED) SendNotifyMessageW(HWND_BROADCAST, WM_TASKBARCREATED, 0, 0); }
static LRESULT CALLBACK TrayProc(HWND h, UINT msg, WPARAM wp, LPARAM lp) {
    if (msg == WM_COPYDATA) {  // iconos (dwData 1) y avisos de barras (0, 3...): todo sigue llegando al explorador
        auto* cds = (const COPYDATASTRUCT*)lp;
        if (cds && cds->dwData == 1 && cds->lpData) trayParse(cds);
        HWND t = realTray(); DWORD_PTR r = 0;
        if (t && !SendMessageTimeoutW(t, msg, wp, lp, SMTO_ABORTIFHUNG, 4000, &r)) r = 0;
        return t ? (LRESULT)r : (cds && cds->dwData == 1);
    }
    if (msg == WM_TASKBARCREATED && WM_TASKBARCREATED) {  // el explorador se ha reiniciado: volver a ponerse delante y pedir los iconos
        if (GetTickCount64() - trayBroadcastAt > 10000) SetTimer(h, 1, 2500, nullptr);
        return 0;
    }
    if (msg == WM_TIMER && wp == 1) { KillTimer(h, 1); trayTopmost(); trayBroadcast(); return 0; }
    if (msg == WM_COMMAND || (msg >= WM_USER && msg < WM_APP)) {  // otros mensajes para la barra: al explorador
        HWND t = realTray(); DWORD_PTR r = 0;
        if (t) SendMessageTimeoutW(t, msg, wp, lp, SMTO_ABORTIFHUNG, 2000, &r);
        return (LRESULT)r;
    }
    return DefWindowProcW(h, msg, wp, lp);
}
static void trayThread() {
    WNDCLASSW wc{}; wc.lpfnWndProc = TrayProc; wc.hInstance = GetModuleHandleW(nullptr); wc.lpszClassName = L"Shell_TrayWnd";
    RegisterClassW(&wc);
    trayWnd = CreateWindowExW(WS_EX_TOOLWINDOW | WS_EX_TOPMOST, L"Shell_TrayWnd", L"", WS_POPUP, 0, 0, 0, 0, nullptr, nullptr, wc.hInstance, nullptr);
    if (!trayWnd) return;
    ChangeWindowMessageFilterEx(trayWnd, WM_COPYDATA, MSGFLT_ALLOW, nullptr);
    if (WM_TASKBARCREATED) ChangeWindowMessageFilterEx(trayWnd, WM_TASKBARCREATED, MSGFLT_ALLOW, nullptr);
    trayTopmost(); trayBroadcast();
    MSG m; while (GetMessageW(&m, nullptr, 0, 0) > 0) DispatchMessageW(&m);
}
// lado de la isla (hilo de la interfaz)
struct TrayView { std::wstring key, name; HWND hwnd; UINT uid, cb, ver; };
static std::vector<TrayView> trayList; static std::map<std::wstring, std::pair<int, ID2D1Bitmap*>> trayBmps;
static void freeTrayBmps() { for (auto& b : trayBmps) if (b.second.second) b.second.second->Release(); trayBmps.clear(); }
static int iconWidth(HICON h) {
    ICONINFO ii{}; if (!GetIconInfo(h, &ii)) return 0;
    BITMAP bm{}; GetObjectW(ii.hbmColor ? ii.hbmColor : ii.hbmMask, sizeof bm, &bm);
    if (ii.hbmColor) DeleteObject(ii.hbmColor);
    if (ii.hbmMask) DeleteObject(ii.hbmMask);
    return bm.bmWidth;
}
static std::map<std::wstring, std::wstring> trayExeNames;  // descripción de cada .exe (leerla cuesta)
static void trayRefresh() {
    trayList.clear();
    UINT px = (UINT)lroundf(32 * scale);
    std::set<std::wstring> keep;
    // con el candado solo se copia lo necesario: las apps que cambian su icono no tienen que esperar
    struct Snap { TrayView v; std::wstring tip; int gen; HICON icon; };  // icon: copia propia, solo si hay que redibujarlo
    std::vector<Snap> snap;
    {
        std::lock_guard<std::mutex> lk(trayMx);
        for (auto it = trayIcons.begin(); it != trayIcons.end();) {
            if (!IsWindow(it->hwnd)) { if (it->icon) DestroyIcon(it->icon); it = trayIcons.erase(it); continue; }
            if (it->hidden || !it->icon) { ++it; continue; }
            Snap sn; sn.v.hwnd = it->hwnd; sn.v.uid = it->uid; sn.v.cb = it->cb; sn.v.ver = it->ver; sn.tip = it->tip; sn.gen = it->gen; sn.icon = nullptr;
            wchar_t k[64];
            if (it->hasGuid) StringFromGUID2(it->guid, k, 64); else swprintf(k, 64, L"%p:%u", (void*)it->hwnd, it->uid);
            sn.v.key = k;
            auto b = trayBmps.find(sn.v.key);
            if (b == trayBmps.end() || b->second.first != it->gen) sn.icon = CopyIcon(it->icon);
            snap.push_back(sn);
            ++it;
        }
    }
    for (auto& sn : snap) {
        TrayView& v = sn.v;
        DWORD pid = 0; GetWindowThreadProcessId(v.hwnd, &pid);
        std::wstring exe = exeOfPid(pid), tip = sn.tip;
        size_t nl = tip.find_first_of(L"\r\n"); if (nl != std::wstring::npos) tip.resize(nl);
        v.name = trim(tip);
        if (v.name.empty() && !exe.empty()) {
            auto nm = trayExeNames.find(exe);
            v.name = nm != trayExeNames.end() ? nm->second : (trayExeNames[exe] = exeDescription(exe));
        }
        if (sn.icon) {
            auto b = trayBmps.find(v.key);
            if (b != trayBmps.end() && b->second.second) b->second.second->Release();
            ID2D1Bitmap* bmp = nullptr;
            // los iconos de la bandeja suelen ser de 16 px: si es pequeño, mejor el del programa (más nítido);
            // los del explorador (Bluetooth, sonido...) con su propio icono
            if (iconWidth(sn.icon) < (int)px && !exe.empty() && !endsWithI(exe, L"\\explorer.exe")) {
                HICON hi = iconFor(exe, SHIL_JUMBO);
                if (hi) { bmp = bitmapFromIcon(hi, px, true); DestroyIcon(hi); }
                if (!bmp && (hi = iconFor(exe, SHIL_EXTRALARGE))) { bmp = bitmapFromIcon(hi, px, false); DestroyIcon(hi); }
            }
            if (!bmp) bmp = bitmapFromIcon(sn.icon, px, false);
            DestroyIcon(sn.icon);
            trayBmps[v.key] = {sn.gen, bmp};
        }
        keep.insert(v.key);
        trayList.push_back(v);
    }
    for (auto b = trayBmps.begin(); b != trayBmps.end();) {
        if (keep.count(b->first)) ++b; else { if (b->second.second) b->second.second->Release(); b = trayBmps.erase(b); }
    }
}
// menú de una app de segundo plano abierto: la isla deja de estar siempre encima para no taparlo
// (muchas apps, como las de Electron, WinForms o Qt, pintan su menú en una ventana normal, no en un menú de Windows)
static DWORD trayMenuPid = 0; static ULONGLONG trayMenuAt = 0;
static void trayMenuBegin(DWORD pid) {
    trayMenuPid = pid; trayMenuAt = GetTickCount64();
    SetWindowPos(gHwnd, HWND_NOTOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
}
struct PidMenu { DWORD pid; int mw, mh; bool hit; };
// ventana emergente pequeña y visible de esa app (su menú, sea de Windows o pintado por ella)
static BOOL CALLBACK pidMenuWin(HWND h, LPARAM lp) {
    auto* q = (PidMenu*)lp; DWORD p = 0; GetWindowThreadProcessId(h, &p);
    if (p != q->pid || !IsWindowVisible(h)) return TRUE;
    LONG_PTR st = GetWindowLongPtrW(h, GWL_STYLE);
    if (!(st & WS_POPUP) || (st & WS_CAPTION) == WS_CAPTION) return TRUE;
    int cloaked = 0; DwmGetWindowAttribute(h, DWMWA_CLOAKED, &cloaked, sizeof cloaked);
    RECT r; GetWindowRect(h, &r);
    int w = r.right - r.left, hh = r.bottom - r.top;
    if (cloaked || w < 8 || hh < 8 || w > q->mw * 6 / 10 || hh > q->mh * 9 / 10) return TRUE;
    q->hit = true; return FALSE;
}
// true mientras el menú siga abierto (máximo medio minuto)
static bool trayMenuActive() {
    if (!trayMenuPid) return false;
    ULONGLONG el = GetTickCount64() - trayMenuAt;
    bool on = el < 1500;  // margen para que la app llegue a sacar el menú
    if (!on && el < 30000) {
        PidMenu q{trayMenuPid, (int)(mon.right - mon.left), (int)(mon.bottom - mon.top), false};
        EnumWindows(pidMenuWin, (LPARAM)&q); on = q.hit;
    }
    if (!on) trayMenuPid = 0;
    return on;
}
// el mismo clic que le mandaría la barra de tareas
static void trayClick(int i, bool right) {
    if (i < 0 || i >= (int)trayList.size()) return;
    const TrayView& t = trayList[i];
    if (!IsWindow(t.hwnd) || !t.cb) return;
    DWORD pid = 0; GetWindowThreadProcessId(t.hwnd, &pid); AllowSetForegroundWindow(pid);
    if (right) trayMenuBegin(pid);
    POINT pt; GetCursorPos(&pt);
    auto send = [&](UINT m) {
        if (t.ver >= 4) PostMessageW(t.hwnd, t.cb, MAKEWPARAM((WORD)pt.x, (WORD)pt.y), MAKELPARAM(m, t.uid));
        else PostMessageW(t.hwnd, t.cb, t.uid, m);
    };
    if (right) { send(WM_RBUTTONDOWN); send(WM_RBUTTONUP); if (t.ver >= 3) send(WM_CONTEXTMENU); }
    else { send(WM_LBUTTONDOWN); send(WM_LBUTTONUP); if (t.ver >= 3) send(WM_USER + 0 /* NIN_SELECT */); }
}

// qué programa abre cada atajo, para reconocerlo cuando está abierto
static void resolvePinned(App& a) {
    if (a.resolved) return;
    a.resolved = true;
    const std::wstring pre = L"shell:AppsFolder\\";
    if (!_wcsnicmp(a.target.c_str(), pre.c_str(), pre.size())) {
        std::wstring id = a.target.substr(pre.size());
        if (id.size() > 38 && id[0] == L'{' && id[37] == L'}') {
            GUID g; LPWSTR kf = nullptr;
            if (SUCCEEDED(CLSIDFromString(id.substr(0, 38).c_str(), &g)) && SUCCEEDED(SHGetKnownFolderPath(g, 0, nullptr, &kf)) && kf) a.mExe = std::wstring(kf) + id.substr(38);
            CoTaskMemFree(kf);
        } else {
            a.mAumid = lowerW(id);
            IShellItem2* si = nullptr; LPWSTR tp = nullptr;
            if (SUCCEEDED(SHCreateItemFromParsingName(a.target.c_str(), nullptr, IID_PPV_ARGS(&si)))) {
                if (SUCCEEDED(si->GetString(PKEY_LinkTarget_, &tp)) && tp) { if (endsWithI(tp, L".exe")) a.mExe = tp; CoTaskMemFree(tp); }
                si->Release();
            }
        }
    } else if (endsWithI(a.target, L".exe")) {
        a.mExe = a.target;
        if (a.mExe.find(L'\\') == std::wstring::npos) { wchar_t full[MAX_PATH]; if (SearchPathW(nullptr, a.mExe.c_str(), nullptr, MAX_PATH, full, nullptr)) a.mExe = full; }
    }
    if (endsWithI(a.icon, L".exe")) a.mExe2 = a.icon;  // p. ej. Ajustes (ms-settings:) con el icono de SystemSettings.exe
    a.mExe = lowerW(a.mExe); a.mExe2 = lowerW(a.mExe2);
}
static bool runMatches(const RunApp& r, const App& a) {
    if (!a.mAumid.empty() && lowerW(r.aumid) == a.mAumid) return true;
    std::wstring e = lowerW(r.exe);
    return !e.empty() && (e == a.mExe || e == a.mExe2);
}
static void refreshTiles() {
    for (auto& a : apps) resolvePinned(a);
    refreshRunning();
    for (auto it = runIcons.begin(); it != runIcons.end();) {  // solo se quedan los de las que siguen abiertas
        bool alive = false; for (auto& r : running) if (r.key == it->first) { alive = true; break; }
        if (alive) ++it; else { if (it->second) it->second->Release(); it = runIcons.erase(it); }
    }
    // como el dock del Mac: primero las fijadas (en su orden, con puntito si están abiertas) y luego las demás abiertas
    tiles.clear(); nPinnedTiles = 0;
    std::vector<bool> used(running.size(), false);
    std::vector<int> pinRun(apps.size(), -1);
    for (int j = 0; j < (int)apps.size(); j++)
        for (int r = 0; r < (int)running.size(); r++) if (!used[r] && runMatches(running[r], apps[j])) { pinRun[j] = r; used[r] = true; break; }
    // si no se ha reconocido por el programa (p. ej. Discord, que se abre con su Update.exe), por el nombre
    for (int j = 0; j < (int)apps.size(); j++) if (pinRun[j] < 0)
        for (int r = 0; r < (int)running.size(); r++) if (!used[r] && !_wcsicmp(runName(running[r]).c_str(), apps[j].name.c_str())) { pinRun[j] = r; used[r] = true; break; }
    for (int j = 0; j < (int)apps.size(); j++) { Tile t; t.pin = j; t.run = pinRun[j]; tiles.push_back(t); nPinnedTiles++; }
    for (int r = 0; r < (int)running.size(); r++) if (!used[r]) { Tile t; t.run = r; tiles.push_back(t); }
    if ((int)tiles.size() > MAX_TILES) tiles.resize(MAX_TILES);
    nPinnedTiles = std::min(nPinnedTiles, (int)tiles.size());
}
static std::wstring tileName(const Tile& t) { return t.pin >= 0 ? apps[t.pin].name : runName(running[t.run]); }
static ID2D1Bitmap* tileIcon(const Tile& t) { return t.pin >= 0 && apps[t.pin].bmp ? apps[t.pin].bmp : t.run >= 0 ? runIcon(running[t.run]) : nullptr; }
static void forceForeground(HWND w) {
    if (IsIconic(w)) ShowWindow(w, SW_RESTORE);
    if (!SetForegroundWindow(w)) {
        HWND fg = GetForegroundWindow();
        DWORD ft = fg ? GetWindowThreadProcessId(fg, nullptr) : 0, me = GetCurrentThreadId();
        if (ft && ft != me && AttachThreadInput(me, ft, TRUE)) { SetForegroundWindow(w); AttachThreadInput(me, ft, FALSE); }
    }
}
// clic en una app abierta: va a su ventana; si ya estaba delante, a la siguiente o se minimiza (como la barra de tareas)
static void activateRun(const RunApp& r) {
    if (r.wins.empty()) return;
    HWND top = r.wins.front();
    if (top == fgAtOpen && !IsIconic(top)) {
        if (r.wins.size() > 1) forceForeground(r.wins.back());
        else ShowWindow(top, SW_MINIMIZE);
    } else forceForeground(top);
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
static ID2D1Bitmap* thumbFor(const std::wstring& path, UINT px, int flags) {
    IShellItemImageFactory* f = nullptr;
    if (FAILED(SHCreateItemFromParsingName(path.c_str(), nullptr, IID_PPV_ARGS(&f)))) return nullptr;
    HBITMAP hb = nullptr; SIZE sz{(LONG)px, (LONG)px};
    f->GetImage(sz, (SIIGBF)flags, &hb); f->Release();
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
// salida de sonido, como en la barra de tareas. Windows no tiene una función pública para cambiar el
// dispositivo predeterminado: se usa IPolicyConfig, la interfaz del propio panel de sonido (la usan también
// EarTrumpet o SoundSwitch). Solo importa el orden de la tabla: se llama a SetDefaultEndpoint.
struct IPolicyConfig_ : IUnknown {
    virtual HRESULT STDMETHODCALLTYPE GetMixFormat(PCWSTR, void**) = 0;
    virtual HRESULT STDMETHODCALLTYPE GetDeviceFormat(PCWSTR, INT, void**) = 0;
    virtual HRESULT STDMETHODCALLTYPE ResetDeviceFormat(PCWSTR) = 0;
    virtual HRESULT STDMETHODCALLTYPE SetDeviceFormat(PCWSTR, void*, void*) = 0;
    virtual HRESULT STDMETHODCALLTYPE GetProcessingPeriod(PCWSTR, INT, void*, void*) = 0;
    virtual HRESULT STDMETHODCALLTYPE SetProcessingPeriod(PCWSTR, void*) = 0;
    virtual HRESULT STDMETHODCALLTYPE GetShareMode(PCWSTR, void*) = 0;
    virtual HRESULT STDMETHODCALLTYPE SetShareMode(PCWSTR, void*) = 0;
    virtual HRESULT STDMETHODCALLTYPE GetPropertyValue(PCWSTR, void*, void*) = 0;
    virtual HRESULT STDMETHODCALLTYPE SetPropertyValue(PCWSTR, void*, void*) = 0;
    virtual HRESULT STDMETHODCALLTYPE SetDefaultEndpoint(PCWSTR, ERole) = 0;
    virtual HRESULT STDMETHODCALLTYPE SetEndpointVisibility(PCWSTR, INT) = 0;
};
static const CLSID CLSID_PolicyConfigClient_ = {0x870af99c, 0x171d, 0x4f9e, {0xaf, 0x0d, 0xe6, 0x3d, 0xf4, 0x0c, 0x2b, 0xc9}};
static const IID IID_IPolicyConfig_ = {0xf8679f50, 0x850a, 0x41cf, {0x9c, 0x72, 0x43, 0x0f, 0x29, 0x02, 0x90, 0xc8}};
static const PROPERTYKEY PKEY_DevFriendlyName_ = {{0xa45c254e, 0xdf1c, 0x4efd, {0x80, 0x20, 0x67, 0xd1, 0x46, 0xa8, 0x50, 0xe0}}, 14};
struct AudioDev { std::wstring id, name; };
static std::vector<AudioDev> devs; static std::wstring devCur; static bool devOpen = false;
static void devLoad() {  // solo al abrir la lista
    devs.clear(); devCur.clear();
    IMMDeviceEnumerator* en = nullptr;
    if (FAILED(CoCreateInstance(__uuidof(MMDeviceEnumerator), nullptr, CLSCTX_ALL, __uuidof(IMMDeviceEnumerator), (void**)&en))) return;
    IMMDevice* d = nullptr; LPWSTR id = nullptr;
    if (SUCCEEDED(en->GetDefaultAudioEndpoint(eRender, eConsole, &d))) { if (SUCCEEDED(d->GetId(&id)) && id) { devCur = id; CoTaskMemFree(id); } d->Release(); }
    IMMDeviceCollection* c = nullptr;
    if (SUCCEEDED(en->EnumAudioEndpoints(eRender, DEVICE_STATE_ACTIVE, &c))) {
        UINT n = 0; c->GetCount(&n);
        for (UINT i = 0; i < n; i++) {
            IMMDevice* dv = nullptr; if (FAILED(c->Item(i, &dv))) continue;
            AudioDev a; LPWSTR sid = nullptr;
            if (SUCCEEDED(dv->GetId(&sid)) && sid) { a.id = sid; CoTaskMemFree(sid); }
            IPropertyStore* ps = nullptr;
            if (SUCCEEDED(dv->OpenPropertyStore(STGM_READ, &ps))) {
                PROPVARIANT v; PropVariantInit(&v);
                if (SUCCEEDED(ps->GetValue(PKEY_DevFriendlyName_, &v)) && v.vt == VT_LPWSTR && v.pwszVal) a.name = v.pwszVal;
                PropVariantClear(&v); ps->Release();
            }
            if (!a.id.empty()) devs.push_back(a);
            dv->Release();
        }
        c->Release();
    }
    en->Release();
}
static void devSet(int i) {  // como "Elegir dónde reproducir el sonido" de Configuración: consola y multimedia
    if (i < 0 || i >= (int)devs.size()) return;
    IPolicyConfig_* pc = nullptr;
    if (SUCCEEDED(CoCreateInstance(CLSID_PolicyConfigClient_, nullptr, CLSCTX_ALL, IID_IPolicyConfig_, (void**)&pc)) && pc) {
        pc->SetDefaultEndpoint(devs[i].id.c_str(), eConsole);
        pc->SetDefaultEndpoint(devs[i].id.c_str(), eMultimedia);
        pc->Release();
    }
    devCur = devs[i].id;
    SafeRelease(vol);  // el deslizador pasa a mover el nuevo
}
static float volGet(bool* mute) {
    float v = 0; BOOL m = FALSE;
    if (vol) { vol->GetMasterVolumeLevelScalar(&v); vol->GetMute(&m); }
    if (mute) *mute = m;
    return v;
}

// "pop" al cambiar el volumen (como en el Mac): suena al volumen nuevo, así se oye cómo de alto ha quedado.
// Se genera una vez en memoria: un tono que baja rápido de tono (1150 -> 620 Hz) con un ataque suave y
// una caída corta, con un armónico flojo para que suene redondo. ~0,1 s, 9 KB.
static std::vector<BYTE> popWav;
static void buildPop() {
    const int sr = 44100, n = sr / 10;
    popWav.assign(44 + n * 2, 0);
    BYTE* b = popWav.data();
    auto u32 = [&](int o, DWORD v) { memcpy(b + o, &v, 4); };
    auto u16 = [&](int o, WORD v) { memcpy(b + o, &v, 2); };
    memcpy(b, "RIFF", 4); u32(4, 36 + n * 2); memcpy(b + 8, "WAVEfmt ", 8);
    u32(16, 16); u16(20, 1); u16(22, 1); u32(24, sr); u32(28, sr * 2); u16(32, 2); u16(34, 16);
    memcpy(b + 36, "data", 4); u32(40, n * 2);
    double ph = 0;
    for (int i = 0; i < n; i++) {
        double t = (double)i / sr;
        double f = 620 + 530 * exp(-t * 55);           // caída de tono: "pop"
        ph += 2 * M_PI * f / sr;
        double env = std::min(1.0, t / 0.004) * exp(-t * 38);
        double v = (sin(ph) + 0.22 * sin(2 * ph)) * env * 0.42;
        short smp = (short)lround(std::clamp(v, -1.0, 1.0) * 32767);
        memcpy(b + 44 + i * 2, &smp, 2);
    }
}
static void volPop() {
    if (alertOn) return;  // no cortar la alarma del temporizador (PlaySound es de uno en uno)
    static ULONGLONG last = 0; ULONGLONG n = GetTickCount64();
    if (n - last < 90) return;  // con la rueda, como mucho unos 11 por segundo
    bool m = false; float v = volGet(&m);
    if (m || v < 0.005f) return;
    last = n;
    if (popWav.empty()) buildPop();
    PlaySoundW((LPCWSTR)popWav.data(), nullptr, SND_MEMORY | SND_ASYNC | SND_NODEFAULT);
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

// ---------------------------------------------------------------- buscador de aplicaciones (como el menú Inicio)
static const GUID FOLDERID_AppsFolder_ = {0x1e87508d, 0x89c2, 0x42f0, {0x8a, 0x7e, 0x64, 0x5a, 0x0f, 0x50, 0xca, 0x58}};
static const GUID BHID_EnumItems_ = {0x94f60519, 0x2850, 0x4924, {0xaa, 0x5a, 0xd1, 0x5e, 0x84, 0x86, 0x80, 0x39}};
static const wchar_t* APPS_PREFIX = L"shell:AppsFolder\\";
static const PROPERTYKEY PKEY_Link_TargetParsingPath_ = {{0xB9B4B3FC, 0x2B51, 0x4A42, {0xB5, 0xD8, 0x32, 0x41, 0x46, 0xAF, 0xCF, 0x25}}, 2};
// minúsculas y sin tildes, para que "camara" encuentre "Cámara"
static std::wstring foldKey(const std::wstring& s) {
    if (s.empty()) return s;
    std::wstring d = s;
    int n = FoldStringW(MAP_COMPOSITE, s.c_str(), (int)s.size(), nullptr, 0);
    if (n > 0) { d.assign(n, 0); FoldStringW(MAP_COMPOSITE, s.c_str(), (int)s.size(), &d[0], n); }
    std::wstring o; o.reserve(d.size());
    for (wchar_t c : d) if (c < 0x300 || c > 0x36F) o += c;
    if (!o.empty()) CharLowerBuffW(&o[0], (DWORD)o.size());
    return o;
}
static bool isSep(wchar_t c) { return c == L' ' || c == L'-' || c == L'_' || c == L'.' || c == L'(' || c == L'/'; }
// lista de apps del menú Inicio (de escritorio y de la Store), en un hilo aparte
static void enumApps(unsigned gen) {
    CoInitializeEx(nullptr, COINIT_APARTMENTTHREADED);
    std::vector<SApp> out;
    IShellItem* root = nullptr;
    if (SUCCEEDED(SHGetKnownFolderItem(FOLDERID_AppsFolder_, KF_FLAG_DEFAULT, nullptr, IID_PPV_ARGS(&root)))) {
        IEnumShellItems* en = nullptr;
        if (SUCCEEDED(root->BindToHandler(nullptr, BHID_EnumItems_, IID_PPV_ARGS(&en)))) {
            IShellItem* it = nullptr; ULONG got = 0;
            while (en->Next(1, &it, &got) == S_OK && it) {
                LPWSTR nm = nullptr, pid = nullptr;
                if (SUCCEEDED(it->GetDisplayName(SIGDN_NORMALDISPLAY, &nm)) && SUCCEEDED(it->GetDisplayName(SIGDN_PARENTRELATIVEPARSING, &pid)) && nm && pid && *nm) {
                    SApp a; a.name = nm; a.id = pid; a.key = foldKey(a.name);
                    // ruta del programa, para reconocer los atajos que ya apuntan a él
                    IShellItem2* i2 = nullptr; LPWSTR tp = nullptr;
                    if (SUCCEEDED(it->QueryInterface(IID_PPV_ARGS(&i2)))) {
                        if (SUCCEEDED(i2->GetString(PKEY_Link_TargetParsingPath_, &tp)) && tp) { a.path = tp; CoTaskMemFree(tp); }
                        i2->Release();
                    }
                    if (a.path.empty() && a.id.size() > 38 && a.id[0] == L'{' && a.id[37] == L'}') {  // {carpeta conocida}\resto
                        GUID g; LPWSTR kf = nullptr;
                        if (SUCCEEDED(CLSIDFromString(a.id.substr(0, 38).c_str(), &g)) && SUCCEEDED(SHGetKnownFolderPath(g, 0, nullptr, &kf)) && kf)
                            a.path = std::wstring(kf) + a.id.substr(38);
                        CoTaskMemFree(kf);
                    }
                    bool junk = a.key.find(L"uninstall") != std::wstring::npos || a.key.find(L"desinstal") != std::wstring::npos;
                    if (!junk) out.push_back(std::move(a));
                }
                CoTaskMemFree(nm); CoTaskMemFree(pid); it->Release(); it = nullptr;
            }
            en->Release();
        }
        root->Release();
    }
    CoUninitialize();
    std::sort(out.begin(), out.end(), [](const SApp& a, const SApp& b) { return a.key < b.key; });
    out.erase(std::unique(out.begin(), out.end(), [](const SApp& a, const SApp& b) { return a.key == b.key; }), out.end());
    for (auto& a : out)  // iniciales: "vsc" encuentra "Visual Studio Code"
        for (size_t i = 0; i < a.key.size(); i++) if (!isSep(a.key[i]) && (i == 0 || isSep(a.key[i - 1]))) a.ini += a.key[i];
    { std::lock_guard<std::mutex> lk(gMx); gAppsShared.swap(out); }
    PostMessage(gHwnd, WM_APP_APPS, gen, 0);
}
static const int S_COLS = 2, S_ROWS = 4;
static int sMaxScroll() { return std::max(0, ((int)sRes.size() + S_COLS - 1) / S_COLS - S_ROWS); }
static void sEnsureVisible() {
    int r = sSel / S_COLS;
    if (r < sScroll) sScroll = r;
    if (r >= sScroll + S_ROWS) sScroll = r - S_ROWS + 1;
    sScroll = std::clamp(sScroll, 0, sMaxScroll());
}
static void sFilter() {
    sRes.clear(); sSel = 0; sScroll = 0;
    std::wstring q = foldKey(trim(sQ));
    if (q.empty()) { for (int i = 0; i < (int)sApps.size(); i++) sRes.push_back(i); return; }
    std::vector<std::pair<int, int>> sc;
    for (int i = 0; i < (int)sApps.size(); i++) {
        const SApp& a = sApps[i]; int best = -1;
        // 0 empieza por, 1 empieza una palabra, 2 está dentro, 3 iniciales
        for (size_t p = a.key.find(q); p != std::wstring::npos && best != 0; p = a.key.find(q, p + 1)) {
            int s = p == 0 ? 0 : isSep(a.key[p - 1]) ? 1 : 2;
            if (best < 0 || s < best) best = s;
        }
        if (best < 0 && q.size() >= 2 && a.ini.compare(0, q.size(), q) == 0) best = 3;
        if (best >= 0) sc.push_back({best, i});
    }
    std::stable_sort(sc.begin(), sc.end(), [](const std::pair<int, int>& a, const std::pair<int, int>& b) {
        if (a.first != b.first) return a.first < b.first;
        return sApps[a.second].name.size() < sApps[b.second].name.size();
    });
    for (auto& p : sc) sRes.push_back(p.second);
}
// atajo que ya abre esta app (por shell:AppsFolder o por la ruta del programa); vacío si no hay
static std::wstring sPinnedTarget(const SApp& s) {
    std::wstring t = APPS_PREFIX + s.id;
    for (auto& a : apps)
        if (!_wcsicmp(a.target.c_str(), t.c_str()) || (!s.path.empty() && !_wcsicmp(a.target.c_str(), s.path.c_str()))) return a.target;
    return L"";
}
static bool sPinned(const SApp& s) { return !sPinnedTarget(s).empty(); }
static std::wstring fromUtf8(const std::string& s) {
    int n = MultiByteToWideChar(CP_UTF8, 0, s.data(), (int)s.size(), nullptr, 0);
    std::wstring w(n, 0); if (n) MultiByteToWideChar(CP_UTF8, 0, s.data(), (int)s.size(), &w[0], n);
    return w;
}
static void appendAtajo(std::wstring name, const std::wstring& target) {
    std::string raw; bg::readAll(appsFile, raw);
    if (!raw.empty() && raw.back() != '\n') raw += "\r\n";
    for (auto& c : name) if (c == L'|') c = L'/';
    raw += toUtf8(name + L" | " + target) + "\r\n";
    bg::writeAll(appsFile, raw);
}
static void removeAtajo(const std::wstring& target) {
    std::string raw; if (!bg::readAll(appsFile, raw)) return;
    std::string out; size_t p = 0;
    while (p < raw.size()) {
        size_t e = raw.find('\n', p); if (e == std::string::npos) e = raw.size();
        std::string l = raw.substr(p, e - p); p = e + 1;
        std::wstring w = trim(fromUtf8(l));
        bool drop = false;
        if (!w.empty() && w[0] != L'#') {
            size_t a = w.find(L'|');
            if (a != std::wstring::npos) {
                size_t b = w.find(L'|', a + 1);
                std::wstring t = expandEnv(trim(w.substr(a + 1, b == std::wstring::npos ? std::wstring::npos : b - a - 1)));
                drop = !_wcsicmp(t.c_str(), target.c_str());
            }
        }
        if (!drop) { out += l; if (e < raw.size()) out += "\n"; }
    }
    bg::writeAll(appsFile, out);
}
static void sTogglePin(int ri) {
    if (ri < 0 || ri >= (int)sRes.size()) return;
    const SApp& a = sApps[sRes[ri]];
    std::wstring t = APPS_PREFIX + a.id, cur = sPinnedTarget(a);
    if (!cur.empty()) { removeAtajo(cur); sMsg = L"Quitada del dock"; }
    else if ((int)apps.size() >= MAX_APPS) sMsg = L"Dock lleno (36): quita una antes";
    else { appendAtajo(a.name, t); sMsg = L"Fijada en el dock"; }
    sMsgAt = nowMs();
    dockAppsChanged();
}
static void grabFocusOf(HWND w) {
    HWND fg = GetForegroundWindow();
    if (fg != w && !SetForegroundWindow(w)) {
        DWORD ft = fg ? GetWindowThreadProcessId(fg, nullptr) : 0, me = GetCurrentThreadId();
        if (ft && ft != me && AttachThreadInput(me, ft, TRUE)) { SetForegroundWindow(w); AttachThreadInput(me, ft, FALSE); }
    }
    SetFocus(w);
}
static void grabFocus() { grabFocusOf(gHwnd); }
static void startSearch() {
    view = V_SEARCH; sActive = true; sQ.clear(); sMsg.clear(); sCaret = true;
    HWND fg = GetForegroundWindow(); if (fg != gHwnd) sPrevFg = fg;
    grabFocus();  // para poder escribir
    SetTimer(gHwnd, T_CARET, 530, nullptr);
    if (!sLoaded) std::thread(enumApps, ++sGen).detach();
    sFilter();
}
static void endSearch(bool restoreFocus) {
    if (!sActive) return;
    sActive = false; KillTimer(gHwnd, T_CARET); freeSearchIcons();
    if (restoreFocus && GetForegroundWindow() == gHwnd && sPrevFg && IsWindow(sPrevFg)) SetForegroundWindow(sPrevFg);
    sPrevFg = nullptr;
    if (view == V_SEARCH) view = lastTab;
    if (expanded && !hovered) SetTimer(gHwnd, T_COLLAPSE, 450, nullptr);  // con el ratón fuera, se pliega como siempre
}
static void sLaunch(int ri) {
    if (ri < 0 || ri >= (int)sRes.size()) return;
    std::wstring t = APPS_PREFIX + sApps[sRes[ri]].id;
    endSearch(false);
    ShellExecuteW(nullptr, L"open", t.c_str(), nullptr, nullptr, SW_SHOWNORMAL);
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
    fSearch = mkFont(T, 15, DWRITE_FONT_WEIGHT_NORMAL);
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
    SafeRelease(br); SafeRelease(dcrt); rt = nullptr; SafeRelease(artBmp); SafeRelease(artSBmp); artVerUI = ~0u; dockDropBitmaps(); freeIcons(); freeSearchIcons(); freeRunIcons();
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
        if (!rt) createTarget(); else { rt->SetDpi(96 * scale, 96 * scale); dockDropBitmaps(); freeIcons(); freeSearchIcons(); freeRunIcons(); SafeRelease(cacheRT); cacheValid = false; for (auto& it : shelf) { SafeRelease(it.bmp); it.tried = false; } }
        ensureDib();
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
static ID2D1PathGeometry* boltGeo = nullptr;
static void drawBolt(float cx, float cy, float hgt) {
    if (!boltGeo) {
        if (FAILED(d2d->CreatePathGeometry(&boltGeo))) { boltGeo = nullptr; return; }
        ID2D1GeometrySink* s = nullptr;
        if (SUCCEEDED(boltGeo->Open(&s))) {
            static const D2D1_POINT_2F P[] = {{0.12f, -0.5f}, {-0.31f, 0.07f}, {-0.03f, 0.07f}, {-0.12f, 0.5f}, {0.31f, -0.08f}, {0.03f, -0.08f}};
            s->BeginFigure(P[0], D2D1_FIGURE_BEGIN_FILLED); s->AddLines(P + 1, 5); s->EndFigure(D2D1_FIGURE_END_CLOSED);
            s->Close(); s->Release();
        }
    }
    if (hgt <= 0.1f) return;
    D2D1_MATRIX_3X2_F cur; rt->GetTransform(&cur);
    D2D1::Matrix3x2F m = D2D1::Matrix3x2F::Scale(hgt, hgt) * D2D1::Matrix3x2F::Translation(cx, cy) * *D2D1::Matrix3x2F::ReinterpretBaseType(&cur);
    rt->SetTransform(&m); rt->FillGeometry(boltGeo, br); rt->SetTransform(&cur);
}
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
enum { PM_IDLE, PM_MUSIC, PM_EVENT, PM_ALERT, PM_TIMER, PM_SW, PM_CHARGE };
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
    if (chargeOn) return PM_CHARGE;
    int m = 0; const CalEvent* e = cfg.alerts ? upcomingEvent(&m) : nullptr;
    if (e && m <= 15) return PM_EVENT;
    if (tmState) return PM_TIMER;
    if (swRun) return PM_SW;
    if (media.has && !media.title.empty()) return PM_MUSIC;
    if (e) return PM_EVENT;
    return PM_IDLE;
}
static std::wstring hhmm(int m) { wchar_t b[8]; swprintf(b, 8, L"%02d:%02d", m / 60, m % 60); return b; }

static SYSTEM_POWER_STATUS psCache{}; static bool psOk = false; static ULONGLONG psAt = 0;
// estado de la batería guardado un segundo: con música la píldora se dibuja muchas veces por segundo
static const SYSTEM_POWER_STATUS& powerStatus(bool* ok = nullptr) {
    ULONGLONG n = GetTickCount64();
    if (!psAt || n - psAt >= 1000) { psOk = GetSystemPowerStatus(&psCache) != 0; psAt = n; }
    if (ok) *ok = psOk;
    return psCache;
}
static void drawBattery(float x, float cy) {
    bool ok; SYSTEM_POWER_STATUS ps = powerStatus(&ok); if (!ok || ps.BatteryFlag == 128 || ps.BatteryFlag == 255 || ps.BatteryLifePercent > 100) return;
    float pct = ps.BatteryLifePercent / 100.f; bool chg = ps.ACLineStatus == 1;
    std::wstring num = std::to_wstring(ps.BatteryLifePercent);
    col(1, 1, 1, 0.9f); textN(num, fSmall, x - 34, cy - 9, 30, 18, DWRITE_TEXT_ALIGNMENT_TRAILING);
    if (chg) { colC(GREEN); drawBolt(x - 4 - textWidth(num, fSmall) - 8, cy, 11); }
    col(1, 1, 1, 0.4f);
    D2D1_ROUNDED_RECT body{{x, cy - 5.5f, x + 22, cy + 5.5f}, 3.2f, 3.2f}; rt->DrawRoundedRectangle(&body, br, 1.1f, nullptr);
    fillRR(x + 23, cy - 2, 1.6f, 4, 0.8f);
    if (chg) colC(GREEN); else if (pct <= 0.2f) colC(RED); else col(1, 1, 1, 1);
    fillRR(x + 2, cy - 3.5f, 18 * clampf(pct, 0.06f, 1), 7, 1.6f);
}

// ---------------------------------------------------------------- wifi y volumen en la píldora (por avisos de Windows, sin sondear)
static int netKind = 0, netBars = 0;  // netKind: 0 sin red, 1 wifi, 2 cable
static HANDLE wlanH = nullptr;
static std::atomic<int> wifiBarsSeen{-1};
static int barsOf(ULONG q) { return q >= 75 ? 4 : q >= 50 ? 3 : q >= 25 ? 2 : 1; }
// Windows avisa de cada escaneo y de cada cambio de señal: solo se despierta a la isla si cambia algo visible
static std::atomic<bool> gWifiListOpen{false};
static void CALLBACK wlanNotify(PWLAN_NOTIFICATION_DATA d, PVOID) {
    if (d->NotificationSource == WLAN_NOTIFICATION_SOURCE_MSM) {
        if (d->NotificationCode == wlan_notification_msm_signal_quality_change && d->pData && d->dwDataSize >= sizeof(ULONG)) {
            int b = barsOf(*(ULONG*)d->pData);
            if (wifiBarsSeen.exchange(b) != b) PostMessage(gHwnd, WM_APP_NET, 0, 0);
            return;
        }
        if (d->NotificationCode != wlan_notification_msm_connected && d->NotificationCode != wlan_notification_msm_disconnected) return;
    } else if (d->NotificationSource == WLAN_NOTIFICATION_SOURCE_ACM) {
        switch (d->NotificationCode) {
        case wlan_notification_acm_connection_complete: case wlan_notification_acm_disconnected:
        case wlan_notification_acm_interface_arrival: case wlan_notification_acm_interface_removal: break;
        case wlan_notification_acm_scan_complete: case wlan_notification_acm_scan_fail: if (!gWifiListOpen) return; break;
        default: return;
        }
    }
    PostMessage(gHwnd, WM_APP_NET, 0, 0);
}
static void CALLBACK ipChange(PVOID, PMIB_IPINTERFACE_ROW, MIB_NOTIFICATION_TYPE) { PostMessage(gHwnd, WM_APP_NET, 0, 0); }
static bool refreshNet() {  // true si ha cambiado lo que se ve
    int kind = 0, bars = 0;
    PWLAN_INTERFACE_INFO_LIST l = nullptr;
    if (wlanH && WlanEnumInterfaces(wlanH, nullptr, &l) == ERROR_SUCCESS) {
        for (DWORD i = 0; i < l->dwNumberOfItems && !kind; i++) {
            if (l->InterfaceInfo[i].isState != wlan_interface_state_connected) continue;
            DWORD sz = 0; PWLAN_CONNECTION_ATTRIBUTES ca = nullptr; WLAN_OPCODE_VALUE_TYPE vt;
            if (WlanQueryInterface(wlanH, &l->InterfaceInfo[i].InterfaceGuid, wlan_intf_opcode_current_connection, nullptr, &sz, (PVOID*)&ca, &vt) == ERROR_SUCCESS && ca) {
                ULONG q = ca->wlanAssociationAttributes.wlanSignalQuality;
                kind = 1; bars = barsOf(q); wifiBarsSeen = bars;
                WlanFreeMemory(ca);
            }
        }
        WlanFreeMemory(l);
    }
    if (!kind) {  // ¿cable? (un adaptador activo con puerta de enlace)
        ULONG sz = 16384; std::vector<BYTE> buf(sz);
        ULONG fl = GAA_FLAG_INCLUDE_GATEWAYS | GAA_FLAG_SKIP_ANYCAST | GAA_FLAG_SKIP_MULTICAST | GAA_FLAG_SKIP_DNS_SERVER;
        ULONG r = GetAdaptersAddresses(AF_UNSPEC, fl, nullptr, (PIP_ADAPTER_ADDRESSES)buf.data(), &sz);
        if (r == ERROR_BUFFER_OVERFLOW) { buf.resize(sz); r = GetAdaptersAddresses(AF_UNSPEC, fl, nullptr, (PIP_ADAPTER_ADDRESSES)buf.data(), &sz); }
        if (r == NO_ERROR)
            for (auto a = (PIP_ADAPTER_ADDRESSES)buf.data(); a; a = a->Next)
                if (a->OperStatus == IfOperStatusUp && a->FirstGatewayAddress && a->IfType != IF_TYPE_SOFTWARE_LOOPBACK) {
                    kind = a->IfType == IF_TYPE_IEEE80211 ? 1 : 2; bars = 4; break;
                }
    }
    if (kind == netKind && bars == netBars) return false;
    netKind = kind; netBars = bars; return true;
}
static void netInit() {
    DWORD ver = 0;
    if (WlanOpenHandle(2, nullptr, &ver, &wlanH) == ERROR_SUCCESS)
        WlanRegisterNotification(wlanH, WLAN_NOTIFICATION_SOURCE_ACM | WLAN_NOTIFICATION_SOURCE_MSM, TRUE, wlanNotify, nullptr, nullptr, nullptr);
    else wlanH = nullptr;
    HANDLE nh = nullptr; NotifyIpInterfaceChange(AF_UNSPEC, ipChange, nullptr, FALSE, &nh);
    refreshNet();
}

// ---------------------------------------------------------------- wifi y bluetooth (listas en Controles, como en la barra de tareas)
static bool wifiOpen = false, btOpen = false; static int listScroll = 0;
struct WNet { std::wstring ssid, profile; int q = 0; bool sec = false, conn = false, prof = false; DOT11_BSS_TYPE bss = dot11_BSS_type_infrastructure; };
static std::vector<WNet> nets; static std::wstring netBusy; static ULONGLONG netBusyAt = 0;  // red a la que se está conectando
static bool wifiGuid(GUID* g) {
    PWLAN_INTERFACE_INFO_LIST l = nullptr; bool ok = false;
    if (wlanH && WlanEnumInterfaces(wlanH, nullptr, &l) == ERROR_SUCCESS) {
        if (l->dwNumberOfItems) { *g = l->InterfaceInfo[0].InterfaceGuid; ok = true; }
        WlanFreeMemory(l);
    }
    return ok;
}
static std::wstring ssidStr(const DOT11_SSID& s) {
    int n = MultiByteToWideChar(CP_UTF8, 0, (const char*)s.ucSSID, (int)s.uSSIDLength, nullptr, 0);
    std::wstring w(n, 0); if (n) MultiByteToWideChar(CP_UTF8, 0, (const char*)s.ucSSID, (int)s.uSSIDLength, &w[0], n);
    return w;
}
static void netList() {
    nets.clear(); GUID g; if (!wifiGuid(&g)) return;
    PWLAN_AVAILABLE_NETWORK_LIST nl = nullptr;
    if (WlanGetAvailableNetworkList(wlanH, &g, 0, nullptr, &nl) != ERROR_SUCCESS) return;
    for (DWORD i = 0; i < nl->dwNumberOfItems; i++) {  // una fila por nombre de red (Windows repite la que tiene perfil guardado)
        const WLAN_AVAILABLE_NETWORK& a = nl->Network[i];
        std::wstring ss = ssidStr(a.dot11Ssid); if (ss.empty()) continue;
        auto it = std::find_if(nets.begin(), nets.end(), [&](const WNet& n) { return n.ssid == ss; });
        if (it == nets.end()) { nets.push_back(WNet()); it = nets.end() - 1; it->ssid = ss; it->bss = a.dot11BssType; }
        it->q = std::max(it->q, (int)a.wlanSignalQuality);
        it->sec = it->sec || a.bSecurityEnabled;
        bool c = (a.dwFlags & WLAN_AVAILABLE_NETWORK_CONNECTED) != 0;
        if (c) it->conn = true;
        if ((a.dwFlags & WLAN_AVAILABLE_NETWORK_HAS_PROFILE) && a.strProfileName[0] && (it->profile.empty() || c)) { it->prof = true; it->profile = a.strProfileName; }
    }
    WlanFreeMemory(nl);
    std::stable_sort(nets.begin(), nets.end(), [](const WNet& a, const WNet& b) { if (a.conn != b.conn) return a.conn; if (a.prof != b.prof) return a.prof; return a.q > b.q; });
    for (auto& n : nets) if (n.conn && n.ssid == netBusy) netBusy.clear();
    if (!netBusy.empty() && GetTickCount64() - netBusyAt > 20000) netBusy.clear();
}
static void netScan() { GUID g; if (wifiGuid(&g)) WlanScan(wlanH, &g, nullptr, nullptr, nullptr); }
// false si hay que pedir la contraseña: eso lo hace el panel de redes de Windows
static bool netConnect(int i) {
    if (i < 0 || i >= (int)nets.size() || nets[i].conn) return true;
    WNet& n = nets[i];
    if (!n.prof) { ShellExecuteW(nullptr, L"open", L"ms-availablenetworks:", nullptr, nullptr, SW_SHOWNORMAL); return false; }
    GUID g; if (!wifiGuid(&g)) return true;
    WLAN_CONNECTION_PARAMETERS cp{}; cp.wlanConnectionMode = wlan_connection_mode_profile; cp.strProfile = n.profile.c_str(); cp.dot11BssType = n.bss;
    if (WlanConnect(wlanH, &g, &cp, nullptr) == ERROR_SUCCESS) { netBusy = n.ssid; netBusyAt = GetTickCount64(); }
    return true;
}
static void netDisconnect() { GUID g; if (wifiGuid(&g)) WlanDisconnect(wlanH, &g, nullptr); }

// Bluetooth: los emparejados. Los de audio se conectan y desconectan como el botón "Conectar" de Configuración:
// pidiéndoselo al controlador de audio Bluetooth del dispositivo (propiedad "oneshot reconnect / disconnect").
static const GUID KSCATEGORY_AUDIO_ = {0x6994AD04, 0x93EF, 0x11D0, {0xA3, 0xCC, 0x00, 0xA0, 0xC9, 0x22, 0x31, 0x96}};
static const GUID KSPROPSETID_BtAudio_ = {0x7fa06c40, 0xb8f6, 0x4c7e, {0x85, 0x56, 0xe8, 0xc3, 0x3a, 0x12, 0xe5, 0x4d}};
struct BtDev { std::wstring name, ks; ULONGLONG addr = 0; ULONG cod = 0; bool conn = false; };
static std::vector<BtDev> bts; static ULONGLONG btBusy = 0, btBusyAt = 0; static bool btWant = false;
static void btList() {
    bts.clear();
    BLUETOOTH_DEVICE_SEARCH_PARAMS sp{}; sp.dwSize = sizeof sp;
    sp.fReturnAuthenticated = TRUE; sp.fReturnRemembered = TRUE; sp.fReturnConnected = TRUE;
    BLUETOOTH_DEVICE_INFO di{}; di.dwSize = sizeof di;
    if (HBLUETOOTH_DEVICE_FIND f = BluetoothFindFirstDevice(&sp, &di)) {
        do {
            BtDev d; d.name = di.szName; d.addr = di.Address.ullLong; d.cod = di.ulClassofDevice; d.conn = di.fConnected != FALSE;
            if (!d.name.empty()) bts.push_back(d);
            di = BLUETOOTH_DEVICE_INFO{}; di.dwSize = sizeof di;
        } while (BluetoothFindNextDevice(f, &di));
        BluetoothFindDeviceClose(f);
    }
    // controlador de audio (A2DP) de cada uno, por su dirección en la ruta
    HDEVINFO hd = SetupDiGetClassDevsW(&KSCATEGORY_AUDIO_, nullptr, nullptr, DIGCF_DEVICEINTERFACE | DIGCF_PRESENT);
    if (hd != INVALID_HANDLE_VALUE) {
        SP_DEVICE_INTERFACE_DATA id{}; id.cbSize = sizeof id;
        for (DWORD i = 0; SetupDiEnumDeviceInterfaces(hd, nullptr, &KSCATEGORY_AUDIO_, i, &id); i++) {
            DWORD need = 0; SetupDiGetDeviceInterfaceDetailW(hd, &id, nullptr, 0, &need, nullptr);
            if (need < sizeof(SP_DEVICE_INTERFACE_DETAIL_DATA_W)) continue;
            std::vector<BYTE> buf(need); auto* det = (SP_DEVICE_INTERFACE_DETAIL_DATA_W*)buf.data(); det->cbSize = sizeof(SP_DEVICE_INTERFACE_DETAIL_DATA_W);
            if (!SetupDiGetDeviceInterfaceDetailW(hd, &id, det, need, nullptr, nullptr)) continue;
            std::wstring path = det->DevicePath, lo = lowerW(path);
            if (lo.find(L"bthenum#{0000110b") == std::wstring::npos) continue;
            for (auto& d : bts) { wchar_t a[24]; swprintf(a, 24, L"&%012llx_", d.addr); if (d.ks.empty() && lo.find(a) != std::wstring::npos) d.ks = path; }
        }
        SetupDiDestroyDeviceInfoList(hd);
    }
    std::stable_sort(bts.begin(), bts.end(), [](const BtDev& a, const BtDev& b) { if (a.conn != b.conn) return a.conn; return !a.ks.empty() && b.ks.empty(); });
}
// false si no es de audio: para esos se abre la página de Bluetooth de Windows
static bool btToggle(int i) {
    if (i < 0 || i >= (int)bts.size()) return true;
    BtDev& d = bts[i];
    if (d.ks.empty()) { ShellExecuteW(nullptr, L"open", L"ms-settings:bluetooth", nullptr, nullptr, SW_SHOWNORMAL); return false; }
    if (btBusy) return true;
    btBusy = d.addr; btBusyAt = GetTickCount64(); btWant = !d.conn;
    std::wstring path = d.ks; ULONG op = d.conn ? 1 : 0;  // 0 reconectar, 1 desconectar
    std::thread([path, op] {  // puede tardar unos segundos: fuera del hilo de la isla
        HANDLE h = CreateFileW(path.c_str(), GENERIC_READ | GENERIC_WRITE, FILE_SHARE_READ | FILE_SHARE_WRITE, nullptr, OPEN_EXISTING, FILE_FLAG_OVERLAPPED, nullptr);
        if (h != INVALID_HANDLE_VALUE) {
            struct { GUID Set; ULONG Id, Flags; } prop{KSPROPSETID_BtAudio_, op, 1 /* KSPROPERTY_TYPE_GET */};
            OVERLAPPED ov{}; ov.hEvent = CreateEventW(nullptr, TRUE, FALSE, nullptr); DWORD ret = 0;
            if (!DeviceIoControl(h, 0x2F0003 /* IOCTL_KS_PROPERTY */, &prop, sizeof prop, nullptr, 0, &ret, &ov) && GetLastError() == ERROR_IO_PENDING)
                GetOverlappedResult(h, &ov, &ret, TRUE);
            CloseHandle(ov.hEvent); CloseHandle(h);
        }
        Sleep(700);
        PostMessageW(gHwnd, WM_APP_BTLIST, 0, 0);
    }).detach();
    return true;
}
// encender y apagar el wifi y el Bluetooth: Windows.Devices.Radios, la API de los botones del panel rápido
// de Windows (sin permisos de administrador). Las vtables van a mano, como las de la música:
// IRadioStatics: 6 GetRadiosAsync, 9 RequestAccessAsync. IRadio: 6 SetStateAsync, 9 get_State, 11 get_Kind.
// IVectorView: 6 GetAt, 7 get_Size. Estado: 1 encendido, 2 apagado, 3 desactivado. Tipo: 1 wifi, 3 Bluetooth.
static const IID IID_RadioStatics_ = {0x5fb6a12e, 0x67cb, 0x46ae, {0xaa, 0xe9, 0x65, 0x91, 0x9f, 0x86, 0xef, 0xf4}};
static std::atomic<int> radioWifi{-1}, radioBt{-1};  // -1 sin saber, 0 apagado, 1 encendido
static std::atomic<bool> radioBusy{false}; static bool radioAsked = false;
static void radioWork(int kind, int setTo) {  // en su propio hilo; setTo: 0 solo leer, 1 encender, 2 apagar
    RoInitialize(RO_INIT_MULTITHREADED);
    HSTRING cls = nullptr; const wchar_t* cn = L"Windows.Devices.Radios.Radio";
    WindowsCreateString(cn, (UINT32)wcslen(cn), &cls);
    void* st = nullptr;
    if (cls && SUCCEEDED(RoGetActivationFactory(cls, IID_RadioStatics_, &st)) && st) {
        if (setTo) { void* op = nullptr; ((bg::FnObj)bg::VT(st)[9])(st, &op); bg::waitAsync(op, 3000); }  // permiso (lo da solo)
        void* op = nullptr; ((bg::FnObj)bg::VT(st)[6])(st, &op);
        void* vv = bg::waitAsync(op, 3000);
        if (vv) {
            UINT n = 0; ((HRESULT(STDMETHODCALLTYPE*)(void*, UINT*))bg::VT(vv)[7])(vv, &n);
            for (UINT i = 0; i < n; i++) {
                void* r = nullptr; ((HRESULT(STDMETHODCALLTYPE*)(void*, UINT, void**))bg::VT(vv)[6])(vv, i, &r);
                if (!r) continue;
                int k = 0, sv = 0; ((bg::FnInt)bg::VT(r)[11])(r, &k); ((bg::FnInt)bg::VT(r)[9])(r, &sv);
                if (setTo && k == kind) {
                    void* o2 = nullptr; ((HRESULT(STDMETHODCALLTYPE*)(void*, int, void**))bg::VT(r)[6])(r, setTo, &o2);
                    bg::waitAsync(o2, 6000);
                    ((bg::FnInt)bg::VT(r)[9])(r, &sv);
                }
                int v = sv == 1 ? 1 : (sv == 2 || sv == 3) ? 0 : -1;
                if (k == 1) radioWifi = v; else if (k == 3) radioBt = v;
                bg::rel(r);
            }
            bg::rel(vv);
        }
        bg::rel(st);
    }
    if (cls) WindowsDeleteString(cls);
    RoUninitialize();
    radioBusy = false;
    PostMessageW(gHwnd, WM_APP_RADIO, 0, 0);
}
static void radioRead() { if (radioBusy.exchange(true)) return; radioAsked = true; std::thread(radioWork, 0, 0).detach(); }
static void radioToggle(int kind) {
    int cur = kind == 1 ? radioWifi.load() : radioBt.load();
    if (cur < 0 || radioBusy.exchange(true)) return;
    std::thread(radioWork, kind, cur ? 2 : 1).detach();
}
static void closeLists() { devOpen = wifiOpen = btOpen = false; gWifiListOpen = false; listScroll = 0; }
static std::atomic<float> volLvl{-1.f}; static std::atomic<bool> volMuted{false};
struct VolCb : IAudioEndpointVolumeCallback {
    HRESULT STDMETHODCALLTYPE QueryInterface(REFIID r, void** pp) override {
        if (r == IID_IUnknown || r == __uuidof(IAudioEndpointVolumeCallback)) { *pp = this; return S_OK; }
        *pp = nullptr; return E_NOINTERFACE;
    }
    ULONG STDMETHODCALLTYPE AddRef() override { return 2; }
    ULONG STDMETHODCALLTYPE Release() override { return 1; }
    HRESULT STDMETHODCALLTYPE OnNotify(PAUDIO_VOLUME_NOTIFICATION_DATA d) override {
        volLvl = d->fMasterVolume; volMuted = d->bMuted != FALSE; PostMessage(gHwnd, WM_APP_VOL, 0, 0); return S_OK;
    }
};
struct DevCb : IMMNotificationClient {
    HRESULT STDMETHODCALLTYPE QueryInterface(REFIID r, void** pp) override {
        if (r == IID_IUnknown || r == __uuidof(IMMNotificationClient)) { *pp = this; return S_OK; }
        *pp = nullptr; return E_NOINTERFACE;
    }
    ULONG STDMETHODCALLTYPE AddRef() override { return 2; }
    ULONG STDMETHODCALLTYPE Release() override { return 1; }
    HRESULT STDMETHODCALLTYPE OnDeviceStateChanged(LPCWSTR, DWORD) override { return S_OK; }
    HRESULT STDMETHODCALLTYPE OnDeviceAdded(LPCWSTR) override { return S_OK; }
    HRESULT STDMETHODCALLTYPE OnDeviceRemoved(LPCWSTR) override { return S_OK; }
    HRESULT STDMETHODCALLTYPE OnDefaultDeviceChanged(EDataFlow f, ERole r, LPCWSTR) override {
        if (f == eRender && r == eConsole) PostMessage(gHwnd, WM_APP_VOLDEV, 0, 0);
        return S_OK;
    }
    HRESULT STDMETHODCALLTYPE OnPropertyValueChanged(LPCWSTR, const PROPERTYKEY) override { return S_OK; }
};
static VolCb volCb; static DevCb devCb;
static IMMDeviceEnumerator* volEnum = nullptr; static IAudioEndpointVolume* volInd = nullptr;
static void volIndInit() {  // altavoz predeterminado (se rehace si cambia, p. ej. al conectar auriculares)
    if (volInd) { volInd->UnregisterControlChangeNotify(&volCb); SafeRelease(volInd); }
    if (!volEnum) {
        if (FAILED(CoCreateInstance(__uuidof(MMDeviceEnumerator), nullptr, CLSCTX_ALL, __uuidof(IMMDeviceEnumerator), (void**)&volEnum))) { volEnum = nullptr; return; }
        volEnum->RegisterEndpointNotificationCallback(&devCb);
    }
    IMMDevice* d = nullptr;
    if (SUCCEEDED(volEnum->GetDefaultAudioEndpoint(eRender, eConsole, &d))) { d->Activate(__uuidof(IAudioEndpointVolume), CLSCTX_ALL, nullptr, (void**)&volInd); d->Release(); }
    if (volInd) {
        volInd->RegisterControlChangeNotify(&volCb);
        float v = 0; BOOL m = FALSE; volInd->GetMasterVolumeLevelScalar(&v); volInd->GetMute(&m);
        volLvl = v; volMuted = m != FALSE;
    } else volLvl = -1.f;
}
static int volIcon() {  // 0 sin dispositivo, 1 silencio, 2..5 nivel
    float v = volLvl; if (v < 0) return 0;
    if (volMuted) return 1;
    return v <= 0.001f ? 2 : v < 0.34f ? 3 : v < 0.67f ? 4 : 5;
}

static bool onAC() { bool ok; auto& ps = powerStatus(&ok); return ok && ps.ACLineStatus == 1; }
static bool hasBattery() { bool ok; auto& ps = powerStatus(&ok); return ok && ps.BatteryFlag != 128 && ps.BatteryFlag != 255 && ps.BatteryLifePercent <= 100; }

// ---- estado (wifi, volumen, bandeja, día, batería): lo enseña la píldora en todos los modos normales
static std::wstring shortDate() {
    SYSTEMTIME st; GetLocalTime(&st);
    return std::wstring(DOW[st.wDayOfWeek]) + L" " + std::to_wstring(st.wDay) + L" " + MON[st.wMonth - 1];
}
static float batteryW() { return cfg.battery && hasBattery() ? 24 + 40 + (onAC() ? 10.f : 0.f) : 0.f; }
// ancho de la parte izquierda a partir del centro del icono del wifi
static float statusLeftW() { return shelf.empty() ? 34.f : 64.f; }
// ancho de la parte derecha (día + batería + cafeína)
static float dateW(const std::wstring& d) {
    static std::wstring last; static float w = 0;
    if (d != last) { last = d; w = textWidth(d, fSmall); }
    return w;
}
static float statusRightW() { return batteryW() + dateW(shortDate()) + (caffeine ? 22.f : 0.f); }
// wifi, volumen y bandeja; x = centro del icono del wifi
static void drawStatusLeft(float x, float cy) {
    if (netKind == 1) {
        static const wchar_t* W[5] = {L"", L"", L"", L"", L""};
        col(1, 1, 1, 0.25f); glyph(L"", fIcon, x, cy);
        col(1, 1, 1, 0.85f); glyph(W[std::clamp(netBars, 1, 4)], fIcon, x, cy);
    } else if (netKind == 2) { col(1, 1, 1, 0.85f); glyph(L"", fIcon, x, cy); }
    else { col(1, 1, 1, 0.45f); glyph(L"", fIcon, x, cy); }
    static const wchar_t* V[6] = {L"", L"", L"", L"", L"", L""};
    int vi = volIcon();
    if (vi) { col(1, 1, 1, vi == 1 ? 0.5f : 0.85f); glyph(V[vi], fIcon, x + 22, cy); }
    if (!shelf.empty()) { col(1, 1, 1, 0.55f); glyph(L"", fIcon, x + 46, cy); textN(std::to_wstring(shelf.size()), fTiny, x + 56, cy - 8, 24, 16); }
}
// día, batería y cafeína pegados a la derecha (right = borde derecho)
static void drawStatusRight(float right, float cy) {
    std::wstring d = shortDate();
    if (cfg.battery && hasBattery()) { drawBattery(right - 24, cy); right -= batteryW(); }
    float dwid = dateW(d);
    col(1, 1, 1, 0.55f); text(d, fSmall, right - 90, cy - 9, 90, 18, DWRITE_TEXT_ALIGNMENT_TRAILING);
    if (caffeine) { colC(ACC()); glyph(L"", fIcon, right - dwid - 14, cy); }
}
// lo que ocupa el contador del temporizador o del cronómetro (con o sin horas)
static float counterW(bool hours) { return textWidth(hours ? L"0:00:00" : L"00:00", fTime); }

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
    } else if (mode == PM_CHARGE) {
        SYSTEM_POWER_STATUS ps{}; GetSystemPowerStatus(&ps);
        int pc = ps.BatteryLifePercent <= 100 ? ps.BatteryLifePercent : 0;
        float t = (float)(nowMs() - chargeAt) / 1000.f;
        float in = clampf(t / 0.45f, 0, 1), pop = easeOutBack(in);
        float glow = 0.5f + 0.5f * sinf(t * 5.5f);
        float bx = px + 21;
        colC(GREEN, (0.16f + 0.2f * glow) * in); circle(bx, cy, 10.5f + 2.5f * glow * in);
        colC(GREEN); drawBolt(bx, cy, 17 * pop);
        col(1, 1, 1); text(L"Cargando", fTime, px + 40, cy - 10, 120, 20);
        // la pila se rellena hasta el porcentaje de verdad
        float fill = easeOut(clampf((t - 0.25f) / 0.9f, 0, 1)) * pc / 100.f;
        float rx = px + pw - 16 - 28;
        col(1, 1, 1, 0.45f);
        D2D1_ROUNDED_RECT body{{rx, cy - 6.5f, rx + 25, cy + 6.5f}, 3.6f, 3.6f}; rt->DrawRoundedRectangle(&body, br, 1.2f, nullptr);
        fillRR(rx + 26, cy - 2.5f, 2, 5, 1);
        colC(GREEN); fillRR(rx + 2, cy - 4.5f, 21 * clampf(fill, 0.05f, 1), 9, 2);
        colC(GREEN); textN(std::to_wstring((int)lroundf(fill * 100)) + L" %", fTime, rx - 8 - 70, cy - 10, 70, 20, DWRITE_TEXT_ALIGNMENT_TRAILING);
    } else if (mode == PM_TIMER) {
        col(1, 1, 1); textN(tm, fTime, px + 16, cy - 10, 60, 20);
        ULONGLONG rem = tmRemaining();
        float a = tmState == 2 ? 0.5f : 1.f;
        float rx = px + pw - 16 - 8;
        drawStatusLeft(px + 78, cy);
        drawStatusRight(rx - 14 - counterW(rem >= 3600000) - 16, cy);
        float ga = gA; gA *= a;
        ring(rx, cy, 7.5f, tmDur ? (float)rem / tmDur : 0, timerColor(), 2.4f);
        colC(timerColor()); textN(fmtClock(rem, true), fTime, rx - 14 - 80, cy - 10, 80, 20, DWRITE_TEXT_ALIGNMENT_TRAILING);
        gA = ga;
    } else if (mode == PM_SW) {
        col(1, 1, 1); textN(tm, fTime, px + 16, cy - 10, 60, 20);
        ULONGLONG el = swElapsed();
        drawStatusLeft(px + 78, cy);
        drawStatusRight(px + pw - 16 - 20 - counterW(el >= 3600000) - 16, cy);
        colC(ORANGE); glyph(L"\uE916", fIcon, px + pw - 16 - 7, cy);
        col(1, 1, 1, 0.9f); textN(fmtClock(el, false), fTime, px + pw - 16 - 20 - 80, cy - 10, 80, 20, DWRITE_TEXT_ALIGNMENT_TRAILING);
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
        float bx = px + pw - 14 - 19;
        drawStatusLeft(px + 96, cy);
        float rs = bx - 12, tx = px + 96 + statusLeftW() + 6, tr = rs - statusRightW() - 12;
        drawStatusRight(rs, cy);
        col(1, 1, 1, 0.55f); text(media.title, fSmall, tx, cy - 9, std::max(0.f, tr - tx), 18);
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
        // wifi y volumen, como en la barra de tareas
        drawStatusLeft(px + 78, cy);
        drawStatusRight(px + pw - 15, cy);
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

// ---------------------------------------------------------------- buscador de aplicaciones
static const D2D1_COLOR_F WINBLUE{0.18f, 0.62f, 1.f, 1};
static void winLogo(float cx, float cy, float s, D2D1_COLOR_F c) {
    float g = s * 0.1f, q = (s - g) / 2, x = cx - s / 2, y = cy - s / 2;
    colC(c);
    fillRR(x, y, q, q, 0.8f); fillRR(x + q + g, y, q, q, 0.8f);
    fillRR(x, y + q + g, q, q, 0.8f); fillRR(x + q + g, y + q + g, q, q, 0.8f);
}
static float textWidthTrail(const std::wstring& s, IDWriteTextFormat* f) {
    IDWriteTextLayout* lay = nullptr; float w = 0;
    if (SUCCEEDED(dw->CreateTextLayout(s.c_str(), (UINT32)s.size(), f, 2000, 30, &lay))) { DWRITE_TEXT_METRICS m; lay->GetMetrics(&m); w = m.widthIncludingTrailingWhitespace; lay->Release(); }
    return w;
}
static void drawSearch(float x, float y, float w, float h) {
    beginCard(0, y); card(x, y, w, h);
    // campo de texto
    float fx = x + 12, fy = y + 12, fw = w - 24, fh = 34;
    col(1, 1, 1, 0.09f + 0.03f * hv(H_SRCH)); fillRR(fx, fy, fw, fh, 12);
    winLogo(fx + 19, fy + fh / 2, 13, WINBLUE);
    float tx = fx + 38, tmax = fw - 38 - 200;
    if (sQ.empty()) { col(1, 1, 1, 0.35f); text(L"Buscar aplicaciones", fSearch, tx, fy, tmax, fh); }
    else { col(1, 1, 1); text(sQ, fSearch, tx, fy, tmax, fh); }
    if (sCaret) { float cw = sQ.empty() ? 0 : std::min(textWidthTrail(sQ, fSearch), tmax); colC(ACC()); fillRR(tx + cw + 1, fy + 9, 1.6f, fh - 18, 0.8f); }
    addHit(fx, fy, fw, fh, H_SRCH);
    // resultados en 2 columnas
    const float gx = x + 12, gy = y + 54, colw = (w - 24 - 8) / 2, rh = 37;
    int hoverPin = -1;
    for (int k = 0; k < S_COLS * S_ROWS; k++) {
        int ri = sScroll * S_COLS + k; if (ri >= (int)sRes.size()) break;
        const SApp& a = sApps[sRes[ri]];
        float rx = gx + (k % S_COLS) * (colw + 8), ry = gy + (k / S_COLS) * rh, bh = rh - 3;
        int id = H_SRCH_RES + k, pid = H_SRCH_PIN + k;
        bool sel = ri == sSel; float hh = std::max(hv(id), hv(pid));
        if (hoverId == pid) hoverPin = ri;
        if (sel) { colC(ACC(), 0.3f + 0.08f * hh); fillRR(rx, ry, colw, bh, 10); }
        else if (hh > 0.01f) { col(1, 1, 1, 0.07f * hh); fillRR(rx, ry, colw, bh, 10); }
        auto it = sIcons.find(a.id);
        if (it == sIcons.end()) it = sIcons.emplace(a.id, thumbFor(APPS_PREFIX + a.id, (UINT)lroundf(24 * scale), SIIGBF_ICONONLY | SIIGBF_BIGGERSIZEOK)).first;
        float is = 24, ix = rx + 9, iy = ry + (bh - is) / 2;
        if (it->second) {
            D2D1_SIZE_F bs = it->second->GetSize(); float kk = is / std::max(bs.width, bs.height);
            float dw_ = bs.width * kk, dh_ = bs.height * kk;
            D2D1_RECT_F d{ix + (is - dw_) / 2, iy + (is - dh_) / 2, ix + (is + dw_) / 2, iy + (is + dh_) / 2};
            rt->DrawBitmap(it->second, &d, gA, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR, nullptr);
        } else {
            col(0.3f, 0.3f, 0.32f); fillRR(ix, iy, is, is, 6);
            col(1, 1, 1, 0.9f); text(a.name.substr(0, 1), fSmall, ix, iy, is, is, DWRITE_TEXT_ALIGNMENT_CENTER);
        }
        col(1, 1, 1, 0.92f); text(a.name, fBody, rx + 42, ry, colw - 42 - 40, bh);
        // añadir a los atajos / quitar
        bool pinned = sPinned(a);
        float pcx = rx + colw - 19, pcy = ry + bh / 2, show = pinned ? 1.f : std::max(sel ? 1.f : 0.f, hh);
        if (show > 0.01f) {
            float ph = hv(pid), pk = 1 - 0.1f * prs(pid);
            if (pinned) {
                colC(ACC(), show); circle(pcx, pcy, 10 * pk);
                col(1, 1, 1, show); line(pcx - 4, pcy + 0.3f, pcx - 1.2f, pcy + 3.2f, 1.6f); line(pcx - 1.2f, pcy + 3.2f, pcx + 4.2f, pcy - 3, 1.6f);
            } else {
                col(1, 1, 1, (0.12f + 0.14f * ph) * show); circle(pcx, pcy, 10 * pk);
                col(1, 1, 1, 0.9f * show); line(pcx - 4, pcy, pcx + 4, pcy, 1.6f); line(pcx, pcy - 4, pcx, pcy + 4, 1.6f);
            }
            addHit(pcx - 12, pcy - 12, 24, 24, pid);
        }
        addHit(rx, ry, colw, bh, id);
    }
    // texto a la derecha del campo
    std::wstring info;
    if (!sMsg.empty() && nowMs() - sMsgAt < 2500) info = sMsg;
    else if (hoverPin >= 0) info = sPinned(sApps[sRes[hoverPin]]) ? L"Quitar del dock" : (int)apps.size() >= MAX_APPS ? L"Dock lleno (36)" : L"Fijar en el dock";
    else if (!sLoaded) info = L"Cargando...";
    else info = std::to_wstring(sRes.size()) + (sRes.size() == 1 ? L" app" : L" apps");
    col(1, 1, 1, 0.4f); text(info, fTiny, fx + fw - 190, fy, 176, fh, DWRITE_TEXT_ALIGNMENT_TRAILING);
    if (sLoaded && sRes.empty()) { col(1, 1, 1, 0.4f); text(L"Sin resultados", fSmall, x, gy + 50, w, 20, DWRITE_TEXT_ALIGNMENT_CENTER); }
    // barra de desplazamiento
    int rows = ((int)sRes.size() + S_COLS - 1) / S_COLS;
    if (rows > S_ROWS) {
        float th = S_ROWS * rh - 3, bx = x + w - 6, kh = std::max(18.f, th * S_ROWS / rows), ky = gy + (th - kh) * sScroll / (float)sMaxScroll();
        col(1, 1, 1, 0.18f); fillRR(bx - 1.5f, ky, 3, kh, 1.5f);
    }
}


// ---------------------------------------------------------------- menú de clic derecho de una app del dock (como el de la barra de tareas)
// Los menús del dock se abren hacia arriba desde el icono, dentro de la propia ventana del dock.
enum { CA_NEW, CA_PIN, CA_UNPIN, CA_CLOSE };
static int ctxTile = -1; static D2D1_RECT_F ctxAnchor{}; static std::vector<int> ctxActs; static float ctxTopY = 0;  // arriba del menú (coordenadas del dock)
static const float CTX_W = 212, CTX_RH = 30, CTX_HD = 30, CTX_P = 5;
static std::wstring tileLaunchTarget(const Tile& t, std::wstring* args) {
    if (t.pin >= 0) { if (args) *args = apps[t.pin].args; return apps[t.pin].target; }
    const RunApp& r = running[t.run];
    return r.aumid.empty() ? r.exe : L"shell:AppsFolder\\" + r.aumid;
}
static float ctxBuild() {  // rellena las acciones y devuelve el alto del menú
    ctxActs.clear();
    if (ctxTile < 0 || ctxTile >= (int)tiles.size()) return 0;
    const Tile& t = tiles[ctxTile];
    ctxActs.push_back(CA_NEW);
    if (t.pin >= 0) ctxActs.push_back(CA_UNPIN); else if ((int)apps.size() < MAX_APPS) ctxActs.push_back(CA_PIN);
    if (t.run >= 0) ctxActs.push_back(CA_CLOSE);
    return CTX_HD + ctxActs.size() * CTX_RH + CTX_P;
}
// escala lo que se dibuje después desde (cx, cy): de "from" a 1 según a (0..1)
static void popupBegin(float cx, float cy, float a, float from, D2D1_MATRIX_3X2_F& base) {
    rt->GetTransform(&base);
    float sc = from + (1 - from) * a;
    D2D1_MATRIX_3X2_F m{sc, 0, 0, sc, cx - sc * cx, cy - sc * cy};
    D2D1_MATRIX_3X2_F mb = mmul(m, base); rt->SetTransform(&mb);
}
static void popupCard(float x, float y, float w, float h, float r) {
    for (int i = 3; i >= 1; i--) { col(0, 0, 0, 0.09f); float g = i * 2.5f; fillRR(x - g, y - g + 3, w + 2 * g, h + 2 * g, r + g); }  // sombra
    col(0.14f, 0.14f, 0.15f, 0.97f); fillRR(x, y, w, h, r);
    col(1, 1, 1, 0.12f); D2D1_ROUNDED_RECT rr{{x + 0.5f, y + 0.5f, x + w - 0.5f, y + h - 0.5f}, r, r}; rt->DrawRoundedRectangle(&rr, br, 1, nullptr);
}
static void drawCtx(float dW, float barTop) {
    float h = ctxBuild();
    if (!h) return;
    const Tile& t = tiles[ctxTile];
    float acx = (ctxAnchor.left + ctxAnchor.right) / 2;
    float x = std::clamp(acx - CTX_W / 2, 8.f, dW - 8 - CTX_W), y = barTop - 12 - h;
    ctxTopY = y;
    float a = easeOut(tw(20, 1.f, 20)), ga = gA; gA = ga * a;
    D2D1_MATRIX_3X2_F base; popupBegin(acx, y + h + 8, a, 0.9f, base);  // crece desde el icono
    popupCard(x, y, CTX_W, h, 12);
    if (ID2D1Bitmap* b = tileIcon(t)) { D2D1_RECT_F d{x + 12, y + 7, x + 28, y + 23}; rt->DrawBitmap(b, &d, gA, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR, nullptr); }
    col(1, 1, 1, 0.6f); text(tileName(t), fSmall, x + 34, y + 5, CTX_W - 46, 20);
    col(1, 1, 1, 0.08f); fillRR(x + 8, y + CTX_HD - 1, CTX_W - 16, 1, 0.5f);
    int nw = t.run >= 0 ? (int)running[t.run].wins.size() : 0;
    for (size_t i = 0; i < ctxActs.size(); i++) {
        int id = H_CTX + (int)i, act = ctxActs[i];
        float ry = y + CTX_HD + 2 + i * CTX_RH;
        col(1, 1, 1, 0.1f * hv(id) + 0.06f * prs(id)); fillRR(x + 5, ry, CTX_W - 10, CTX_RH - 2, 8);
        const wchar_t* g = act == CA_NEW ? L"" : act == CA_PIN ? L"" : act == CA_UNPIN ? L"" : L"";
        std::wstring l = act == CA_NEW ? L"Abrir nueva ventana" : act == CA_PIN ? L"Fijar en el dock" : act == CA_UNPIN ? L"Quitar del dock"
                       : nw > 1 ? L"Cerrar todas las ventanas (" + std::to_wstring(nw) + L")" : L"Cerrar ventana";
        D2D1_COLOR_F c = act == CA_CLOSE ? RED : D2D1_COLOR_F{1, 1, 1, 0.9f};
        colC(c, c.a); glyph(g, fIcon, x + 20, ry + (CTX_RH - 2) / 2, 20);
        colC(c, c.a); text(l, fSmall, x + 36, ry, CTX_W - 46, CTX_RH - 2);
        addHit(x + 5, ry, CTX_W - 10, CTX_RH - 2, id);
    }
    rt->SetTransform(&base);
    gA = ga;
}
static void dockAppsChanged();
static void dockRefreshSoon(UINT ms);
static void ctxRun(int item) {
    if (ctxTile < 0 || ctxTile >= (int)tiles.size() || item < 0 || item >= (int)ctxActs.size()) { ctxTile = -1; return; }
    Tile t = tiles[ctxTile]; int act = ctxActs[item];
    ctxTile = -1;
    if (act == CA_NEW) {
        std::wstring args, tg = tileLaunchTarget(t, &args);
        ShellExecuteW(nullptr, L"open", tg.c_str(), args.empty() ? nullptr : args.c_str(), nullptr, SW_SHOWNORMAL);
    } else if (act == CA_PIN) {
        appendAtajo(tileName(t), tileLaunchTarget(t, nullptr)); dockAppsChanged();
    } else if (act == CA_UNPIN) {
        removeAtajo(apps[t.pin].target); dockAppsChanged();
    } else if (act == CA_CLOSE && t.run >= 0) {
        for (HWND w : running[t.run].wins) PostMessage(w, WM_SYSCOMMAND, SC_CLOSE, 0);  // como "Cerrar ventana" de la barra de tareas
        dockRefreshSoon(500);  // las ventanas tardan un poco en cerrarse
    }
}

// ---------------------------------------------------------------- vista previa de ventanas (miniaturas en directo de DWM, como la barra de tareas)
// Va en una ventanita aparte encima del dock: DWM las pinta él solo, sin gastar CPU de islita.
static HWND prevWnd = nullptr;
static std::vector<HWND> prevSrcs; static std::vector<HTHUMBNAIL> prevThumbs; static std::vector<RECT> prevSlots; static std::vector<std::wstring> prevTitles;
static std::vector<HWND> prevPending; static ULONGLONG prevPendingAt = 0;
static bool prevClickable = false; static int prevHot = -1;  // con el menú de clic derecho: se elige una ventana pulsándola
static void dockClosePopups(bool restoreFocus);
static int prevSlotAt(LPARAM lp) {
    POINT pt{(short)LOWORD(lp), (short)HIWORD(lp)};
    for (size_t i = 0; i < prevSlots.size(); i++) {
        RECT r = prevSlots[i]; InflateRect(&r, (int)(6 * scale), (int)(24 * scale));
        if (PtInRect(&r, pt)) return (int)i;
    }
    return -1;
}
static LRESULT CALLBACK prevProc(HWND h, UINT m, WPARAM wp, LPARAM lp) {
    switch (m) {
    case WM_MOUSEACTIVATE: return MA_NOACTIVATE;
    case WM_NCHITTEST: return prevClickable ? HTCLIENT : HTTRANSPARENT;
    case WM_SETCURSOR: SetCursor(LoadCursor(nullptr, prevHot >= 0 ? IDC_HAND : IDC_ARROW)); return TRUE;
    case WM_MOUSEMOVE: {
        int i = prevSlotAt(lp);
        if (i != prevHot) { prevHot = i; InvalidateRect(h, nullptr, FALSE); }
        TRACKMOUSEEVENT t{sizeof t, TME_LEAVE, h, 0}; TrackMouseEvent(&t);
        return 0;
    }
    case WM_MOUSELEAVE: if (prevHot >= 0) { prevHot = -1; InvalidateRect(h, nullptr, FALSE); } return 0;
    case WM_LBUTTONUP: {
        int i = prevSlotAt(lp);
        if (i >= 0 && i < (int)prevSrcs.size()) {
            HWND w = prevSrcs[i];
            dockClosePopups(false);
            if (IsWindow(w)) forceForeground(w);
        }
        return 0;
    }
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC dc = BeginPaint(h, &ps); RECT r; GetClientRect(h, &r);
        HBRUSH b = CreateSolidBrush(RGB(38, 38, 41)); FillRect(dc, &r, b); DeleteObject(b);
        SetBkMode(dc, TRANSPARENT);
        HFONT f = CreateFontW(-(int)(12 * scale), 0, 0, 0, FW_NORMAL, 0, 0, 0, DEFAULT_CHARSET, 0, 0, CLEARTYPE_QUALITY, 0, L"Segoe UI");
        HGDIOBJ o = SelectObject(dc, f);
        for (size_t i = 0; i < prevSrcs.size() && i < prevSlots.size(); i++) {
            const RECT& sl = prevSlots[i];
            if ((int)i == prevHot) {  // la que tiene el ratón: recuadro del color de acento
                D2D1_COLOR_F a = ACC();
                HBRUSH hb = CreateSolidBrush(RGB((int)(a.r * 255), (int)(a.g * 255), (int)(a.b * 255)));
                int g = (int)(4 * scale); RECT fr{sl.left - g, sl.top - g, sl.right + g, sl.bottom + g};
                HRGN outer = CreateRoundRectRgn(fr.left, fr.top, fr.right + 1, fr.bottom + 1, 8, 8), inner = CreateRectRgn(sl.left - 1, sl.top - 1, sl.right + 1, sl.bottom + 1);
                CombineRgn(outer, outer, inner, RGN_DIFF); FillRgn(dc, outer, hb);
                DeleteObject(outer); DeleteObject(inner); DeleteObject(hb);
            }
            if (i < prevTitles.size() && !prevTitles[i].empty()) {  // título encima de cada miniatura
                SetTextColor(dc, RGB(225, 225, 230));
                RECT tr{sl.left, sl.top - (int)(20 * scale), sl.right, sl.top - (int)(4 * scale)};
                DrawTextW(dc, prevTitles[i].c_str(), -1, &tr, DT_LEFT | DT_BOTTOM | DT_SINGLELINE | DT_END_ELLIPSIS | DT_NOPREFIX);
            }
            if (!prevThumbs[i]) {  // minimizada: Windows no la dibuja, así que va su icono
                HWND src = prevSrcs[i]; HICON ic = nullptr; DWORD_PTR res = 0;
                if (SendMessageTimeoutW(src, WM_GETICON, ICON_BIG, 0, SMTO_ABORTIFHUNG, 100, &res)) ic = (HICON)res;
                if (!ic) ic = (HICON)GetClassLongPtrW(src, GCLP_HICON);
                if (!ic) ic = LoadIconW(nullptr, IDI_APPLICATION);
                HBRUSH sb = CreateSolidBrush(RGB(48, 48, 52)); FillRect(dc, &sl, sb); DeleteObject(sb);
                int sz = (int)(36 * scale), cx = (sl.left + sl.right) / 2, cy = (sl.top + sl.bottom) / 2;
                DrawIconEx(dc, cx - sz / 2, cy - sz + (int)(4 * scale), ic, sz, sz, 0, nullptr, DI_NORMAL);
                SetTextColor(dc, RGB(150, 150, 156));
                RECT tr{sl.left, cy + (int)(10 * scale), sl.right, sl.bottom};
                DrawTextW(dc, L"Minimizada", -1, &tr, DT_CENTER | DT_TOP | DT_SINGLELINE);
            }
        }
        SelectObject(dc, o); DeleteObject(f);
        EndPaint(h, &ps); return 0;
    }
    }
    return DefWindowProcW(h, m, wp, lp);
}
static void hidePreview() {
    prevHot = -1;
    for (HTHUMBNAIL t : prevThumbs) if (t) DwmUnregisterThumbnail(t);
    prevThumbs.clear(); prevSrcs.clear(); prevSlots.clear(); prevTitles.clear();
    if (prevWnd) ShowWindow(prevWnd, SW_HIDE);
}
// cx = centro horizontal en pantalla; edge = coordenada de pantalla por encima de la cual va; titles vacío = sin títulos
static void showPreview(const std::vector<HWND>& srcs, const std::vector<std::wstring>& titles, int cx, int edge) {
    if (srcs == prevSrcs && prevWnd && IsWindowVisible(prevWnd)) return;
    hidePreview();
    if (srcs.empty()) return;
    if (!prevWnd) {
        WNDCLASSEXW wc{sizeof wc}; wc.lpfnWndProc = prevProc; wc.hInstance = GetModuleHandleW(nullptr);
        wc.lpszClassName = L"islita_prev"; wc.hCursor = LoadCursorW(nullptr, (LPCWSTR)IDC_ARROW);
        RegisterClassExW(&wc);
        prevWnd = CreateWindowExW(WS_EX_TOPMOST | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE, wc.lpszClassName, L"", WS_POPUP, 0, 0, 0, 0, nullptr, nullptr, wc.hInstance, nullptr);
        if (!prevWnd) return;
        DWORD cp = 2; DwmSetWindowAttribute(prevWnd, 33 /* DWMWA_WINDOW_CORNER_PREFERENCE */, &cp, sizeof cp);  // esquinas redondeadas
    }
    int n = (int)srcs.size();
    bool titled = !titles.empty();
    int pad = (int)(10 * scale), gap = (int)(10 * scale), titleH = titled ? (int)(20 * scale) : 0;
    int monW = mon.right - mon.left;
    float maxW = n == 1 ? 320 * scale : std::min(240 * scale, (monW * 0.85f - 2 * pad - (n - 1) * gap) / n);
    float maxH = n == 1 ? 200 * scale : 150 * scale;
    std::vector<SIZE> sz(n);
    for (int i = 0; i < n; i++) {
        HTHUMBNAIL th = nullptr; SIZE ss{};
        if (IsWindow(srcs[i]) && !IsIconic(srcs[i]) && SUCCEEDED(DwmRegisterThumbnail(prevWnd, srcs[i], &th))) DwmQueryThumbnailSourceSize(th, &ss);
        if (th && ss.cx > 0 && ss.cy > 0) {
            float k = std::min(1.f, std::min(maxW / ss.cx, maxH / ss.cy));
            sz[i] = {std::max(1L, (LONG)(ss.cx * k)), std::max(1L, (LONG)(ss.cy * k))};
        } else {
            if (th) { DwmUnregisterThumbnail(th); th = nullptr; }
            sz[i] = {(LONG)std::min(maxW, 180 * scale), (LONG)std::min(maxH, 110 * scale)};
        }
        prevThumbs.push_back(th);
    }
    int rowH = 0, totW = 2 * pad + (n - 1) * gap;
    for (auto& z : sz) { rowH = std::max(rowH, (int)z.cy); totW += z.cx; }
    int x = pad;
    for (int i = 0; i < n; i++) {
        int top = pad + titleH + (rowH - sz[i].cy) / 2;
        RECT sl{x, top, x + sz[i].cx, top + sz[i].cy};
        prevSlots.push_back(sl);
        if (prevThumbs[i]) {
            DWM_THUMBNAIL_PROPERTIES tp{};
            tp.dwFlags = DWM_TNP_RECTDESTINATION | DWM_TNP_VISIBLE | DWM_TNP_OPACITY | DWM_TNP_SOURCECLIENTAREAONLY;
            tp.rcDestination = sl; tp.fVisible = TRUE; tp.opacity = 255; tp.fSourceClientAreaOnly = FALSE;
            DwmUpdateThumbnailProperties(prevThumbs[i], &tp);
        }
        x += sz[i].cx + gap;
    }
    prevSrcs = srcs; prevTitles = titles;
    int wh = 2 * pad + titleH + rowH;
    int wx = std::clamp(cx - totW / 2, (int)mon.left + 8, (int)mon.right - 8 - totW);
    SetWindowPos(prevWnd, HWND_TOPMOST, wx, edge - (int)(8 * scale) - wh, totW, wh, SWP_NOACTIVATE | SWP_SHOWWINDOW);
    InvalidateRect(prevWnd, nullptr, TRUE);
}

// ---------------------------------------------------------------- carpeta: las ventanas de una app, numeradas (como las carpetas del iPhone)
static int fldTile = -1, fldScroll = 0; static D2D1_RECT_F fldAnchor{}; static std::vector<HWND> fldWins; static HWND fldPrevFg = nullptr;
static const int FLD_ROWS = 6;
static const float FLD_W = 300, FLD_RH = 30, FLD_HD = 32, FLD_P = 6;
static float folderHeight() { return fldTile < 0 ? 0 : FLD_HD + std::min((int)fldWins.size(), FLD_ROWS) * FLD_RH + FLD_P; }
static void grabFocusOf(HWND w);
static void openFolder(int tile, D2D1_RECT_F anchor) {
    const RunApp& r = running[tiles[tile].run];
    fldWins = r.wins;
    std::stable_sort(fldWins.begin(), fldWins.end(), [](HWND a, HWND b) { return winSeq[a] < winSeq[b]; });
    fldTile = tile; fldScroll = 0; twSnap(24, 0); fldAnchor = anchor;
    HWND fg = GetForegroundWindow(); fldPrevFg = fg != dockHwnd ? fg : fgAtOpen;
    grabFocusOf(dockHwnd);  // para poder elegir con el número
}
static void closeFolder(bool restoreFocus) {
    if (fldTile < 0) return;
    fldTile = -1; fldWins.clear(); hidePreview();
    if (restoreFocus && GetForegroundWindow() == dockHwnd && fldPrevFg && IsWindow(fldPrevFg)) SetForegroundWindow(fldPrevFg);
    fldPrevFg = nullptr;
}
static void folderPick(int i) {
    if (i < 0 || i >= (int)fldWins.size()) return;
    HWND w = fldWins[i];
    closeFolder(false);
    if (IsWindow(w)) forceForeground(w); else dockRefreshSoon(100);
}
static std::wstring folderTitle(HWND w, const std::wstring& app) {
    wchar_t b[256]; int n = GetWindowTextW(w, b, 256);
    std::wstring t(b, std::max(n, 0));
    // "Aula Global - Google Chrome" -> "Aula Global": el nombre de la app ya está arriba
    for (const wchar_t* sep : {L" - ", L" — ", L" – "}) {
        std::wstring tail = sep + app;
        if (t.size() > tail.size() && !_wcsicmp(t.c_str() + t.size() - tail.size(), tail.c_str())) { t.resize(t.size() - tail.size()); break; }
    }
    return t;
}
static void drawFolder(float dW, float barTop) {
    if (fldTile < 0 || fldTile >= (int)tiles.size()) return;
    const Tile& t = tiles[fldTile];
    int n = (int)fldWins.size(), rows = std::min(n, FLD_ROWS);
    fldScroll = std::clamp(fldScroll, 0, std::max(0, n - FLD_ROWS));
    float h = folderHeight();
    float acx = (fldAnchor.left + fldAnchor.right) / 2;
    float x = std::clamp(acx - FLD_W / 2, 8.f, dW - 8 - FLD_W), y = barTop - 12 - h;
    float a = easeOut(tw(24, 1.f, 20)), ga = gA; gA = ga * a;
    D2D1_MATRIX_3X2_F base; popupBegin(acx, y + h + 8, a, 0.86f, base);  // crece desde la app
    popupCard(x, y, FLD_W, h, 14);
    std::wstring app = tileName(t);
    if (ID2D1Bitmap* b = tileIcon(t)) { D2D1_RECT_F d{x + 12, y + 8, x + 28, y + 24}; rt->DrawBitmap(b, &d, gA, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR, nullptr); }
    col(1, 1, 1, 0.75f); text(app, fSmall, x + 34, y + 6, FLD_W - 34 - 90, 20);
    col(1, 1, 1, 0.38f); text(std::to_wstring(n) + L" ventanas", fTiny, x + FLD_W - 100, y + 6, 88, 20, DWRITE_TEXT_ALIGNMENT_TRAILING);
    col(1, 1, 1, 0.08f); fillRR(x + 8, y + FLD_HD - 1, FLD_W - 16, 1, 0.5f);
    for (int k = 0; k < rows; k++) {
        int i = fldScroll + k, id = H_FOLD + k;
        HWND w = fldWins[i];
        float ry = y + FLD_HD + 2 + k * FLD_RH;
        col(1, 1, 1, 0.1f * hv(id) + 0.06f * prs(id)); fillRR(x + 5, ry, FLD_W - 10, FLD_RH - 2, 9);
        bool act = w == fgAtOpen, mini = IsIconic(w) != 0;
        // número (con el teclado: pulsarlo abre esa ventana)
        float bx = x + 13, by = ry + (FLD_RH - 2) / 2 - 9;
        if (act) colC(ACC()); else col(1, 1, 1, 0.12f + 0.06f * hv(id));
        fillRR(bx, by, 18, 18, 5.5f);
        col(1, 1, 1, i < 9 ? 0.95f : 0.5f); textN(std::to_wstring(i + 1), fTiny, bx, by, 18, 18, DWRITE_TEXT_ALIGNMENT_CENTER);
        float tw_ = FLD_W - 46 - 12 - (mini ? 68 : 0);
        std::wstring ttl = IsWindow(w) ? folderTitle(w, app) : L"(cerrada)";
        col(1, 1, 1, mini ? 0.5f : 0.92f); text(ttl.empty() ? app : ttl, fSmall, x + 40, ry, tw_, FLD_RH - 2);
        if (mini) { col(1, 1, 1, 0.32f); text(L"minimizada", fTiny, x + FLD_W - 12 - 66, ry, 62, FLD_RH - 2, DWRITE_TEXT_ALIGNMENT_TRAILING); }
        addHit(x + 5, ry, FLD_W - 10, FLD_RH - 2, id);
    }
    if (n > FLD_ROWS) {  // barra de desplazamiento
        float th = rows * FLD_RH - 4, ty = y + FLD_HD + 4, kh = std::max(16.f, th * FLD_ROWS / n), ky = ty + (th - kh) * fldScroll / (float)(n - FLD_ROWS);
        col(1, 1, 1, 0.2f); fillRR(x + FLD_W - 4.5f, ky, 2.5f, kh, 1.25f);
    }
    rt->SetTransform(&base);
    gA = ga;
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
static void listHead(float x, float y, float w, const wchar_t* t) {
    float bx = x + 24, by = y + 21;
    col(1, 1, 1, 0.08f + 0.1f * hv(H_DEV_BACK)); circle(bx, by, 11);
    col(1, 1, 1, 0.85f); glyph(L"", fIcon, bx, by);
    addHit(bx - 13, by - 13, 26, 26, H_DEV_BACK);
    col(1, 1, 1, 0.5f); text(t, fCalHead, x + 42, y + 12, w - 56, 18);
}
static void listRowBg(float x, float ry, float w, float rh, int id, bool cur) {
    col(1, 1, 1, 0.07f * hv(id) + 0.05f * prs(id) + (cur ? 0.08f : 0.f)); fillRR(x + 8, ry, w - 16, rh - 3, 9);
}
static void listMore(float x, float ry, float w, float rh, const wchar_t* t, int id) {
    float cy = ry + (rh - 3) / 2;
    col(1, 1, 1, 0.06f * hv(id)); fillRR(x + 8, ry, w - 16, rh - 3, 9);
    col(1, 1, 1, 0.55f + 0.3f * hv(id)); glyph(L"", fIcon, x + 24, cy); text(t, fSmall, x + 40, cy - 9, w - 54, 18);
    addHit(x + 8, ry, w - 16, rh - 3, id);
}
static void drawControls(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    const float rh = 27; int rows = (int)((h - 46) / rh) - 1;  // la última fila: "Más opciones"
    if (wifiOpen) {
        listHead(x, y, w, L"Wi-Fi");
        int n = (int)nets.size(); listScroll = std::clamp(listScroll, 0, std::max(0, n - rows));
        if (!n) { col(1, 1, 1, 0.4f); text(radioWifi == 0 ? L"El wifi está apagado" : wlanH ? L"Buscando redes..." : L"No hay wifi", fSmall, x, y + 40 + rows * rh / 2 - 9, w, 18, DWRITE_TEXT_ALIGNMENT_CENTER); }
        static const wchar_t* B[4] = {L"", L"", L"", L""};
        for (int r = 0; r < rows && listScroll + r < n; r++) {
            const WNet& nt = nets[listScroll + r]; int id = H_NET + r;
            float ry = y + 40 + r * rh, cy = ry + (rh - 3) / 2, right = x + w - 14;
            listRowBg(x, ry, w, rh, id, nt.conn);
            int bi = nt.q >= 75 ? 3 : nt.q >= 50 ? 2 : nt.q >= 25 ? 1 : 0;
            col(1, 1, 1, 0.25f); glyph(L"", fIcon, x + 24, cy);
            col(1, 1, 1, nt.conn ? 1.f : 0.8f); glyph(B[bi], fIcon, x + 24, cy);
            float nameW = right - (x + 40) - 24;
            if (nt.conn) {  // desconectar
                float dx = right - 8; float dh = hv(H_NET_DISC);
                col(1, 1, 1, 0.1f + 0.12f * dh); circle(dx, cy, 9);
                col(1, 1, 1, 0.75f + 0.25f * dh); glyph(L"", fIcon, dx, cy);
                addHit(dx - 10, cy - 10, 20, 20, H_NET_DISC);
            } else if (nt.ssid == netBusy) {
                colC(ACC()); text(L"Conectando", fTiny, right - 70, cy - 7, 70, 14, DWRITE_TEXT_ALIGNMENT_TRAILING); nameW -= 50;
            } else if (nt.sec) { col(1, 1, 1, 0.4f); glyph(L"", fIcon, right - 8, cy); }
            col(1, 1, 1, nt.conn ? 1.f : 0.85f); text(nt.ssid, fSmall, x + 40, cy - 9, nameW, 18);
            addHit(x + 8, ry, w - 16, rh - 3, id);
        }
        listMore(x, y + 40 + rows * rh, w, rh, L"Más opciones de wifi", H_NET_MORE);
        return;
    }
    if (btOpen) {
        listHead(x, y, w, L"Bluetooth");
        int n = radioBt == 0 ? 0 : (int)bts.size(); listScroll = std::clamp(listScroll, 0, std::max(0, n - rows));
        if (!n && radioBt == 0) { col(1, 1, 1, 0.4f); text(L"El Bluetooth está apagado", fSmall, x, y + 40 + rows * rh / 2 - 9, w, 18, DWRITE_TEXT_ALIGNMENT_CENTER); }
        else if (!n) { col(1, 1, 1, 0.4f); text(L"Nada emparejado", fSmall, x, y + 40 + rows * rh / 2 - 9, w, 18, DWRITE_TEXT_ALIGNMENT_CENTER); }
        for (int r = 0; r < rows && listScroll + r < n; r++) {
            const BtDev& d = bts[listScroll + r]; int id = H_BT + r;
            float ry = y + 40 + r * rh, cy = ry + (rh - 3) / 2, right = x + w - 14;
            listRowBg(x, ry, w, rh, id, d.conn);
            int major = (d.cod >> 8) & 0x1F, minor = (d.cod >> 2) & 0x3F;
            const wchar_t* g = major == 4 ? (minor == 5 || minor == 7 ? L"" : L"") : major == 5 ? L"" : major == 2 ? L"" : major == 1 ? L"" : L"";
            col(1, 1, 1, d.conn ? 0.95f : 0.6f); glyph(g, fIcon, x + 24, cy);
            const wchar_t* st = d.addr == btBusy ? (btWant ? L"Conectando" : L"Desconectando") : d.conn ? L"Conectado" : nullptr;
            float nameW = right - (x + 40);
            if (st) { if (d.addr == btBusy || d.conn) colC(ACC()); float sw = textWidth(st, fTiny); text(st, fTiny, right - sw, cy - 7, sw, 14); nameW -= sw + 6; }
            col(1, 1, 1, d.conn ? 1.f : 0.85f); text(d.name, fSmall, x + 40, cy - 9, nameW, 18);
            addHit(x + 8, ry, w - 16, rh - 3, id);
        }
        listMore(x, y + 40 + rows * rh, w, rh, L"Más opciones de Bluetooth", H_BT_MORE);
        return;
    }
    if (devOpen) {  // lista de salidas de sonido
        float bx = x + 24, by = y + 21;
        col(1, 1, 1, 0.08f + 0.1f * hv(H_DEV_BACK)); circle(bx, by, 11);
        col(1, 1, 1, 0.85f); glyph(L"\uE76B", fIcon, bx, by);
        addHit(bx - 13, by - 13, 26, 26, H_DEV_BACK);
        col(1, 1, 1, 0.5f); text(L"Salida de sonido", fCalHead, x + 42, y + 12, w - 56, 18);
        if (devs.empty()) { col(1, 1, 1, 0.4f); text(L"No hay salidas de sonido", fSmall, x, y + h / 2 - 9, w, 18, DWRITE_TEXT_ALIGNMENT_CENTER); return; }
        const float rh = 27;
        int n = std::min((int)devs.size(), (int)((h - 46) / rh));
        for (int i = 0; i < n; i++) {
            float ry = y + 40 + i * rh, cy = ry + (rh - 3) / 2;
            bool cur = devs[i].id == devCur; int id = H_DEV + i;
            col(1, 1, 1, 0.07f * hv(id) + 0.05f * prs(id) + (cur ? 0.08f : 0.f)); fillRR(x + 8, ry, w - 16, rh - 3, 9);
            std::wstring lo = lowerW(devs[i].name);
            auto has = [&](std::initializer_list<const wchar_t*> ws) { for (auto w_ : ws) if (lo.find(w_) != std::wstring::npos) return true; return false; };
            const wchar_t* g = has({L"auricular", L"headphone", L"headset", L"cascos", L"arctis", L"steelseries", L"hyperx", L"airpods", L"buds"}) ? L"\uE7F6"
                             : has({L"hdmi", L"displayport", L"monitor", L"nvidia high definition", L"amd high definition", L"display audio"}) ? L"\uE7F4" : L"\uE7F5";
            col(1, 1, 1, cur ? 0.95f : 0.6f); glyph(g, fIcon, x + 24, cy);
            col(1, 1, 1, cur ? 1.f : 0.8f); text(devs[i].name, fSmall, x + 40, cy - 9, w - 40 - (cur ? 34 : 14), 18);
            if (cur) { colC(ACC()); glyph(L"\uE73E", fIcon, x + w - 26, cy); }
            addHit(x + 8, ry, w - 16, rh - 3, id);
        }
        return;
    }
    cardTitle(L"Controles", x, y, {1, 1, 1, 1}, 0.5f);
    volInit(); briStart();
    bool mute = false; float v = volGet(&mute);
    float vx = x + 14, vw = w - 28;
    // salida de sonido: flechita a la derecha del volumen (como en la barra de tareas)
    float dvx = vx + vw - 13, dvy = y + 51, dh_ = hv(H_DEV_BTN), dk = 1 - 0.1f * prs(H_DEV_BTN);
    col(1, 1, 1, 0.12f + 0.06f * dh_); circle(dvx, dvy, 13 * dk);
    col(1, 1, 1, 0.85f); glyph(L"\uE76C", fIcon, dvx, dvy);
    addHit(dvx - 14, dvy - 15, 28, 30, H_DEV_BTN);
    float svw = vw - 34;
    volRect = {vx, y + 36, vx + svw, y + 66};
    slider(vx, y + 36, svw, 30, mute ? 0 : v, mute || v < 0.01f ? L"\uE74F" : L"\uE767", H_VOL, 11, dragKind == 1, true);
    int b = briCur;
    briRect = {vx, y + 72, vx + vw, y + 102};
    slider(vx, y + 72, vw, 30, b < 0 ? 0 : b / 100.f, L"\uE793", H_BRI, 14, dragKind == 2, briAvail && b >= 0);
    // wifi y bluetooth: abren su lista
    {
        float by2 = y + 110, bw2 = (vw - 8) / 2;
        if (!radioAsked) radioRead();  // estado de las radios: una vez por apertura
        auto pillBtn = [&](float bx, const wchar_t* g, const wchar_t* l, int state, int togId, int listId, int tw_) {
            float hh = std::max(hv(togId), hv(listId)), k = prs(togId);
            float on = tw(tw_, state == 1 ? 1.f : 0.f, 14);
            colC(mix({0.2f + 0.06f * hh, 0.2f + 0.06f * hh, 0.215f + 0.06f * hh, 1}, ACC(), on), 1 - 0.1f * k);
            fillRR(bx, by2, bw2, 28, 11);
            col(1, 1, 1, state == 0 ? 0.6f : 1.f); glyph(g, fIcon, bx + 13, by2 + 14);
            text(l, fTiny, bx + 23, by2 + 7, bw2 - 23 - 19, 14);
            col(1, 1, 1, 0.25f); fillRR(bx + bw2 - 19, by2 + 7, 1, 14, 0.5f);  // separador: botón | lista
            col(1, 1, 1, 0.6f + 0.4f * hv(listId)); glyph(L"\uE76C", fIcon, bx + bw2 - 10, by2 + 14);
            addHit(bx + bw2 - 19, by2, 19, 28, listId);
            addHit(bx, by2, bw2 - 19, 28, togId);
        };
        pillBtn(vx, netKind == 2 ? L"\uE839" : L"\uE701", L"Wi-Fi", radioWifi, H_NET_TOG, H_NET_BTN, 22);
        pillBtn(vx + bw2 + 8, L"\uE702", L"Bluetooth", radioBt, H_BT_TOG, H_BT_BTN, 23);
    }
    struct Q { const wchar_t* g; const wchar_t* l; bool on; } q[4] = {
        {L"\uEC32", L"Cafeína", caffeine}, {mute ? L"\uE74F" : L"\uE767", L"Silencio", mute}, {L"\uE722", L"Captura", false}, {L"\uE72E", L"Bloquear", false}};
    float qy = y + 170, step = (vw - 40) / 3.f;
    for (int i = 0; i < 4; i++) {
        float cx = vx + 20 + i * step; int id = H_Q + i;
        float on = tw(12 + i * 100, q[i].on ? 1.f : 0.f, 14);
        float k = 1 - 0.08f * prs(id), hh = hv(id);
        colC(mix({0.2f + 0.07f * hh, 0.2f + 0.07f * hh, 0.215f + 0.07f * hh, 1}, ACC(), on)); circle(cx, qy, 16 * k);
        col(1, 1, 1); glyph(q[i].g, fIcon, cx, qy);
        col(1, 1, 1, 0.6f); text(q[i].l, fTiny, cx - 30, qy + 18, 60, 14, DWRITE_TEXT_ALIGNMENT_CENTER);
        addHit(cx - 18, qy - 18, 36, 50, id);
    }
    if (caffeine) { colC(ACC(), 0.9f); text(L"Pantalla siempre encendida", fTiny, x + w - 14 - 140, y + 14, 140, 14, DWRITE_TEXT_ALIGNMENT_TRAILING); }
}

// ---------------------------------------------------------------- pestaña Ajustes
static void drawGeneral(float x, float y, float w, float h, int idx) {
    beginCard(idx, y); card(x, y, w, h);
    cardTitle(L"General", x, y, {1, 1, 1, 1}, 0.5f);
    struct R { const wchar_t* l; bool on; int id; } r[7] = {
        {L"Iniciar con Windows", cfg.autostart, H_SET}, {L"Abrir al pasar el ratón", cfg.hoverOpen, H_SET + 1},
        {L"Rayita si hay una ventana debajo", cfg.discreetOn, H_SET + 6}, {L"Ocultar en pantalla completa", cfg.hideFull, H_SET + 2},
        {L"Animar ecualizador", cfg.eq, H_SET + 3}, {L"Mostrar batería", cfg.battery, H_SET + 4},
        {L"Dock en vez de la barra", cfg.hideTaskbar, H_SET + 7}};
    for (int i = 0; i < 7; i++) {
        float ry = y + 42 + i * 24.5f;
        col(1, 1, 1, 0.9f); text(r[i].l, fSmall, x + 16, ry - 9, w - 78, 18);
        switchCtl(x + w - 16 - 42, ry, r[i].on, r[i].id - H_SET, r[i].id);
        addHit(x + 8, ry - 12, w - 16, 24, r[i].id);
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
    button(x + 14, y + 166, w - 28, 28, L"Editar apps del dock", H_EDIT_APPS);
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
    float ti = tw(1, (float)(view >= V_SET ? lastTab : view), 15), ia = tw(5, view >= V_SET ? 0.25f : 1.f, 15);
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
    // buscador de aplicaciones (logo de Windows)
    float wx = qx - 34, wh = hv(H_WIN), kw = 1 - 0.1f * prs(H_WIN), won = tw(18, view == V_SEARCH ? 1.f : 0.f, 14);
    col(1, 1, 1, 0.08f + 0.08f * wh + 0.12f * won); circle(wx, gcy, 13 * kw);
    winLogo(wx, gcy, 11 * kw, mix(WINBLUE, {1, 1, 1, 1}, 0.15f * wh));
    addHit(wx - 14, gcy - 14, 28, 28, H_WIN);
    // apps en segundo plano (la flechita de la bandeja)
    float yx = wx - 34, yh = hv(H_TRAYBTN), ky = 1 - 0.1f * prs(H_TRAYBTN), yon = tw(21, view == V_TRAY ? 1.f : 0.f, 14);
    col(1, 1, 1, 0.08f + 0.08f * yh + 0.12f * yon); circle(yx, gcy, 13 * ky);
    col(1, 1, 1, 0.8f + 0.2f * std::max(yh, yon)); glyph(L"\uE70E", fIcon, yx, gcy - 1);
    addHit(yx - 14, gcy - 14, 28, 28, H_TRAYBTN);
    float lx = yx - 20 - 90;
    if (ch > 0.01f) { col(1, 1, 1, 0.75f * ch); text(L"Claude Code", fTiny, lx, hy, 90, hh, DWRITE_TEXT_ALIGNMENT_TRAILING); }
    else if (wh > 0.01f) { col(1, 1, 1, 0.75f * wh); text(L"Buscar apps", fTiny, lx, hy, 90, hh, DWRITE_TEXT_ALIGNMENT_TRAILING); }
    else if (yh > 0.01f) { col(1, 1, 1, 0.75f * yh); text(L"Segundo plano", fTiny, lx, hy, 90, hh, DWRITE_TEXT_ALIGNMENT_TRAILING); }
    // temporizador en marcha visible desde cualquier pestaña
    else if (tmState == 1 && view != 1) {
        colC(timerColor()); textN(fmtClock(tmRemaining(), true), fTab, lx, hy, 90, hh, DWRITE_TEXT_ALIGNMENT_TRAILING);
    } else if (swRun && view != 1) {
        colC(ORANGE); textN(fmtClock(swElapsed(), false), fTab, lx, hy, 90, hh, DWRITE_TEXT_ALIGNMENT_TRAILING);
    }
}
static void drawTray(float x, float y, float w, float h) {
    beginCard(0, y); card(x, y, w, h);
    const wchar_t* ttl = L"Segundo plano";
    col(1, 1, 1, 0.5f); text(ttl, fCalHead, x + 16, y + 12, 140, 18);
    if (!trayList.empty()) {
        col(1, 1, 1, 0.35f); textN(std::to_wstring(trayList.size()) + (trayList.size() == 1 ? L" app" : L" apps"), fTiny, x + 16 + textWidth(ttl, fCalHead) + 8, y + 12, 120, 18);
        col(1, 1, 1, 0.3f); text(L"Clic derecho: menú de la app", fTiny, x + w - 14 - 240, y + 12, 240, 18, DWRITE_TEXT_ALIGNMENT_TRAILING);
    } else {
        col(1, 1, 1, 0.4f); text(L"Ninguna app en segundo plano", fSmall, x, y + h / 2 - 10, w, 20, DWRITE_TEXT_ALIGNMENT_CENTER);
        return;
    }
    const float tw_ = 82, th = 74, gap = 4;
    int cols = (int)((w - 28 + gap) / (tw_ + gap));
    float x0 = x + 14 + ((w - 28) - (cols * tw_ + (cols - 1) * gap)) / 2, y0 = y + 40;
    int show = std::min((int)trayList.size(), cols * 2);
    for (int i = 0; i < show; i++) {
        const TrayView& t = trayList[i];
        float tx = x0 + (i % cols) * (tw_ + gap), ty = y0 + (i / cols) * (th + gap);
        int id = H_TRAY + i; float hh = hv(id), pp = prs(id);
        col(1, 1, 1, 0.07f * hh + 0.05f * pp); fillRR(tx, ty, tw_, th, 12);
        float s = 32 * (1 - 0.06f * pp), cx = tx + tw_ / 2, cy = ty + 8 + 18;
        auto b = trayBmps.find(t.key);
        if (b != trayBmps.end() && b->second.second) {
            D2D1_RECT_F d{cx - s / 2, cy - s / 2, cx + s / 2, cy + s / 2};
            rt->DrawBitmap(b->second.second, &d, gA, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR, nullptr);
        } else { col(1, 1, 1, 0.4f); circle(cx, cy, 10); }
        col(1, 1, 1, 0.55f + 0.4f * hh); text(t.name, fTiny, tx + 4, ty + th - 24, tw_ - 8, 16, DWRITE_TEXT_ALIGNMENT_CENTER);
        addHit(tx, ty, tw_, th, id);
    }
}
static void drawView(int v, float ox, float y) {
    float h = EH - 44 - 12, x = ox + 12;
    if (v == 0) {
        drawMusic(x, y, 290, h, 0); x += 300;
        drawCalendar(x, y, 236, h, 1); x += 246;
        drawStats(x, y, ox + EW - 12 - x, h, 2);
    } else if (v == V_TOOLS) {
        drawTimer(x, y, 250, h, 0); x += 260;
        drawNextEvent(x, y, 210, h, 1); x += 220;
        drawControls(x, y, ox + EW - 12 - x, h, 2);
    } else if (v == V_SHELF) {
        drawShelf(x, y, EW - 24, h);
    } else if (v == V_SEARCH) {
        drawSearch(x, y, EW - 24, h);
    } else if (v == V_TRAY) {
        drawTray(x, y, EW - 24, h);
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
static std::vector<Hit> cacheHits;  // zonas de clic del panel dentro de la imagen
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
    hitsOn = true; gOpen = 1; gA = 1; gViewA = 1;
    std::vector<Hit> keep; keep.swap(hits);
    drawHeader(0, 0);
    drawView(view, 0, 44);
    rt->EndDraw();
    cacheHits.swap(hits); hits.swap(keep);
    rt = saved; hitsOn = hs; gA = ga;
    cacheValid = true;
}

static void render() {
    if (sActive && (view != V_SEARCH || !expanded)) endSearch(true);  // se salió del buscador por cualquier vía
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
    } else if (chargeOn && !expanded) {
        float t = (float)(nowMs() - chargeAt) / 1000.f;
        float fade = clampf(t / 0.3f, 0, 1) * clampf((CHARGE_MS / 1000.f - t) / 0.5f, 0, 1);
        colC(GREEN, (0.3f + 0.35f * (0.5f + 0.5f * sinf(t * 5.5f))) * fade); rt->DrawRoundedRectangle(&pill, br, 1.5f, nullptr);
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
            // casi abierto: ya se puede pulsar aunque el muelle siga rebotando
            if (expanded && ae > 0.85f)
                for (auto& hh : cacheHits) {
                    auto X = [&](float v) { return s * (v + ox) + cx - s * cx; };
                    auto Y = [&](float v) { return s * (v + py) + py - s * py; };
                    hits.push_back({{X(hh.r.left), Y(hh.r.top), X(hh.r.right), Y(hh.r.bottom)}, hh.id});
                }
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
// Un evento a punto de empezar saca la isla de la rayita solo un rato: 2 min al entrar en los 15 min
// de antes y 1 min más cuando empieza. Un temporizador de un solo disparo la vuelve a encoger (sin sondear).
static bool eventShouts() {
    int em = 0; const CalEvent* e = cfg.alerts ? upcomingEvent(&em) : nullptr;
    if (!e || em > 15) return false;
    static std::wstring key; static ULONGLONG at = 0; static bool started = false;
    std::wstring k = e->title + L"|" + std::to_wstring(e->day) + L"|" + std::to_wstring(e->start);
    ULONGLONG n = nowMs();
    if (k != key) { key = k; at = n; started = em <= 0; }
    else if (em <= 0 && !started) { started = true; at = n; }
    ULONGLONG len = started ? 60000 : 120000;
    if (n - at >= len) return false;
    SetTimer(gHwnd, T_EVSHOW, (UINT)(len - (n - at)) + 50, nullptr);
    return true;
}
static void collapsedTargets() {
    int mode = pillMode();
    bool soon = eventShouts();
    if (discreet && !hovered && !alertOn && !chargeOn && !soon && !peeking) { sw.t = 120; sh.t = 5; sr.t = 2.5f; return; }
    float w = mode == PM_EVENT ? CW_EVENT : mode == PM_MUSIC ? CW_PLAY : mode == PM_ALERT ? 300.f : mode == PM_CHARGE ? 290.f : CW_IDLE, h = CH;
    if (mode == PM_IDLE && !shelf.empty()) w += 30;
    // temporizador, cronómetro y música también llevan el estado (wifi, volumen, día, batería)
    float left = 78 + statusLeftW() + 12;
    if (mode == PM_TIMER) w = std::max(CW_IDLE, left + statusRightW() + 16 + counterW(tmRemaining() >= 3600000) + 38);
    else if (mode == PM_SW) w = std::max(CW_IDLE, left + statusRightW() + 16 + counterW(swElapsed() >= 3600000) + 36);
    else if (mode == PM_MUSIC) w = 96 + statusLeftW() + 6 + 130 + 12 + statusRightW() + 12 + 33;
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
        std::vector<SApp>().swap(sApps); std::vector<int>().swap(sRes); sLoaded = false;
        trayList.clear(); freeTrayBmps(); closeLists(); radioAsked = false; std::vector<AudioDev>().swap(devs); std::vector<WNet>().swap(nets); std::vector<BtDev>().swap(bts);
        if (!dAnim) setEco(true);
        SetCoalescableTimer(gHwnd, T_TRIM, 30000, nullptr, 5000);
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
    if (chargeOn && nowMs() - chargeAt > CHARGE_MS) { chargeOn = false; if (!expanded) collapsedTargets(); }
    render();
    if (springsSettled() && !tweensActive() && !chargeOn) { animating = false; onSettled(); }
}
static void startCharge() {
    if (!visible || expanded || alertOn) return;
    chargeOn = true; chargeAt = nowMs(); lastMode = -1;
    collapsedTargets(); startAnim();
}
static void setExpanded(bool e, int v = -1) {
    if (e == expanded) { if (e && v >= 0 && v != view) { view = v; if (v < V_SET) lastTab = v; render(); } return; }
    expanded = e; cacheValid = false;
    KillTimer(gHwnd, T_COLLAPSE); KillTimer(gHwnd, T_HOVER);
    if (e) {
        gExpandedA = true; chargeOn = false;
        view = v >= 0 ? v : lastTab; if (view < V_SET) lastTab = view;
        twSnap(1, (float)(view == V_SET ? lastTab : view)); twSnap(2, 1.f); shownView = prevView = view; twSnap(5, view == V_SET ? 0.25f : 1.f); twSnap(6, view == V_SET ? 1.f : 0.f);
        SYSTEMTIME st; GetLocalTime(&st); calY = st.wYear; calM = st.wMonth; selDay = 0; twSnap(8, 0);
        FILETIME fs = fileStamp(appsFile);
        if (CompareFileTime(&fs, &appsStamp) != 0) loadApps();
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
    // maximizada (con borde para redimensionar) no es pantalla completa, aunque sin barra de tareas ocupe todo
    if (IsZoomed(fg) && (GetWindowLongPtrW(fg, GWL_STYLE) & WS_THICKFRAME)) return false;
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
    int cx = (mon.left + mon.right) / 2, half = (int)(std::max(CW_EVENT, sw.x) / 2 * scale);
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
    if (trayMenuPid) {
        if (trayMenuActive()) return;
        SetWindowPos(gHwnd, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
    }
    RECT me; GetWindowRect(gHwnd, &me);
    for (HWND a = GetWindow(gHwnd, GW_HWNDPREV); a; a = GetWindow(a, GW_HWNDPREV)) {
        // cualquier ventana visible por delante (Windows a veces deja una normal encima de la isla
        // al traer al frente una maximizada, aunque la isla siga marcada como "siempre encima")
        if (!IsWindowVisible(a) || IsIconic(a)) continue;
        int cloaked = 0; DwmGetWindowAttribute(a, DWMWA_CLOAKED, &cloaked, sizeof cloaked);
        if (cloaked) continue;
        wchar_t cl[32]; GetClassNameW(a, cl, 32);
        if (!wcscmp(cl, L"#32768") || !wcscmp(cl, L"tooltips_class32")) continue;  // menús (p. ej. los de segundo plano) y ayudas: que queden encima
        RECT r, x; GetWindowRect(a, &r);
        if (IntersectRect(&x, &r, &me)) { SetWindowPos(gHwnd, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE); return; }
    }
}
static void CALLBACK winEvent(HWINEVENTHOOK, DWORD, HWND, LONG, LONG, DWORD, DWORD) { checkFullscreen(); if (visible) ensureTopmost(); dockOnForeground(); }

// ================================================================ dock (sustituye a la barra de tareas)
// Barra de apps abajo en el centro, de cristal translúcido, con lupa al pasar el ratón, saltos al abrir una app,
// entradas y salidas animadas y botón de Inicio. Es otra ventana por capas, pero se dibuja con el mismo render
// target de la isla (BindDC a su propia imagen) y solo cuando algo cambia: en reposo no gasta nada.
// Se esconde hacia abajo cuando la ventana activa lo tapa y vuelve al llevar el ratón abajo del todo.
enum { DT_REFRESH = 1, DT_COVER, DT_HIDE, DT_PREVIEW };
enum { D_WIN = 3000, D_ITEM = 3001 };  // zonas de clic del dock: D_ITEM + índice
static const UINT WM_APP_DOCKAPPS = WM_APP + 40;
static const float D_S = 48, D_GAP = 7, D_PAD = 9, D_SEPW = 13, D_BM = 8, D_MAG = 1.6f, D_LABEL = 40, D_R = 20;
static const float D_OP[3] = {0.82f, 0.58f, 0.40f};  // opacidad del fondo según Aspecto > Fondo (sólido, medio, cristal)
struct DockItem {
    std::wstring key, name; ID2D1Bitmap* bmp = nullptr;  // icono con referencia propia: así se puede animar la salida
    int kind = 0;   // 0 app, 1 botón de Inicio, 2 separador
    int tile = -1;  // índice en tiles (-1 mientras se va)
    bool leaving = false;
    float vis = 0, dot = 0, hov = 0, prs = 0;     // animaciones
    float x = 0, w = 0, top = 0, cx = 0;          // dónde se dibujó (coordenadas del dock)
    ULONGLONG bounceAt = 0; int bounceKind = 0; float bounceEnd = 0;  // 1 abriéndose, 2 pide atención
};
static std::vector<DockItem> dItems;
static HDC dDC; static HBITMAP dDib, dOldBmp; static int dDibW = 0, dDibH = 0;
static std::vector<Hit> dHits; static int dHover = H_NONE, dPress = H_NONE; static std::map<int, Tween> dTweens;
static bool dOn = false, dShown = true, dCovered = false, dFull = false, dMouseIn = false, dPendingRefresh = false;
static int hitAt(LPARAM lp);
static Spring dHideS{0, 0, 0};
static float dMag = 0, dMx = 0, dMxT = 0;
static float dW = 0, dH = 0, dRestW = 0, dBarH = 0, dLabelTop = 0, dFolderTop = 0;
static int dWinX = 0, dWinY = 0;
static LARGE_INTEGER dLast; static UINT WM_SHELLHOOK = 0;
static HWINEVENTHOOK dLocHook = nullptr; static DWORD dLocPid = 0; static HWND dWatchFg = nullptr, dPrevFg = nullptr;

// Mientras se dibuja o se atiende el ratón del dock, las zonas de clic, el ratón y las micro-animaciones
// compartidas (hv, prs, tw) son las del dock: así el menú y la carpeta reutilizan el código de la isla.
struct DockCtx {
    float ga; bool hs;
    DockCtx() { hits.swap(dHits); std::swap(hoverId, dHover); std::swap(pressId, dPress); tweens.swap(dTweens); ga = gA; hs = hitsOn; gA = 1; hitsOn = true; }
    ~DockCtx() { hits.swap(dHits); std::swap(hoverId, dHover); std::swap(pressId, dPress); tweens.swap(dTweens); gA = ga; hitsOn = hs; }
};
static float approach(float x, float t, float k, float dt) { x += (t - x) * (1 - expf(-dt * k)); return fabsf(x - t) < 0.002f ? t : x; }

static void dockKick() {
    if (!dOn || !dockHwnd) return;
    if (!dAnim) { dAnim = true; QueryPerformanceCounter(&dLast); setEco(false); }
}
static void dockRefreshSoon(UINT ms) { if (dockHwnd) SetTimer(dockHwnd, DT_REFRESH, ms, nullptr); }
static void dockDropBitmaps() { for (auto& it : dItems) SafeRelease(it.bmp); dockRefreshSoon(20); }
static bool dockPopup() { return ctxTile >= 0 || fldTile >= 0; }

// --- qué hay en el dock
static std::wstring dockKey(const Tile& t) { return t.pin >= 0 ? L"p:" + lowerW(apps[t.pin].target) + L"|" + apps[t.pin].args : L"r:" + running[t.run].key; }
static void dockSync() {
    struct Want { std::wstring key; int kind, tile; };
    std::vector<Want> want;
    want.push_back({L"win", 1, -1});
    want.push_back({L"sep1", 2, -1});
    std::set<std::wstring> seen;
    for (int i = 0; i < (int)tiles.size(); i++) {
        if (i == nPinnedTiles) want.push_back({L"sep2", 2, -1});  // entre las fijadas y las demás abiertas
        std::wstring k = dockKey(tiles[i]);
        while (seen.count(k)) k += L"#";
        seen.insert(k);
        want.push_back({k, 0, i});
    }
    std::vector<DockItem> out; std::vector<bool> used(dItems.size(), false);
    for (auto& w : want) {
        DockItem it; bool found = false;
        for (size_t j = 0; j < dItems.size(); j++)
            if (!used[j] && dItems[j].key == w.key) { it = dItems[j]; used[j] = true; found = true; break; }
        if (!found) { it.key = w.key; it.vis = 0; }
        it.kind = w.kind; it.tile = w.tile; it.leaving = false;
        if (w.kind == 0) {
            const Tile& t = tiles[w.tile];
            it.name = tileName(t);
            ID2D1Bitmap* b = tileIcon(t);
            if (b != it.bmp) { if (b) b->AddRef(); SafeRelease(it.bmp); it.bmp = b; }
        } else if (w.kind == 1) it.name = L"Inicio";
        out.push_back(it);
    }
    // las que ya no están se quedan en su sitio encogiéndose hasta desaparecer
    int pos = -1;
    for (size_t j = 0; j < dItems.size(); j++) {
        if (used[j]) {
            for (size_t k = 0; k < out.size(); k++) if (out[k].key == dItems[j].key) { pos = (int)k; break; }
            continue;
        }
        DockItem g = dItems[j]; g.leaving = true; g.tile = -1; g.bounceAt = 0;
        out.insert(out.begin() + (pos + 1), g); pos++;
    }
    dItems.swap(out);
    if (fldTile >= (int)tiles.size()) fldTile = -1;
    if (ctxTile >= (int)tiles.size()) ctxTile = -1;
}
static void dockRefresh() {
    if (!dOn) return;
    if (dockPopup()) { dPendingRefresh = true; return; }  // con un menú abierto los índices no se tocan
    dPendingRefresh = false;
    FILETIME fs = fileStamp(appsFile);
    if (CompareFileTime(&fs, &appsStamp) != 0) loadApps();
    loadIcons(); refreshTiles(); dockSync(); dockKick();
    SetCoalescableTimer(gHwnd, T_TRIM, 30000, nullptr, 5000);  // devolver la memoria de cargar iconos
}
static void dockAppsChanged() {
    ctxTile = -1; closeFolder(false);
    loadApps(); loadIcons(); dockRefresh();
}

// --- tapado, pantalla completa y visibilidad
static bool dockCovered() {
    HWND fg = GetForegroundWindow();
    if (!fg || fg == dockHwnd || fg == gHwnd || fg == prevWnd) return dCovered;  // sin cambios mientras se usa islita
    if (fg == GetDesktopWindow() || fg == GetShellWindow() || IsIconic(fg) || !IsWindowVisible(fg)) return false;
    wchar_t cls[64]; GetClassNameW(fg, cls, 64);
    if (!wcscmp(cls, L"WorkerW") || !wcscmp(cls, L"Progman") || isTray(fg)) return false;
    int cloaked = 0; DwmGetWindowAttribute(fg, DWMWA_CLOAKED, &cloaked, sizeof cloaked);
    if (cloaked) return false;
    RECT r;
    if (FAILED(DwmGetWindowAttribute(fg, DWMWA_EXTENDED_FRAME_BOUNDS, &r, sizeof r)) && !GetWindowRect(fg, &r)) return false;
    int cx = (mon.left + mon.right) / 2, half = (int)(dRestW / 2 * scale);
    int top = mon.bottom - (int)((D_BM + dBarH) * scale);
    return r.left < cx + half && r.right > cx - half && r.bottom > top && r.top < mon.bottom;
}
static void dockUpdateShown() {
    bool want = !dCovered || dMouseIn || dockPopup();
    if (want == dShown) return;
    dShown = want;
    if (want) SetWindowPos(dockHwnd, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
    else hidePreview();
    dockKick();
}
static void dockCheckCover() {
    if (!dOn || !dockHwnd) return;
    bool full = cfg.hideFull && foregroundIsFullscreen();
    if (full != dFull) {
        dFull = full;
        if (full) { hidePreview(); ShowWindow(dockHwnd, SW_HIDE); }
        else { ShowWindow(dockHwnd, SW_SHOWNOACTIVATE); dockKick(); }
    }
    bool cov = dockCovered();
    if (cov != dCovered) { dCovered = cov; dockUpdateShown(); }
}
// solo se vigila el proceso de la ventana activa: al moverla, maximizarla o restaurarla se mira si tapa el dock
static void CALLBACK dockLocEvent(HWINEVENTHOOK, DWORD, HWND h, LONG obj, LONG child, DWORD, DWORD) {
    if (h && h == dWatchFg && obj == OBJID_WINDOW && child == CHILDID_SELF) SetTimer(dockHwnd, DT_COVER, 40, nullptr);
}
static void dockWatch(HWND fg) {
    dWatchFg = fg;
    DWORD pid = 0; if (fg) GetWindowThreadProcessId(fg, &pid);
    if (pid == dLocPid) return;
    if (dLocHook) { UnhookWinEvent(dLocHook); dLocHook = nullptr; }
    dLocPid = pid;
    if (pid && pid != GetCurrentProcessId())
        dLocHook = SetWinEventHook(EVENT_OBJECT_LOCATIONCHANGE, EVENT_OBJECT_LOCATIONCHANGE, nullptr, dockLocEvent, pid, 0, WINEVENT_OUTOFCONTEXT);
}
static void dockOnForeground() {
    if (!dOn || !dockHwnd) return;
    HWND fg = GetForegroundWindow();
    if (!fg || fg == dockHwnd || fg == gHwnd || fg == prevWnd) return;
    fgAtOpen = fg;
    dockWatch(fg);
    bool known = false;
    for (auto& r : running) if (std::find(r.wins.begin(), r.wins.end(), fg) != r.wins.end()) { known = true; break; }
    if (!known && isTaskWindow(fg)) dockRefreshSoon(60);  // ventana nueva que aún no estaba
    for (auto& it : dItems)  // si pedía atención y ya se ha ido a ella, deja de saltar
        if (it.bounceKind == 2 && it.tile >= 0 && tiles[it.tile].run >= 0) {
            auto& w = running[tiles[it.tile].run].wins;
            if (std::find(w.begin(), w.end(), fg) != w.end()) it.bounceEnd = 0.001f;
        }
    dockCheckCover();
    dockKick();
}

// --- dibujo
static void dockEnsureDib(int w, int h) {
    if (w <= dDibW && h <= dDibH && dDib) return;
    w = std::max(w, dDibW); h = std::max(h, dDibH);
    if (dDib) { SelectObject(dDC, dOldBmp); DeleteObject(dDib); }
    if (!dDC) dDC = CreateCompatibleDC(nullptr);
    BITMAPINFO bi{}; bi.bmiHeader = {sizeof(BITMAPINFOHEADER), w, -h, 1, 32, BI_RGB};
    void* bits; dDib = CreateDIBSection(dDC, &bi, DIB_RGB_COLORS, &bits, nullptr, 0);
    dOldBmp = (HBITMAP)SelectObject(dDC, dDib);
    dDibW = w; dDibH = h;
}
static float dockBounce(DockItem& it, float S) {
    if (!it.bounceAt) return 0;
    const float P = 0.62f;
    float t = (nowMs() - it.bounceAt) / 1000.f, p = fmodf(t, P) / P;
    float hgt = S * (it.bounceKind == 2 ? 0.5f : 0.42f);
    return -hgt * 4 * p * (1 - p);
}
static void dockIcon(DockItem& it, float x, float y, float s, float op) {
    if (it.kind == 1) {  // botón de Inicio: cristal con el logo de Windows
        float r = s * 0.24f;
        col(1, 1, 1, (0.13f + 0.08f * it.hov) * op); fillRR(x, y, s, s, r);
        col(1, 1, 1, 0.16f * op); D2D1_ROUNDED_RECT rr{{x + 0.5f, y + 0.5f, x + s - 0.5f, y + s - 0.5f}, r, r}; rt->DrawRoundedRectangle(&rr, br, 1, nullptr);
        float ga = gA; gA = ga * op;
        winLogo(x + s / 2, y + s / 2, s * 0.44f, mix(WINBLUE, {1, 1, 1, 1}, 0.2f * it.hov));
        gA = ga;
        return;
    }
    op *= 1 - 0.35f * it.prs;  // pulsado: se apaga un poco
    if (it.bmp) { D2D1_RECT_F d{x, y, x + s, y + s}; rt->DrawBitmap(it.bmp, &d, op * gA, D2D1_BITMAP_INTERPOLATION_MODE_LINEAR, nullptr); }
    else {
        col(0.3f, 0.3f, 0.33f, op); fillRR(x, y, s, s, s * 0.22f);
        col(1, 1, 1, 0.9f * op); text(it.name.substr(0, 1), fTitle, x, y, s, s, DWRITE_TEXT_ALIGNMENT_CENTER);
    }
}
static void dockRenderIn() {
    if (!dockHwnd || !rt || !dOn) return;
    hits.clear();
    float monWd = (mon.right - mon.left) / scale;
    // tamaño de los iconos: si no caben, se encogen
    auto baseW = [&](float S) {
        float w = 2 * D_PAD; bool first = true;
        for (auto& it : dItems) { w += (it.kind == 2 ? D_SEPW : S) * it.vis + (first ? 0 : D_GAP * it.vis); first = false; }
        return w;
    };
    float S = D_S, bw = baseW(S);
    if (bw > monWd - 40) { S = std::max(26.f, S * (monWd - 40) / bw); bw = baseW(S); }
    float barH = S + 2 * D_PAD + 4;
    float popH = ctxTile >= 0 ? ctxBuild() : fldTile >= 0 ? folderHeight() : 0;
    float topSpace = std::max(S * (D_MAG - 1) + D_LABEL, popH + 24);
    dW = std::min(monWd, bw + 360); dH = D_BM + barH + topSpace + 8;
    dRestW = bw; dBarH = barH;
    int Wp = (int)ceilf(dW * scale), Hp = (int)ceilf(dH * scale);
    dockEnsureDib(Wp, Hp);
    float hideOff = clampf(dHideS.x, 0, 1.2f) * (barH + D_BM + 14);
    float barTop = dH - D_BM - barH + hideOff, iconBase = barTop + D_PAD + S;
    float cx = dW / 2;

    // posiciones: primero sin lupa (para medir distancias) y luego con ella
    std::vector<float> bc(dItems.size()), sc(dItems.size(), 1.f), ww(dItems.size());
    { float x = cx - bw / 2 + D_PAD; bool first = true;
      for (size_t i = 0; i < dItems.size(); i++) {
          auto& it = dItems[i]; if (!first) x += D_GAP * it.vis; first = false;
          float iw = (it.kind == 2 ? D_SEPW : S) * it.vis; bc[i] = x + iw / 2; x += iw;
      } }
    float R = S * 3.1f, total = 2 * D_PAD;
    for (size_t i = 0; i < dItems.size(); i++) {
        auto& it = dItems[i];
        if (it.kind != 2 && dMag > 0.001f) {
            float d = fabsf(dMx - bc[i]);
            float f = d < R ? 0.5f * (1 + cosf((float)M_PI * d / R)) : 0.f;
            sc[i] = 1 + (D_MAG - 1) * dMag * f;
        }
        ww[i] = (it.kind == 2 ? D_SEPW : S) * it.vis * sc[i];
        total += ww[i] + (i ? D_GAP * it.vis : 0);
    }
    float barL = cx - total / 2, barR = cx + total / 2;

    RECT rc{0, 0, Wp, Hp};
    dcrt->BindDC(dDC, &rc);
    rt->BeginDraw();
    D2D1_COLOR_F clear{0, 0, 0, 0}; rt->Clear(&clear);
    D2D1_MATRIX_3X2_F I{1, 0, 0, 1, 0, 0}; rt->SetTransform(&I);
    gA = 1;
    // franjas casi invisibles que reciben el ratón: el borde de abajo (para hacerlo salir) y, con el ratón dentro,
    // la zona de la lupa (si no, entre dos iconos grandes el ratón "saldría" del dock)
    col(0, 0, 0, 0.004f);
    { D2D1_RECT_F z{cx - bw / 2, dH - (dShown ? D_BM : 2.f), cx + bw / 2, dH}; rt->FillRectangle(&z, br); }
    if (dMouseIn && dHideS.x < 0.5f) { D2D1_RECT_F z{barL, barTop - S * (D_MAG - 1) * dMag - 6, barR, dH}; rt->FillRectangle(&z, br); }

    if (dHideS.x < 1.05f) {
        // sombra suave y cristal
        float r = std::min(D_R, barH / 2);
        for (int i = 4; i >= 1; i--) { float g = i * 3.f; col(0, 0, 0, 0.045f); fillRR(barL - g, barTop - g + 4, total + 2 * g, barH + 2 * g, r + g); }
        col(0.07f, 0.07f, 0.08f, D_OP[cfg.opacity % 3]); fillRR(barL, barTop, total, barH, r);
        col(1, 1, 1, 0.045f); fillRR(barL + 1, barTop + 1, total - 2, barH * 0.48f, r - 1);  // brillo de arriba
        col(0, 0, 0, 0.35f); { D2D1_ROUNDED_RECT o{{barL - 0.5f, barTop - 0.5f, barR + 0.5f, barTop + barH + 0.5f}, r + 0.5f, r + 0.5f}; rt->DrawRoundedRectangle(&o, br, 1, nullptr); }
        col(1, 1, 1, 0.13f); { D2D1_ROUNDED_RECT in{{barL + 0.5f, barTop + 0.5f, barR - 0.5f, barTop + barH - 0.5f}, r - 0.5f, r - 0.5f}; rt->DrawRoundedRectangle(&in, br, 1, nullptr); }

        // iconos (alineados por abajo: al agrandarse crecen hacia arriba, como en el Mac)
        float x = barL + D_PAD; int hoverIdx = -1; dLabelTop = barTop - 30;
        for (size_t i = 0; i < dItems.size(); i++) {
            auto& it = dItems[i];
            if (i) x += D_GAP * it.vis;
            float w = ww[i];
            it.x = x; it.w = w; it.cx = x + w / 2;
            if (it.kind == 2) {
                col(1, 1, 1, 0.2f * it.vis); fillRR(x + w / 2 - 0.6f, barTop + D_PAD + 5, 1.2f, S - 10, 0.6f);
            } else if (it.vis > 0.01f) {
                float s = S * sc[i] * (0.35f + 0.65f * it.vis) * (1 - 0.06f * it.prs);
                float ix = x + (w - s) / 2, iy = iconBase - s + dockBounce(it, S);
                it.top = iy;
                dockIcon(it, ix, iy, s, it.vis);
                // puntito de abierta (del color de acento si es la app activa); uno por ventana, hasta 3
                if (it.dot > 0.01f && it.tile >= 0 && tiles[it.tile].run >= 0) {
                    const RunApp& ra = running[tiles[it.tile].run];
                    bool act = std::find(ra.wins.begin(), ra.wins.end(), fgAtOpen) != ra.wins.end();
                    float dy = barTop + barH - 5.5f, dcx = x + w / 2;
                    int nd = std::min((int)ra.wins.size(), 3);
                    if (act) colC(ACC(), it.dot); else col(1, 1, 1, 0.75f * it.dot);
                    if (nd <= 1) { float dw = (act ? 10.f : 4.f) * it.dot; fillRR(dcx - dw / 2, dy - 2, dw, 4, 2); }
                    else { float gp = 6.f; for (int k = 0; k < nd; k++) circle(dcx + (k - (nd - 1) / 2.f) * gp, dy, 1.9f * it.dot); }
                }
                if (!it.leaving) addHit(x - D_GAP / 2, std::min(iy, iconBase - S) - 4, w + D_GAP, dH - (std::min(iy, iconBase - S) - 4), it.kind == 1 ? D_WIN : D_ITEM + (int)i);
                if (it.hov > 0.01f && !it.leaving && (hoverIdx < 0 || it.hov > dItems[hoverIdx].hov)) hoverIdx = (int)i;
            }
            x += w;
        }
        // nombre encima del icono con el ratón
        if (hoverIdx >= 0 && !dockPopup()) {
            auto& it = dItems[hoverIdx];
            float a = easeOut(it.hov);
            float tw_ = std::min(260.f, textWidth(it.name, fSmall) + 22), th = 26;
            float lx = clampf(it.cx - tw_ / 2, 4, dW - 4 - tw_), ly = it.top - 12 - th + (1 - a) * 5;
            dLabelTop = ly;
            col(0.11f, 0.11f, 0.12f, 0.92f * a); fillRR(lx, ly, tw_, th, 9);
            col(1, 1, 1, 0.12f * a); { D2D1_ROUNDED_RECT rr{{lx + 0.5f, ly + 0.5f, lx + tw_ - 0.5f, ly + th - 0.5f}, 9, 9}; rt->DrawRoundedRectangle(&rr, br, 1, nullptr); }
            col(1, 1, 1, 0.95f * a); text(it.name, fSmall, lx + 11, ly, tw_ - 22, th, DWRITE_TEXT_ALIGNMENT_CENTER);
        }
        // menú o carpeta: van por encima de todo (y sus zonas de clic primero)
        if (dockPopup()) {
            size_t n0 = hits.size();
            if (ctxTile >= 0) drawCtx(dW, barTop);
            else { drawFolder(dW, barTop); dFolderTop = barTop - 12 - folderHeight(); }
            std::rotate(hits.begin(), hits.begin() + n0, hits.end());
        }
    }
    gA = 1;
    if (rt->EndDraw() == D2DERR_RECREATE_TARGET) { createTarget(); return; }
    dWinX = mon.left + ((mon.right - mon.left) - Wp) / 2; dWinY = mon.bottom - Hp;
    POINT dst{dWinX, dWinY}; SIZE sz{Wp, Hp}; POINT src{0, 0};
    BLENDFUNCTION bf{AC_SRC_OVER, 0, 255, AC_SRC_ALPHA};
    UpdateLayeredWindow(dockHwnd, nullptr, &dst, &sz, dDC, &src, 0, &bf, ULW_ALPHA);
}
static void dockRender() { DockCtx c; dockRenderIn(); }

// --- animación: avanza todo y dice si queda algo moviéndose
static bool dockStepIn(float dt) {
    bool busy = false;
    dHideS.t = dShown ? 0.f : 1.f;
    step(dHideS, dt / 1.0f, 190.f, dShown ? 0.72f : 1.f);
    if (!dHideS.settled()) busy = true;
    float magT = dMouseIn && !dockPopup() && dShown ? 1.f : 0.f;
    dMag = approach(dMag, magT, 13, dt); if (dMag != magT) busy = true;
    dMx = approach(dMx, dMxT, 30, dt); if (dMx != dMxT && dMag > 0) busy = true;
    stepTweens(dt); if (tweensActive()) busy = true;
    ULONGLONG now = nowMs();
    for (size_t i = 0; i < dItems.size();) {
        auto& it = dItems[i];
        int id = it.kind == 1 ? D_WIN : D_ITEM + (int)i;
        bool run = it.tile >= 0 && tiles[it.tile].run >= 0;
        float o[4] = {it.vis, it.dot, it.hov, it.prs};
        it.vis = approach(it.vis, it.leaving ? 0.f : 1.f, 9, dt);
        it.dot = approach(it.dot, run && !it.leaving ? 1.f : 0.f, 10, dt);
        it.hov = approach(it.hov, hoverId == id && !dockPopup() ? 1.f : 0.f, 16, dt);
        it.prs = approach(it.prs, pressId == id ? 1.f : 0.f, 30, dt);
        if (o[0] != it.vis || o[1] != it.dot || o[2] != it.hov || o[3] != it.prs) busy = true;
        if (it.bounceAt) {
            const float P = 0.62f; float t = (now - it.bounceAt) / 1000.f;
            // abriéndose: hasta que la app tenga ventana (máx. 8 s); atención: 3 saltos o hasta que se vaya a ella
            if (!it.bounceEnd && ((it.bounceKind == 1 && (run || t > 8)) || (it.bounceKind == 2 && t > 3 * P))) it.bounceEnd = ceilf(t / P) * P;
            if (it.bounceEnd == 0.001f) it.bounceEnd = ceilf(t / P) * P;
            if (it.bounceEnd && t >= it.bounceEnd) { it.bounceAt = 0; it.bounceEnd = 0; it.bounceKind = 0; }
            busy = true;
        }
        if (it.leaving && it.vis <= 0.002f) { SafeRelease(it.bmp); dItems.erase(dItems.begin() + i); busy = true; continue; }
        i++;
    }
    return busy;
}
static void dockPreviewUpdate();
static void dockFrame() {
    LARGE_INTEGER now; QueryPerformanceCounter(&now);
    float dt = clampf((float)(now.QuadPart - dLast.QuadPart) / qpf.QuadPart, 0.001f, 1 / 30.f);
    dLast = now;
    bool busy;
    { DockCtx c; busy = dockStepIn(dt); dockRenderIn(); if (tweensActive()) busy = true; }  // el dibujo puede haber puesto animaciones nuevas (menú, carpeta)
    if (ctxTile >= 0) dockPreviewUpdate();  // miniaturas encima del menú en cuanto acaba de abrirse
    if (!busy) { dAnim = false; if (!animating && !expanded) setEco(true); }
}
static void dockStartBounce(int i, int kind) {
    if (i < 0 || i >= (int)dItems.size()) return;
    auto& it = dItems[i];
    if (it.bounceAt && it.bounceKind >= kind) return;
    it.bounceAt = nowMs(); it.bounceKind = kind; it.bounceEnd = 0;
    dockKick();
}

// --- vista previa de las ventanas de la app con el ratón (o de la fila de la carpeta)
static void dockPreviewUpdate() {
    std::vector<HWND> want; std::vector<std::wstring> titles; int cx = 0, edge = 0; bool clickable = false;
    {
        DockCtx c;
        if (dOn && dShown && dHideS.x < 0.05f) {
            if (ctxTile >= 0 && ctxTile < (int)tiles.size()) {
                const Tile& t = tiles[ctxTile];
                if (t.run >= 0 && tw(20, 1.f, 20) > 0.98f) {
                    want = running[t.run].wins;
                    std::stable_sort(want.begin(), want.end(), [](HWND a, HWND b) { return winSeq[a] < winSeq[b]; });
                    if (want.size() > 8) want.resize(8);
                    std::wstring app = tileName(t);
                    for (HWND w : want) { std::wstring tt = folderTitle(w, app); titles.push_back(tt.empty() ? app : tt); }
                    cx = dWinX + (int)((ctxAnchor.left + ctxAnchor.right) / 2 * scale); edge = dWinY + (int)((ctxTopY - 4) * scale);
                    clickable = true;
                }
            } else if (fldTile >= 0) {
                if (hoverId >= H_FOLD && hoverId < H_FOLD + FLD_ROWS && tw(24, 1.f, 20) > 0.98f) {
                    int i = fldScroll + hoverId - H_FOLD;
                    if (i < (int)fldWins.size())
                        for (auto& ht : hits) if (ht.id == hoverId) { want.push_back(fldWins[i]); cx = dWinX + (int)((ht.r.left + ht.r.right) / 2 * scale); edge = dWinY + (int)(dFolderTop * scale); break; }
                }
            }
        }
    }
    if (want.empty()) { prevPending.clear(); KillTimer(dockHwnd, DT_PREVIEW); if (!prevSrcs.empty()) hidePreview(); return; }
    prevClickable = clickable;
    if (clickable || !prevSrcs.empty()) { showPreview(want, titles, cx, edge); return; }  // menú abierto o ya había una: al momento
    // la primera espera un poco, para que no salte al pasar el ratón de largo
    ULONGLONG now = nowMs();
    if (want != prevPending) { prevPending = want; prevPendingAt = now; }
    if (now - prevPendingAt >= 450) showPreview(want, titles, cx, edge);
    else SetTimer(dockHwnd, DT_PREVIEW, (UINT)(450 - (now - prevPendingAt)) + 15, nullptr);
}

// --- clics
static void dockClosePopups(bool restoreFocus) {
    ctxTile = -1; closeFolder(restoreFocus); hidePreview(); prevClickable = false;
    if (restoreFocus && GetForegroundWindow() == dockHwnd && dPrevFg && IsWindow(dPrevFg)) SetForegroundWindow(dPrevFg);
    dPrevFg = nullptr;
    if (dPendingRefresh) dockRefresh();
    dockUpdateShown(); dockKick();
}
static void dockStartMenu() {
    INPUT in[2]{}; in[0].type = INPUT_KEYBOARD; in[0].ki.wVk = VK_LWIN; in[1] = in[0]; in[1].ki.dwFlags = KEYEVENTF_KEYUP;
    SendInput(2, in, sizeof(INPUT));
}
static void dockClick(int id) {  // fuera de DockCtx
    if (id >= H_CTX && id < H_CTX + 8) {
        HWND back = dPrevFg; int item = id - H_CTX;
        if (GetForegroundWindow() == dockHwnd && back && IsWindow(back)) SetForegroundWindow(back);
        dPrevFg = nullptr;
        ctxRun(item);
        dockClosePopups(false);
        return;
    }
    if (id >= H_FOLD && id < H_FOLD + FLD_ROWS) { folderPick(fldScroll + id - H_FOLD); dockClosePopups(false); return; }
    if (dockPopup()) { dockClosePopups(true); return; }
    if (id == D_WIN) { dockStartMenu(); return; }
    int i = id - D_ITEM;
    if (i < 0 || i >= (int)dItems.size() || dItems[i].tile < 0) return;
    Tile t = tiles[dItems[i].tile];
    HWND fg = GetForegroundWindow(); if (fg != dockHwnd && fg != gHwnd) fgAtOpen = fg;
    if (t.run >= 0 && running[t.run].wins.size() >= 2) {  // varias ventanas: se elige cuál
        hidePreview();
        D2D1_RECT_F a{dItems[i].x, dItems[i].top, dItems[i].x + dItems[i].w, dItems[i].top + dItems[i].w};
        { DockCtx c; openFolder(dItems[i].tile, a); hoverId = H_NONE; }
        dockUpdateShown();
    } else if (t.run >= 0) activateRun(running[t.run]);
    else {
        App& a = apps[t.pin];
        ShellExecuteW(nullptr, L"open", a.target.c_str(), a.args.empty() ? nullptr : a.args.c_str(), nullptr, SW_SHOWNORMAL);
        dockStartBounce(i, 1);
        dockRefreshSoon(1500);
    }
    dockKick();
}

static LRESULT CALLBACK DockProc(HWND h, UINT msg, WPARAM wp, LPARAM lp) {
    if (msg == WM_SHELLHOOK && WM_SHELLHOOK) {
        int code = (int)(wp & 0x7FFF);
        if (code == HSHELL_WINDOWCREATED || code == HSHELL_WINDOWDESTROYED || code == 13 /* HSHELL_WINDOWREPLACED */) dockRefreshSoon(150);
        else if (wp == HSHELL_FLASH) {  // una app pide atención: salta (si no es la activa)
            HWND w = (HWND)lp;
            if (w && w != GetForegroundWindow())
                for (size_t i = 0; i < dItems.size(); i++) {
                    auto& it = dItems[i];
                    if (it.tile < 0 || tiles[it.tile].run < 0) continue;
                    auto& ws = running[tiles[it.tile].run].wins;
                    if (std::find(ws.begin(), ws.end(), w) != ws.end()) { dockStartBounce((int)i, 2); break; }
                }
        }
        return 0;
    }
    switch (msg) {
    case WM_TIMER:
        if (wp == DT_REFRESH) { KillTimer(h, DT_REFRESH); dockRefresh(); }
        else if (wp == DT_COVER) { KillTimer(h, DT_COVER); dockCheckCover(); }
        else if (wp == DT_HIDE) { KillTimer(h, DT_HIDE); dockUpdateShown(); }
        else if (wp == DT_PREVIEW) { KillTimer(h, DT_PREVIEW); dockPreviewUpdate(); }
        return 0;
    case WM_MOUSEMOVE: {
        float x = (short)LOWORD(lp) / scale;
        if (!dMouseIn) {
            dMouseIn = true; dMx = x;
            TRACKMOUSEEVENT t{sizeof t, TME_LEAVE, h, 0}; TrackMouseEvent(&t);
            KillTimer(h, DT_HIDE);
            if (!dShown) dockUpdateShown();
            FILETIME fs = fileStamp(appsFile); if (CompareFileTime(&fs, &appsStamp) != 0) dockRefresh();  // atajos.txt editado a mano
        }
        dMxT = x;        { DockCtx c; int id = hitAt(lp); if (id != hoverId) hoverId = id; }
        dockPreviewUpdate();
        dockKick();
        return 0;
    }
    case WM_MOUSELEAVE:
        dMouseIn = false;
        { DockCtx c; hoverId = H_NONE; }
        if (fldTile < 0) dockPreviewUpdate();
        if (dCovered) SetTimer(h, DT_HIDE, 600, nullptr);
        dockKick();
        return 0;
    case WM_LBUTTONDOWN:
        { DockCtx c; pressId = hitAt(lp); }
        SetCapture(h); if (fldTile < 0) hidePreview(); prevPending.clear();
        dockKick();
        return 0;
    case WM_LBUTTONUP: {
        ReleaseCapture();
        int id, was;
        { DockCtx c; id = hitAt(lp); was = pressId; pressId = H_NONE; }
        if (id && id == was) dockClick(id);
        else if (!id && dockPopup()) dockClosePopups(true);
        dockKick();
        return 0;
    }
    case WM_RBUTTONUP: {
        int id; { DockCtx c; id = hitAt(lp); }
        if (dockPopup()) { dockClosePopups(true); return 0; }
        if (id == D_WIN) {  // clic derecho en Inicio: el buscador de apps de la isla
            setExpanded(true, lastTab); startSearch(); render();
            return 0;
        }
        int i = id - D_ITEM;
        if (i >= 0 && i < (int)dItems.size() && dItems[i].tile >= 0) {
            HWND fg = GetForegroundWindow(); if (fg != dockHwnd && fg != gHwnd) { fgAtOpen = fg; dPrevFg = fg; }
            hidePreview(); prevPending.clear();
            { DockCtx c; ctxTile = dItems[i].tile; ctxAnchor = {dItems[i].x, dItems[i].top, dItems[i].x + dItems[i].w, dItems[i].top + dItems[i].w}; twSnap(20, 0); hoverId = H_NONE; }
            grabFocusOf(h);  // un clic en otro sitio lo cierra
            dockUpdateShown(); dockKick();
        }
        return 0;
    }
    case WM_MBUTTONUP: {  // botón de la rueda: nueva ventana (como en la barra de tareas)
        int id; { DockCtx c; id = hitAt(lp); }
        int i = id - D_ITEM;
        if (i >= 0 && i < (int)dItems.size() && dItems[i].tile >= 0) {
            std::wstring args, tg = tileLaunchTarget(tiles[dItems[i].tile], &args);
            ShellExecuteW(nullptr, L"open", tg.c_str(), args.empty() ? nullptr : args.c_str(), nullptr, SW_SHOWNORMAL);
            dockStartBounce(i, 1); dockRefreshSoon(1500);
        }
        return 0;
    }
    case WM_MOUSEWHEEL:
        if (fldTile >= 0) { int d = GET_WHEEL_DELTA_WPARAM(wp) > 0 ? -1 : 1; fldScroll = std::clamp(fldScroll + d, 0, std::max(0, (int)fldWins.size() - FLD_ROWS)); dockKick(); }
        return 0;
    case WM_KEYDOWN:
        if (fldTile >= 0) {
            if (wp >= '1' && wp <= '9') { folderPick((int)wp - '1'); dockClosePopups(false); }
            else if (wp >= VK_NUMPAD1 && wp <= VK_NUMPAD9) { folderPick((int)(wp - VK_NUMPAD1)); dockClosePopups(false); }
            else if (wp == VK_ESCAPE) dockClosePopups(true);
        } else if (ctxTile >= 0 && wp == VK_ESCAPE) dockClosePopups(true);
        return 0;
    case WM_ACTIVATE:
        if (LOWORD(wp) == WA_INACTIVE && dockPopup()) dockClosePopups(false);  // clic fuera
        return 0;
    case WM_MOUSEACTIVATE: return MA_NOACTIVATE;
    case WM_DISPLAYCHANGE: case WM_DPICHANGED: case WM_SETTINGCHANGE: dockKick(); return 0;
    }
    return DefWindowProcW(h, msg, wp, lp);
}
static void dockApply() {
    dOn = cfg.hideTaskbar && dockHwnd;
    if (!dockHwnd) return;
    if (dOn) {
        dCovered = dockCovered(); dShown = !dCovered; dHideS = {1.f, 0, dShown ? 0.f : 1.f};  // entra desde abajo
        for (auto& it : dItems) it.vis = 0;
        dFull = false;
        ShowWindow(dockHwnd, SW_SHOWNOACTIVATE);
        dockRefresh(); dockOnForeground(); dockKick();
    } else {
        dockClosePopups(false); hidePreview();
        ShowWindow(dockHwnd, SW_HIDE);
        if (dLocHook) { UnhookWinEvent(dLocHook); dLocHook = nullptr; dLocPid = 0; }
    }
}
static void dockInit(HINSTANCE hi) {
    WNDCLASSW wc{}; wc.lpfnWndProc = DockProc; wc.hInstance = hi; wc.lpszClassName = L"islita_dock"; wc.hCursor = LoadCursor(nullptr, IDC_ARROW);
    RegisterClassW(&wc);
    dockHwnd = CreateWindowExW(WS_EX_LAYERED | WS_EX_TOPMOST | WS_EX_TOOLWINDOW | WS_EX_NOACTIVATE, wc.lpszClassName, L"islita dock", WS_POPUP,
                               0, 0, 10, 10, nullptr, nullptr, hi, nullptr);
    WM_SHELLHOOK = RegisterWindowMessageW(L"SHELLHOOK");
    RegisterShellHookWindow(dockHwnd);  // ventanas nuevas, cerradas y que piden atención, sin sondear
    dockApply();
}

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
    else if (id == H_WIN) { if (view == V_SEARCH) view = lastTab; else startSearch(); }
    else if (id == H_DEV_BTN) { closeLists(); devLoad(); devOpen = true; }
    else if (id == H_DEV_BACK) closeLists();
    else if (id == H_NET_BTN) { closeLists(); netList(); netScan(); wifiOpen = true; gWifiListOpen = true; }
    else if (id == H_BT_BTN) { closeLists(); btList(); btOpen = true; }
    else if (id == H_NET_DISC) netDisconnect();
    else if (id == H_NET_TOG) radioToggle(1);
    else if (id == H_BT_TOG) radioToggle(3);
    else if (id >= H_NET && id < H_NET + 12) { if (!netConnect(listScroll + id - H_NET)) { setExpanded(false); return; } }
    else if (id >= H_BT && id < H_BT + 12) { if (!btToggle(listScroll + id - H_BT)) { setExpanded(false); return; } }
    else if (id == H_NET_MORE || id == H_BT_MORE) {
        ShellExecuteW(nullptr, L"open", id == H_NET_MORE ? L"ms-settings:network-wifi" : L"ms-settings:bluetooth", nullptr, nullptr, SW_SHOWNORMAL);
        setExpanded(false); return;
    }
    else if (id >= H_DEV && id < H_DEV + 20) { devSet(id - H_DEV); devOpen = false; }
    else if (id == H_TRAYBTN) { if (view == V_TRAY) view = lastTab; else { trayRefresh(); view = V_TRAY; } }
    else if (id >= H_TRAY && id < H_TRAY + 40) trayClick(id - H_TRAY, false);
    else if (id == H_SRCH) grabFocus();
    else if (id >= H_SRCH_RES && id < H_SRCH_RES + S_COLS * S_ROWS) { sLaunch(sScroll * S_COLS + id - H_SRCH_RES); setExpanded(false); return; }
    else if (id >= H_SRCH_PIN && id < H_SRCH_PIN + S_COLS * S_ROWS) { sSel = sScroll * S_COLS + id - H_SRCH_PIN; sTogglePin(sSel); }
    else if (id == H_SW_R) { if (swRun) { swAcc = swElapsed(); swRun = false; } else { swStart = nowMs(); swRun = true; } }
    else if (id == H_SW_L) { if (swRun) { laps.push_back(swElapsed()); if (laps.size() > 99) laps.erase(laps.begin()); } else { swAcc = 0; laps.clear(); } }
    else if (id == H_Q) setCaffeine(!caffeine);
    else if (id == H_Q + 1) { volInit(); if (vol) { BOOL m = FALSE; vol->GetMute(&m); vol->SetMute(!m, nullptr); if (m) volPop(); } }
    else if (id == H_Q + 2) { setExpanded(false); ShellExecuteW(nullptr, L"open", L"ms-screenclip:", nullptr, nullptr, SW_SHOWNORMAL); return; }
    else if (id == H_Q + 3) { setExpanded(false); LockWorkStation(); return; }
    else if (id == H_SET) { cfg.autostart = !cfg.autostart; setAutostart(cfg.autostart); }
    else if (id == H_SET + 1) cfg.hoverOpen = !cfg.hoverOpen;
    else if (id == H_SET + 2) cfg.hideFull = !cfg.hideFull;
    else if (id == H_SET + 3) cfg.eq = !cfg.eq;
    else if (id == H_SET + 4) cfg.battery = !cfg.battery;
    else if (id == H_SET + 6) { cfg.discreetOn = !cfg.discreetOn; updateDiscreet(); }
    else if (id == H_SET + 7) { cfg.hideTaskbar = !cfg.hideTaskbar; applyTaskbar(); dockApply(); }
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
    if (dragKind == 1) volPop();
    dragKind = 0;
}
static void openFromPill() {
    if (alertOn) { dismissAlert(); setExpanded(true, lastTab); return; }
    int mode = pillMode();
    if (mode == PM_EVENT) {
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
            if (cfg.hideTaskbar) showTrays(false);  // por si se escapó algún aviso
            if (trayWnd && FindWindowW(L"Shell_TrayWnd", nullptr) != trayWnd) trayTopmost();  // los iconos tienen que seguir llegando a islita
            checkFullscreen();
            if (visible) ensureTopmost();
            dockCheckCover();
        } else if (wp == T_COLLAPSE) { KillTimer(h, T_COLLAPSE); if (!sActive) setExpanded(false); }
        else if (wp == T_BTLIST) { KillTimer(h, T_BTLIST); PostMessageW(h, WM_APP_BTLIST, 0, 0); }
        else if (wp == T_PREVIEW) { KillTimer(h, T_PREVIEW); if (!animating) render(); }
        else if (wp == T_EVSHOW) { KillTimer(h, T_EVSHOW); if (!expanded) { collapsedTargets(); startAnim(); } }
        else if (wp == T_CARET) { if (!sActive) { KillTimer(h, T_CARET); return 0; } sCaret = !sCaret; if (!animating) render(); }
        else if (wp == T_PEEK) peekTick();
        else if (wp == T_HOVER) { KillTimer(h, T_HOVER); if (hovered && !expanded) openFromPill(); }
        else if (wp == T_TRIM) { KillTimer(h, T_TRIM); if (!expanded) trimMemory(); }
        return 0;
    case WM_SETCURSOR:
        if (LOWORD(lp) == HTCLIENT) { SetCursor(LoadCursor(nullptr, hoverId == H_SRCH ? IDC_IBEAM : (!expanded || (hoverId && hoverId != H_APPS_CARD)) ? IDC_HAND : IDC_ARROW)); return TRUE; }
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
        if (expanded) { if (!sActive) SetTimer(h, T_COLLAPSE, 450, nullptr); }  // escribiendo en el buscador no se pliega
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
        if (view == V_SEARCH) { sScroll = std::clamp(sScroll + d, 0, sMaxScroll()); render(); return 0; }
        if ((wifiOpen || btOpen) && ((id >= H_NET && id < H_NET + 12) || (id >= H_BT && id < H_BT + 12) || id == H_NET_MORE || id == H_BT_MORE || id == H_NET_DISC)) {
            listScroll = std::max(0, listScroll + d); render(); return 0;
        }
        if (id >= H_PICK && id < H_PICK + 3 && !pomo && tmState == 0) {
            int c = id - H_PICK; auto it = tweens.find(700 + c);
            pickT[c] = roundf(it != tweens.end() ? it->second.t : pickT[c]) + d; updatePick();
        } else if (id == H_VOL && vol) {
            float v = clampf(volGet(nullptr) - d * 0.05f, 0, 1); vol->SetMasterVolumeLevelScalar(v, nullptr); if (v > 0) vol->SetMute(FALSE, nullptr);
            volPop();
        } else if (id == H_BRI && briCur >= 0) briSet(briCur - d * 5);
        render();
        return 0;
    }
    case WM_KEYDOWN: {
        if (!sActive) break;
        int n = (int)sRes.size(); bool ctrl = (GetKeyState(VK_CONTROL) & 0x8000) != 0;
        sCaret = true; SetTimer(h, T_CARET, 530, nullptr);
        switch (wp) {
        case VK_ESCAPE: if (!sQ.empty()) { sQ.clear(); sFilter(); } else view = lastTab; break;
        case VK_RETURN: if (n) { if (ctrl) sTogglePin(sSel); else { sLaunch(sSel); setExpanded(false); return 0; } } break;
        case VK_DOWN: if (n) sSel = std::min(n - 1, sSel + S_COLS); break;
        case VK_UP: if (n) sSel = std::max(0, sSel - S_COLS); break;
        case VK_RIGHT: if (n) sSel = std::min(n - 1, sSel + 1); break;
        case VK_LEFT: if (n) sSel = std::max(0, sSel - 1); break;
        case VK_NEXT: if (n) sSel = std::min(n - 1, sSel + S_COLS * S_ROWS); break;
        case VK_PRIOR: if (n) sSel = std::max(0, sSel - S_COLS * S_ROWS); break;
        default: return 0;
        }
        sEnsureVisible(); render();
        return 0;
    }
    case WM_CHAR: {
        if (!sActive) break;
        wchar_t c = (wchar_t)wp;
        if (c == 8) { if (!sQ.empty()) sQ.pop_back(); }
        else if (c == 127) {  // Ctrl+Retroceso: borra la última palabra
            while (!sQ.empty() && sQ.back() == L' ') sQ.pop_back();
            while (!sQ.empty() && sQ.back() != L' ') sQ.pop_back();
        } else if (c == 22) {  // Ctrl+V
            if (OpenClipboard(h)) {
                if (HANDLE hd = GetClipboardData(CF_UNICODETEXT)) {
                    if (const wchar_t* t = (const wchar_t*)GlobalLock(hd)) {
                        for (; *t && sQ.size() < 80; t++) if (*t >= 32) sQ += *t;
                        GlobalUnlock(hd);
                    }
                }
                CloseClipboard();
            }
        } else if (c >= 32 && sQ.size() < 80) sQ += c;
        else return 0;
        sCaret = true; SetTimer(h, T_CARET, 530, nullptr);
        sFilter(); render();
        return 0;
    }
    case WM_ACTIVATE:
        // se hizo clic en otra ventana mientras se buscaba: se cierra
        if (LOWORD(wp) == WA_INACTIVE && sActive) { endSearch(false); if (!hovered) setExpanded(false); else render(); }
        break;
    case WM_APP_NET:
        if (wifiOpen) { netList(); cacheValid = false; if (!animating) render(); }
        if (refreshNet() && !expanded && !animating) render();
        return 0;
    case WM_APP_RADIO:
        if (wifiOpen) netList();
        if (expanded) { cacheValid = false; if (!animating) render(); }
        return 0;
    case WM_APP_BTLIST:  // tras conectar o desconectar: Windows tarda un poco en reflejarlo, se mira unas veces
        if (btOpen) {
            btList();
            if (btBusy) {
                bool done = false; for (auto& d : bts) if (d.addr == btBusy && d.conn == btWant) done = true;
                if (done || GetTickCount64() - btBusyAt > 12000) btBusy = 0; else SetTimer(h, T_BTLIST, 1200, nullptr);
            }
            cacheValid = false; if (!animating) render();
        } else btBusy = 0;
        return 0;
    case WM_APP_VOL:
        { static int lastVi = -1; int vi = volIcon(); if (vi != lastVi) { lastVi = vi; if (!expanded && !animating) render(); } }
        return 0;
    case WM_APP_VOLDEV:
        volIndInit(); SafeRelease(vol);
        if (devOpen) devLoad();
        if (expanded) cacheValid = false;
        if (!animating) render();
        return 0;
    case WM_APP_APPS:
        if ((unsigned)wp == sGen && expanded) {
            { std::lock_guard<std::mutex> lk(gMx); sApps.swap(gAppsShared); }
            sLoaded = true;
            if (sActive) { sFilter(); if (!animating) render(); }
        }
        { std::lock_guard<std::mutex> lk(gMx); std::vector<SApp>().swap(gAppsShared); }
        return 0;
    case WM_RBUTTONUP:
        if (expanded) {
            int id = hitAt(lp);
            if (id >= H_TRAY && id < H_TRAY + 40) { trayClick(id - H_TRAY, true); setExpanded(false); return 0; }
        }
        if (!expanded) setExpanded(true, V_SET); else { view = V_SET; render(); } return 0;
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
        psAt = 0;  // ha cambiado algo de la batería: se vuelve a consultar
        if (wp == PBT_APMRESUMEAUTOMATIC || wp == PBT_APMRESUMESUSPEND) { scheduleClock(); SetEvent(gWake); }
        {   // cargador enchufado: rayo en la píldora
            SYSTEM_POWER_STATUS ps;
            if (GetSystemPowerStatus(&ps) && ps.ACLineStatus <= 1) {
                if (lastAC == 0 && ps.ACLineStatus == 1 && cfg.battery && hasBattery()) startCharge();
                lastAC = ps.ACLineStatus;
            }
        }
        if (!animating) render();
        return TRUE;
    case WM_APP_TESTCHARGE: startCharge(); return 0;
    case WM_APP_TRAY:
        if (expanded && view == V_TRAY) { trayRefresh(); cacheValid = false; if (!animating) render(); }
        return 0;
    case WM_TIMECHANGE: scheduleClock(); if (!animating) render(); return 0;
    case WM_DISPLAYCHANGE: case WM_DPICHANGED: case WM_SETTINGCHANGE:
        if (msg == WM_DISPLAYCHANGE) gFlushes = 0;  // otra pantalla u otra frecuencia: recalcular
        updateMonitor(); render(); return 0;
    case WM_DESTROY:
        restoreTaskbarOnExit();
        PlaySoundW(nullptr, nullptr, 0); setCaffeine(false); briStop(); RevokeDragDrop(h);
        PostQuitMessage(0); return 0;
    }
    if (msg == WM_TASKBARCREATED && WM_TASKBARCREATED) { applyTaskbar(); return 0; }  // el explorador se ha reiniciado
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
    netInit(); volIndInit(); render();
    WM_TASKBARCREATED = RegisterWindowMessageW(L"TaskbarCreated");
    applyTaskbar();
    dockInit(hi);
    RegisterPowerSettingNotification(gHwnd, &GUID_BATT, DEVICE_NOTIFY_WINDOW_HANDLE);
    RegisterPowerSettingNotification(gHwnd, &GUID_ACDC, DEVICE_NOTIFY_WINDOW_HANDLE);
    { SYSTEM_POWER_STATUS ps; if (GetSystemPowerStatus(&ps) && ps.ACLineStatus <= 1) lastAC = ps.ACLineStatus; }
    std::thread(trayThread).detach();
    SetWinEventHook(EVENT_SYSTEM_FOREGROUND, EVENT_SYSTEM_FOREGROUND, nullptr, winEvent, 0, 0, WINEVENT_OUTOFCONTEXT | WINEVENT_SKIPOWNPROCESS);
    scheduleClock();
    SetCoalescableTimer(gHwnd, T_POLL, 1500, nullptr, 600);

    gWake = CreateEventW(nullptr, FALSE, FALSE, nullptr);
    std::thread worker(bg::run);

    // bucle: en reposo duerme en GetMessage; animando, un fotograma por refresco de pantalla (DwmFlush)
    MSG m;
    for (;;) {
        if (animating || dAnim) {
            bool quit = false;
            while (PeekMessageW(&m, nullptr, 0, 0, PM_REMOVE)) {
                if (m.message == WM_QUIT) { quit = true; break; }
                TranslateMessage(&m); DispatchMessageW(&m);
            }
            if (quit) break;
            if (animating || dAnim) {
                LARGE_INTEGER a, b; QueryPerformanceCounter(&a);
                if (animating) frame();
                if (dAnim) dockFrame();
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
