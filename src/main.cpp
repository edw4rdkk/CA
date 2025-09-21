// arb_cross_all_telegram.cpp
#include <cpr/cpr.h>
#include <nlohmann/json.hpp>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>
#include <iomanip>
#include <algorithm>
#include <thread>
#include <chrono>
#include <fstream>
#include <cctype>
#include <optional>
#include <map>
#include <sstream>

using nlohmann::json;

// ===================== ПАРАМЕТРЫ =====================
static constexpr int HEARTBEAT_INTERVAL_SEC = 300; // каждые 5 минут

static constexpr double MIN_NET_SPREAD_PCT = 2.0;     // минимальный ЧИСТЫЙ спред для показа/рассылки, %
static constexpr int POLL_INTERVAL_SEC = 5;           // период опроса (сек)
static constexpr double MIN_BUY_VOL_USD = 300'000.0;  // мин. суточный оборот у биржи-покупки
static constexpr double MIN_SELL_VOL_USD = 300'000.0; // мин. суточный оборот у биржи-продажи
static constexpr double MAX_REL_INNER_SPREAD = 0.010; // sanity: (ask - bid) / ask > 0.6% — неликвид
static constexpr bool ENABLE_EXPERIMENTAL = true;     // Bitmart/BingX/XT/LBank/CoinEx/Ourbit

// Комиссии (taker). Консервативные 0.20% — подстрой под свой уровень.
static constexpr double FEE_BINANCE = 0.20, FEE_OKX = 0.20, FEE_KUCOIN = 0.20, FEE_BYBIT = 0.20;
static constexpr double FEE_GATE = 0.20, FEE_MEXC = 0.20, FEE_BITGET = 0.20, FEE_HTX = 0.20;
static constexpr double FEE_BITMART = 0.20, FEE_BINGX = 0.20, FEE_XT = 0.20, FEE_LBANK = 0.20;
static constexpr double FEE_COINEX = 0.20, FEE_OURBIT = 0.20;

// ===== 0) Tier-1 + фильтр по ценовому кластеру =====
static const std::unordered_set<std::string> TIER1 = {
    "Binance", "OKX", "Bybit", "KuCoin", "Bitget", "Gate", "MEXC"};
static constexpr double MAX_DEVIATION_FROM_MEDIAN = 0.10; // ±10% к референсу
static constexpr bool REQUIRE_TIER1_INTERSECTION = false; // пара должна быть ≥ на 2 биржах из Tier-1

// ===================== УТИЛИТЫ =====================

static double median(std::vector<double> &v)
{
    if (v.empty())
        return 0.0;
    std::nth_element(v.begin(), v.begin() + v.size() / 2, v.end());
    return v[v.size() / 2];
}

// robust-кластер: Median Absolute Deviation
static double mad(const std::vector<double> &v, double med)
{
    if (v.empty())
        return 0.0;
    std::vector<double> d;
    d.reserve(v.size());
    for (double x : v)
        d.push_back(std::abs(x - med));
    std::nth_element(d.begin(), d.begin() + d.size() / 2, d.end());
    return d[d.size() / 2];
}

static std::string upper(std::string s)
{
    for (char &c : s)
        c = std::toupper((unsigned char)c);
    return s;
}
static bool ends_with(const std::string &s, const std::string &suf)
{
    return s.size() >= suf.size() && std::equal(s.end() - suf.size(), s.end(), suf.begin(), suf.end());
}
static bool is_symbol_leveraged_usdt(const std::string &symbolU)
{
    return ends_with(symbolU, "UPUSDT") || ends_with(symbolU, "DOWNUSDT") || ends_with(symbolU, "BULLUSDT") || ends_with(symbolU, "BEARUSDT");
}
static std::unordered_set<std::string> load_blacklist(const std::string &path = "blacklist.txt")
{
    std::unordered_set<std::string> bl;
    std::ifstream f(path);
    if (!f)
        return bl;
    std::string line;
    while (std::getline(f, line))
    {
        auto pos = line.find('#');
        if (pos != std::string::npos)
            line = line.substr(0, pos);
        std::string token;
        for (char c : line)
            if (!std::isspace((unsigned char)c))
                token.push_back(c);
        if (!token.empty())
            bl.insert(upper(token));
    }
    std::cerr << "[Blacklist] loaded " << bl.size() << " symbols\n";
    return bl;
}

// Ретраи + проверка JSON
static std::optional<json> get_json(const std::string &url,
                                    const cpr::Parameters &params = {},
                                    const cpr::Header &hdr_in = {{"Accept", "application/json"}, {"User-Agent", "arb-scanner/2.0"}, {"Accept-Encoding", "identity"}})
{
    const int max_attempts = 5;
    int backoff_ms = 300;
    for (int attempt = 1; attempt <= max_attempts; ++attempt)
    {
        auto r = cpr::Get(cpr::Url{url}, params, hdr_in, cpr::Timeout{10000});
        if (r.status_code == 200)
        {
            auto it = r.header.find("content-type");
            if (it == r.header.end())
                it = r.header.find("Content-Type");
            bool looks_json = false;
            if (it != r.header.end())
            {
                std::string ct = it->second;
                std::transform(ct.begin(), ct.end(), ct.begin(), ::tolower);
                looks_json = (ct.find("json") != std::string::npos);
            }
            auto j = json::parse(r.text, nullptr, false);
            if (looks_json && !j.is_discarded())
                return j;
            std::cerr << "[JSON] bad body from " << url << " (attempt " << attempt << ")\n";
        }
        else
        {
            std::cerr << "[HTTP] " << url << " -> " << r.status_code
                      << " err: " << r.error.message << " (attempt " << attempt << ")\n";
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(backoff_ms));
        backoff_ms = std::min(backoff_ms * 2, 3000);
    }
    return std::nullopt;
}

// ===================== 1) Quote + ужесточённый add_quote =====================
struct Quote
{
    std::string ex;
    double bid = 0, ask = 0, vol = 0, fee = 0, mid = 0;
};
using Book = std::map<std::string, std::vector<Quote>>;

static void add_quote(Book &book, const std::unordered_set<std::string> &bl,
                      const std::string &baseU, const std::string &exch,
                      double bid, double ask, double vol, double fee)
{
    if (bid <= 0 || ask <= 0)
        return;
    if (bl.count(baseU))
        return;
    double rel = (ask - bid) / ask; // sanity по внутреннему спреду
    if (rel > MAX_REL_INNER_SPREAD)
        return;

    Quote q{exch, bid, ask, vol, fee, (bid + ask) / 2.0};
    book[baseU + "_USDT"].push_back(std::move(q));
}

// ===================== ЛОАДЕРЫ БИРЖ =====================
// Binance
static void load_binance(Book &book, const std::unordered_set<std::string> &bl)
{
    auto jv = get_json("https://api.binance.com/api/v3/ticker/24hr");
    std::unordered_map<std::string, double> vol;
    if (jv && jv->is_array())
    {
        for (auto &t : *jv)
        {
            std::string sym = t.value("symbol", "");
            if (sym.size() < 6 || !ends_with(sym, "USDT"))
                continue;
            auto symU = upper(sym);
            if (is_symbol_leveraged_usdt(symU))
                continue;
            std::string baseU = upper(sym.substr(0, sym.size() - 4));
            try
            {
                vol[baseU] = std::stod(t.value("quoteVolume", "0"));
            }
            catch (...)
            {
            }
        }
    }
    auto jp = get_json("https://api.binance.com/api/v3/ticker/bookTicker");
    if (jp && jp->is_array())
    {
        size_t kept = 0;
        for (auto &t : *jp)
        {
            std::string sym = t.value("symbol", "");
            if (sym.size() < 6 || !ends_with(sym, "USDT"))
                continue;
            auto symU = upper(sym);
            if (is_symbol_leveraged_usdt(symU))
                continue;
            std::string baseU = upper(sym.substr(0, sym.size() - 4));
            try
            {
                double bid = std::stod(t.value("bidPrice", "0"));
                double ask = std::stod(t.value("askPrice", "0"));
                double qv = vol.count(baseU) ? vol[baseU] : 0.0;
                add_quote(book, bl, baseU, "Binance", bid, ask, qv, FEE_BINANCE);
                ++kept;
            }
            catch (...)
            {
            }
        }
        std::cerr << "[Binance] quotes " << kept << "\n";
    }
}

// OKX
static void load_okx(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://www.okx.com/api/v5/market/tickers", {{"instType", "SPOT"}});
    if (!j)
        return;
    auto arr = (*j)["data"];
    if (!arr.is_array())
        return;
    size_t kept = 0;
    for (auto &t : arr)
    {
        std::string inst = t.value("instId", "");
        if (inst.size() < 6 || !ends_with(inst, "USDT"))
            continue; // BTC-USDT
        std::string baseU = upper(inst.substr(0, inst.size() - 5));
        try
        {
            double bid = std::stod(t.value("bidPx", "0"));
            double ask = std::stod(t.value("askPx", "0"));
            double qv = t.contains("volCcy24h") ? std::stod(t.value("volCcy24h", "0")) : 0.0;
            add_quote(book, bl, baseU, "OKX", bid, ask, qv, FEE_OKX);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[OKX] quotes " << kept << "\n";
}

// KuCoin
static void load_kucoin(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://api.kucoin.com/api/v1/market/allTickers");
    if (!j)
        return;
    auto arr = (*j)["data"]["ticker"];
    if (!arr.is_array())
        return;
    size_t kept = 0;
    for (auto &t : arr)
    {
        std::string sym = t.value("symbol", ""); // BTC-USDT
        if (sym.size() < 6 || !ends_with(sym, "USDT"))
            continue;
        std::string baseU = upper(sym.substr(0, sym.size() - 5));
        try
        {
            double bid = std::stod(t.value("bestBidPrice", "0"));
            double ask = std::stod(t.value("bestAskPrice", "0"));
            double qv = std::stod(t.value("volValue", "0"));
            add_quote(book, bl, baseU, "KuCoin", bid, ask, qv, FEE_KUCOIN);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[KuCoin] quotes " << kept << "\n";
}

// Bybit
static void load_bybit(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://api.bybit.com/v5/market/tickers", {{"category", "spot"}});
    if (!j)
        return;
    auto arr = (*j)["result"]["list"];
    if (!arr.is_array())
        return;
    size_t kept = 0;
    for (auto &t : arr)
    {
        std::string sym = t.value("symbol", ""); // BTCUSDT
        if (sym.size() < 6 || !ends_with(sym, "USDT"))
            continue;
        std::string baseU = upper(sym.substr(0, sym.size() - 4));
        try
        {
            double bid = std::stod(t.value("bid1Price", "0"));
            double ask = std::stod(t.value("ask1Price", "0"));
            double qv = std::stod(t.value("turnover24h", "0"));
            add_quote(book, bl, baseU, "Bybit", bid, ask, qv, FEE_BYBIT);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[Bybit] quotes " << kept << "\n";
}

// Gate
static void load_gate(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://api.gateio.ws/api/v4/spot/tickers");
    if (!j || !j->is_array())
        return;
    size_t kept = 0;
    for (auto &t : *j)
    {
        std::string cp = t.value("currency_pair", ""); // BTC_USDT
        if (cp.size() < 6 || !ends_with(cp, "_USDT"))
            continue;
        std::string baseU = upper(cp.substr(0, cp.size() - 5));
        try
        {
            double bid = std::stod(t.value("highest_bid", "0"));
            double ask = std::stod(t.value("lowest_ask", "0"));
            double qv = std::stod(t.value("quote_volume", "0"));
            add_quote(book, bl, baseU, "Gate", bid, ask, qv, FEE_GATE);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[Gate] quotes " << kept << "\n";
}

// MEXC
static void load_mexc(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://api.mexc.com/api/v3/ticker/24hr");
    if (!j || !j->is_array())
        return;
    size_t kept = 0;
    for (auto &t : *j)
    {
        std::string sym = t.value("symbol", ""); // BTCUSDT
        if (sym.size() < 6 || !ends_with(sym, "USDT"))
            continue;
        std::string baseU = upper(sym.substr(0, sym.size() - 4));
        try
        {
            double bid = std::stod(t.value("bidPrice", "0"));
            double ask = std::stod(t.value("askPrice", "0"));
            double qv = std::stod(t.value("quoteVolume", "0"));
            add_quote(book, bl, baseU, "MEXC", bid, ask, qv, FEE_MEXC);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[MEXC] quotes " << kept << "\n";
}

// Bitget
static void load_bitget(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://api.bitget.com/api/spot/v1/market/tickers");
    if (!j)
        return;
    auto arr = (*j)["data"];
    if (!arr.is_array())
        return;
    size_t kept = 0;
    for (auto &t : arr)
    {
        std::string sym = t.value("symbol", "");
        if (sym.empty())
            sym = t.value("instId", "");
        auto symU = upper(sym);
        if (!(ends_with(symU, "USDT") || ends_with(symU, "_USDT")))
            continue;
        std::string baseU = ends_with(symU, "_USDT") ? symU.substr(0, symU.size() - 5)
                                                     : symU.substr(0, symU.size() - 4);
        try
        {
            double bid = 0, ask = 0, qv = 0;
            if (t.contains("buyOne"))
                bid = std::stod(t.value("buyOne", "0"));
            if (t.contains("sellOne"))
                ask = std::stod(t.value("sellOne", "0"));
            if (t.contains("bestBid"))
                bid = std::stod(t.value("bestBid", "0"));
            if (t.contains("bestAsk"))
                ask = std::stod(t.value("bestAsk", "0"));
            if (t.contains("quoteVolume"))
                qv = std::stod(t.value("quoteVolume", "0"));
            add_quote(book, bl, baseU, "Bitget", bid, ask, qv, FEE_BITGET);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[Bitget] quotes " << kept << "\n";
}

// HTX (Huobi)
static void load_htx(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://api.huobi.pro/market/tickers");
    if (!j)
        return;
    auto arr = (*j)["data"];
    if (!arr.is_array())
        return;
    size_t kept = 0;
    for (auto &t : arr)
    {
        std::string sym = t.value("symbol", ""); // btcusdt
        auto symU = upper(sym);
        if (symU.size() < 6 || !ends_with(symU, "USDT"))
            continue;
        std::string baseU = symU.substr(0, symU.size() - 4);
        try
        {
            double bid = t.value("bid", 0.0);
            double ask = t.value("ask", 0.0);
            double qv = 0.0; // объём не всегда доступен
            add_quote(book, bl, baseU, "HTX", bid, ask, qv, FEE_HTX);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[HTX] quotes " << kept << "\n";
}

// ======== Экспериментальные (включаются флагом ENABLE_EXPERIMENTAL) ========
// Bitmart
static void load_bitmart(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://api-cloud.bitmart.com/spot/v1/ticker");
    if (!j)
        return;
    auto arr = (*j)["data"]["tickers"];
    if (!arr.is_array())
        return;
    size_t kept = 0;
    for (auto &t : arr)
    {
        std::string sym = t.value("symbol", ""); // BTC_USDT
        auto symU = upper(sym);
        if (!ends_with(symU, "_USDT"))
            continue;
        std::string baseU = symU.substr(0, symU.size() - 5);
        try
        {
            double bid = std::stod(t.value("best_bid", "0"));
            double ask = std::stod(t.value("best_ask", "0"));
            double qv = std::stod(t.value("quote_volume_24h", "0"));
            add_quote(book, bl, baseU, "Bitmart", bid, ask, qv, FEE_BITMART);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[Bitmart] quotes " << kept << "\n";
}

// // BingX
// static void load_bingx(Book &book, const std::unordered_set<std::string> &bl)
// {
//     auto j = get_json("https://api.bingx.com/api/v1/ticker/24hr");
//     if (!j)
//         return;
//     auto arr = (*j)["data"];
//     if (!arr.is_array())
//         return;
//     size_t kept = 0;
//     for (auto &t : arr)
//     {
//         std::string sym = t.value("symbol", ""); // BTCUSDT или BTC-USDT
//         auto symU = upper(sym);
//         if (!(ends_with(symU, "USDT") || ends_with(symU, "-USDT")))
//             continue;
//         std::string baseU = ends_with(symU, "-USDT") ? symU.substr(0, symU.size() - 5)
//                                                      : symU.substr(0, symU.size() - 4);
//         try
//         {
//             double bid = std::stod(t.value("bidPrice", "0"));
//             double ask = std::stod(t.value("askPrice", "0"));
//             double qv = std::stod(t.value("quoteVolume", "0"));
//             add_quote(book, bl, baseU, "BingX", bid, ask, qv, FEE_BINGX);
//             ++kept;
//         }
//         catch (...)
//         {
//         }
//     }
//     std::cerr << "[BingX] quotes " << kept << "\n";
// }

// XT.com
static void load_xt(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://sapi.xt.com/v4/public/ticker");
    if (!j)
        return;
    auto arr = (*j)["result"];
    if (!arr.is_array())
        return;
    size_t kept = 0;
    for (auto &t : arr)
    {
        std::string sym = t.value("s", ""); // BTC_USDT
        auto symU = upper(sym);
        if (!ends_with(symU, "_USDT"))
            continue;
        std::string baseU = symU.substr(0, symU.size() - 5);
        try
        {
            double bid = std::stod(t.value("b", "0"));
            double ask = std::stod(t.value("a", "0"));
            double qv = std::stod(t.value("qv", "0"));
            add_quote(book, bl, baseU, "XT", bid, ask, qv, FEE_XT);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[XT] quotes " << kept << "\n";
}

// LBank
static void load_lbank(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://api.lbkex.com/v2/ticker/24hr.do?symbol=all");
    if (!j)
        return;
    auto arr = (*j)["data"];
    if (!arr.is_array())
        return;
    size_t kept = 0;
    for (auto &t : arr)
    {
        std::string sym = t.value("symbol", ""); // btc_usdt
        auto symU = upper(sym);
        if (!ends_with(symU, "_USDT"))
            continue;
        std::string baseU = symU.substr(0, symU.size() - 5);
        try
        {
            double bid = std::stod(t.value("bestBid", "0"));
            double ask = std::stod(t.value("bestAsk", "0"));
            double qv = std::stod(t.value("quoteVolume", "0"));
            add_quote(book, bl, baseU, "LBank", bid, ask, qv, FEE_LBANK);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[LBank] quotes " << kept << "\n";
}

// CoinEx
static void load_coinex(Book &book, const std::unordered_set<std::string> &bl)
{
    auto j = get_json("https://api.coinex.com/v1/market/ticker/all");
    if (!j)
        return;
    auto data = (*j)["data"];
    if (!data.is_object())
        return;
    size_t kept = 0;
    for (auto it = data.begin(); it != data.end(); ++it)
    {
        std::string sym = upper(it.key()); // BTCUSDT
        if (!ends_with(sym, "USDT"))
            continue;
        std::string baseU = sym.substr(0, sym.size() - 4);
        auto tick = it.value();
        try
        {
            double bid = tick["ticker"]["buy"].get<double>();
            double ask = tick["ticker"]["sell"].get<double>();
            double qv = tick["ticker"]["vol"].get<double>(); // может быть не в USDT — используем как сигнал
            add_quote(book, bl, baseU, "CoinEx", bid, ask, qv, FEE_COINEX);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[CoinEx] quotes " << kept << "\n";
}

// // Ourbit (best-effort)
// static void load_ourbit(Book &book, const std::unordered_set<std::string> &bl)
// {
//     auto j = get_json("https://openapi.ourbit.com/api/v1/market/tickers");
//     if (!j)
//         return;
//     auto arr = (*j)["data"];
//     if (!arr.is_array())
//         return;
//     size_t kept = 0;
//     for (auto &t : arr)
//     {
//         std::string sym = t.value("symbol", ""); // BTCUSDT/BTC_USDT
//         auto symU = upper(sym);
//         if (!(ends_with(symU, "USDT") || ends_with(symU, "_USDT")))
//             continue;
//         std::string baseU = ends_with(symU, "_USDT") ? symU.substr(0, symU.size() - 5)
//                                                      : symU.substr(0, symU.size() - 4);
//         try
//         {
//             double bid = 0, ask = 0, qv = 0;
//             if (t.contains("bidPrice"))
//                 bid = std::stod(t.value("bidPrice", "0"));
//             if (t.contains("askPrice"))
//                 ask = std::stod(t.value("askPrice", "0"));
//             if (t.contains("quoteVolume"))
//                 qv = std::stod(t.value("quoteVolume", "0"));
//             add_quote(book, bl, baseU, "Ourbit", bid, ask, qv, FEE_OURBIT);
//             ++kept;
//         }
//         catch (...)
//         {
//         }
//     }
//     std::cerr << "[Ourbit] quotes " << kept << "\n";
// }

// ===================== Telegram =====================
void sendTelegram(const std::string &token, const std::string &chat_id, const std::string &text)
{
    auto r = cpr::Post(
        cpr::Url{"https://api.telegram.org/bot" + token + "/sendMessage"},
        cpr::Payload{{"chat_id", chat_id}, {"text", text}, {"parse_mode", "Markdown"}});
    if (r.status_code != 200)
    {
        std::cerr << "[Telegram] send failed: " << r.status_code << " " << r.error.message << "\n";
    }
}

// ===================== Персистентность и сигналы =====================
struct Hit
{
    std::string pair, buyEx, sellEx;
    double ask, bid, gross, net, buyVol, sellVol;
};

struct Key
{
    std::string pair;
    std::string buyEx;
    std::string sellEx;
};
struct KeyHash
{
    size_t operator()(const Key &k) const noexcept
    {
        return std::hash<std::string>()(k.pair) ^ (std::hash<std::string>()(k.buyEx) << 1) ^ (std::hash<std::string>()(k.sellEx) << 2);
    }
};
struct KeyEq
{
    bool operator()(const Key &a, const Key &b) const noexcept
    {
        return a.pair == b.pair && a.buyEx == b.buyEx && a.sellEx == b.sellEx;
    }
};

static std::unordered_map<Key, int, KeyHash, KeyEq> surviveCounter;
static constexpr int MIN_TICKS_TO_SHOW = 2;

// антиспам TG: на одну связку раз в 10 минут
static std::unordered_map<Key, std::chrono::system_clock::time_point, KeyHash, KeyEq> lastSent;
static constexpr int MIN_SEND_INTERVAL_SEC = 600;

// ===================== MAIN =====================
int main()
{
    std::string tg_token = std::getenv("TG_TOKEN") ? std::getenv("TG_TOKEN") : "";
    std::string tg_chat = std::getenv("TG_CHAT_ID") ? std::getenv("TG_CHAT_ID") : "";
    if (tg_token.empty() || tg_chat.empty())
    {
        std::cerr << "[Telegram] set TG_TOKEN and TG_CHAT_ID env vars\n";
    }

    auto blacklist = load_blacklist();
    auto lastHeartbeat = std::chrono::system_clock::now();

    while (true)
    {
        Book book;

        // Production-grade лоадеры
        load_binance(book, blacklist);
        load_okx(book, blacklist);
        load_kucoin(book, blacklist);
        load_bybit(book, blacklist);
        load_gate(book, blacklist);
        load_mexc(book, blacklist);
        load_bitget(book, blacklist);
        load_htx(book, blacklist);

        if (ENABLE_EXPERIMENTAL)
        {
            load_bitmart(book, blacklist);
            // load_bingx(book, blacklist);
            load_xt(book, blacklist);
            load_lbank(book, blacklist);
            load_coinex(book, blacklist);
            // load_ourbit(book, blacklist);
        }

        // --- формируем сигналы ---
        std::vector<Hit> hits;
        hits.reserve(5000);

        for (auto &kv : book)
        {
            const std::string &pair = kv.first;
            auto &quotes = kv.second;
            if (quotes.size() < 2)
                continue;

            // (a) Соберём mids для всех и отдельно для Tier-1
            std::vector<const Quote *> all;
            all.reserve(quotes.size());
            std::vector<double> mids_all;
            mids_all.reserve(quotes.size());
            std::vector<double> mids_t1;
            mids_t1.reserve(quotes.size());
            for (const auto &q : quotes)
            {
                all.push_back(&q);
                mids_all.push_back(q.mid);
                if (TIER1.count(q.ex))
                    mids_t1.push_back(q.mid);
            }
            if (all.size() < 2)
                continue;

            // (b) Референс — медиана Tier-1, если они есть; иначе — медиана всех
            double ref = 0.0;
            if (mids_t1.size() >= 1)
            {
                ref = median(mids_t1);
            }
            else
            {
                ref = median(mids_all);
            }

            // (c) MAD-кокон: оставляем цены внутри ref ± K*MAD
            //   Для Tier-1 берём мягче (K=6), для остальных строже (K=4)
            double m_all = mad(mids_all, ref);
            double k_t1 = 6.0;
            double k_non = 4.0;
            double band_t1_low = ref - k_t1 * m_all;
            double band_t1_high = ref + k_t1 * m_all;
            double band_non_low = ref - k_non * m_all;
            double band_non_high = ref + k_non * m_all;

            // (d) «якорь Tier-1»:
            //    - Если есть хоть 1 биржа из Tier-1 около ref — разрешаем и non-Tier1,
            //      но только если они попадают в более узкий band_non.
            //    - Если Tier-1 нет вообще — работаем по all, но всё равно через band_non.
            std::vector<const Quote *> filtered;
            filtered.reserve(all.size());
            bool have_tier1_anchor = (mids_t1.size() >= 1);
            for (const Quote *q : all)
            {
                bool is_t1 = TIER1.count(q->ex) > 0;
                double lo = is_t1 ? band_t1_low : band_non_low;
                double hi = is_t1 ? band_t1_high : band_non_high;
                if (q->mid >= lo && q->mid <= hi)
                {
                    filtered.push_back(q);
                }
            }
            if (filtered.size() < 2)
                continue;

            // (e) Если есть Tier-1 якорь — требуем хотя бы одну Tier-1 в итоговом множестве
            if (have_tier1_anchor)
            {
                bool t1_present = false;
                for (auto *q : filtered)
                    if (TIER1.count(q->ex))
                    {
                        t1_present = true;
                        break;
                    }
                if (!t1_present)
                    continue;
            }
        }

        // --- персистентность (минимум 2 тика подряд) ---
        std::unordered_set<Key, KeyHash, KeyEq> currentKeys;
        currentKeys.reserve(hits.size() * 2);
        for (const auto &h : hits)
        {
            Key k{h.pair, h.buyEx, h.sellEx};
            currentKeys.insert(k);
            surviveCounter[k] += 1;
        }
        for (auto it = surviveCounter.begin(); it != surviveCounter.end();)
        {
            if (!currentKeys.count(it->first))
                it = surviveCounter.erase(it);
            else
                ++it;
        }
        std::vector<Hit> durable;
        durable.reserve(hits.size());
        for (const auto &h : hits)
        {
            Key k{h.pair, h.buyEx, h.sellEx};
            if (surviveCounter[k] >= MIN_TICKS_TO_SHOW)
                durable.push_back(h);
        }

        std::sort(durable.begin(), durable.end(),
                  [](const Hit &a, const Hit &b)
                  { return a.net == b.net ? a.gross > b.gross : a.net > b.net; });

        // --- вывод и отправка в Telegram ---
        auto now = std::chrono::system_clock::now();
        auto now_c = std::chrono::system_clock::to_time_t(now);
        std::cout << "\n--- " << std::put_time(std::localtime(&now_c), "%F %T") << " ---\n";
        std::cout << std::left
                  << std::setw(16) << "PAIR"
                  << std::setw(8) << "BUY"
                  << std::setw(8) << "SELL"
                  << std::right
                  << std::setw(12) << "Ask"
                  << std::setw(12) << "Bid"
                  << std::setw(10) << "Gross%"
                  << std::setw(10) << "Net%"
                  << std::setw(14) << "BuyVol24h"
                  << std::setw(14) << "SellVol24h"
                  << "\n";

        size_t shown = 0;
        for (const auto &h : durable)
        {
            if (shown >= 40)
                break; // чтобы не засорять консоль
            std::cout << std::left
                      << std::setw(16) << h.pair
                      << std::setw(8) << h.buyEx
                      << std::setw(8) << h.sellEx
                      << std::right
                      << std::setw(12) << h.ask
                      << std::setw(12) << h.bid
                      << std::setw(10) << std::setprecision(3) << h.gross
                      << std::setw(10) << std::setprecision(3) << h.net
                      << std::setw(14) << std::setprecision(0) << h.buyVol
                      << std::setw(14) << std::setprecision(0) << h.sellVol
                      << std::setprecision(6)
                      << "\n";
            ++shown;

            if (!tg_token.empty() && !tg_chat.empty())
            {
                Key k{h.pair, h.buyEx, h.sellEx};
                bool shouldSend = false;
                auto it = lastSent.find(k);
                if (it == lastSent.end())
                    shouldSend = true;
                else
                {
                    auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(now - it->second).count();
                    if (elapsed > MIN_SEND_INTERVAL_SEC)
                        shouldSend = true;
                }
                if (shouldSend)
                {
                    std::ostringstream msg;
                    msg << "*" << h.pair << "*\n"
                        << "BUY " << h.buyEx << " @" << std::fixed << std::setprecision(8) << h.ask << "\n"
                        << "SELL " << h.sellEx << " @" << std::fixed << std::setprecision(8) << h.bid << "\n"
                        << "Net: " << std::fixed << std::setprecision(2) << h.net << "%   (Gross: " << h.gross << "%)\n"
                        << "Vol24h: " << (long long)h.buyVol << " / " << (long long)h.sellVol;
                    sendTelegram(tg_token, tg_chat, msg.str());
                    lastSent[k] = now;
                }
            }
        }
        if (shown == 0)
        {
            std::cout << "(no durable opportunities >= " << MIN_NET_SPREAD_PCT << "% net)\n";
        }
        // --- Heartbeat: проверочное сообщение раз в 5 минут ---
        if (!tg_token.empty() && !tg_chat.empty())
        {
            auto now = std::chrono::system_clock::now();
            auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(now - lastHeartbeat).count();
            if (elapsed >= HEARTBEAT_INTERVAL_SEC)
            {
                auto now_c = std::chrono::system_clock::to_time_t(now);
                std::ostringstream msg;
                msg << "✅ Bot alive. Time: " << std::put_time(std::localtime(&now_c), "%F %T");
                sendTelegram(tg_token, tg_chat, msg.str());
                lastHeartbeat = now;
            }
        }

        std::this_thread::sleep_for(std::chrono::seconds(POLL_INTERVAL_SEC));
    }
    return 0;
}
