// arb_cross_all_telegram.cpp
// Build (Ubuntu): g++ -std=c++20 arb_cross_all_telegram.cpp -o CA -lcpr -lssl -lcrypto -lpthread
// Env: export TG_TOKEN=... ; export TG_CHAT_ID=...

#include <cpr/cpr.h>
#include <nlohmann/json.hpp>
#include <algorithm>
#include <chrono>
#include <cctype>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <optional>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using nlohmann::json;

// ===================== ПАРАМЕТРЫ =====================
static constexpr int HEARTBEAT_INTERVAL_SEC = 300;
static constexpr int POLL_INTERVAL_SEC = 5;

static constexpr double MIN_NET_SPREAD_PCT = 2.0;
static constexpr double MIN_BUY_VOL_USD = 500'000.0;
static constexpr double MIN_SELL_VOL_USD = 500'000.0;
static constexpr double MAX_REL_INNER_SPREAD = 0.030; // (ask-bid)/ask <= 3%

// Требования к покрытию рынками
static constexpr bool REQUIRE_TIER1_INTERSECTION = true;
static constexpr int MIN_TIER1_FOR_PAIR = 2; // ≥2 Tier-1
static constexpr int MIN_EXCH_FOR_PAIR = 3;  // ≥3 биржи на пару

// Сколько сигналов в TG за проход
static constexpr int TG_TOP_K_PER_TICK = 1;

// Экспериментальные биржи
static constexpr bool ENABLE_EXPERIMENTAL = true;

// Такер-комиссии, %
static constexpr double FEE_BINANCE = 0.20, FEE_OKX = 0.20, FEE_KUCOIN = 0.20, FEE_BYBIT = 0.20;
static constexpr double FEE_GATE = 0.20, FEE_MEXC = 0.20, FEE_BITGET = 0.20, FEE_HTX = 0.20;
static constexpr double FEE_BITMART = 0.20, FEE_BINGX = 0.20, FEE_XT = 0.20, FEE_LBANK = 0.20;
static constexpr double FEE_COINEX = 0.20, FEE_OURBIT = 0.20;

// Tier-1 якорь
static const std::unordered_set<std::string> TIER1 = {
    "Binance", "OKX", "Bybit", "KuCoin", "Bitget", "Gate", "MEXC"};

// Тикеры с риском коллизии имен (можно убрать по мере заполнения chains.csv)
static const std::unordered_set<std::string> COLLISION_TICKERS = {
    "BOT", "U", "M87", "TBC"};

// ===================== УТИЛИТЫ =====================
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
static bool looks_dirty_symbol(const std::string &baseU)
{
    if (baseU.size() < 3)
        return true; // слишком короткие
    for (char c : baseU)
        if (std::isdigit((unsigned char)c))
            return true; // M87, X2Y2
    return false;
}

static double median(std::vector<double> &v)
{
    if (v.empty())
        return 0.0;
    std::nth_element(v.begin(), v.begin() + v.size() / 2, v.end());
    return v[v.size() / 2];
}
static double mad(const std::vector<double> &v, double ref)
{
    if (v.empty())
        return 0.0;
    std::vector<double> d;
    d.reserve(v.size());
    for (double x : v)
        d.push_back(std::abs(x - ref));
    std::nth_element(d.begin(), d.begin() + d.size() / 2, d.end());
    return d[d.size() / 2];
}

// HTTP + JSON
static std::optional<json> get_json(
    const std::string &url,
    const cpr::Parameters &params = {},
    const cpr::Header &hdr_in = {{"Accept", "application/json"}, {"User-Agent", "arb-scanner/2.3"}, {"Accept-Encoding", "identity"}})
{
    const int max_attempts = 4;
    int backoff = 300;
    for (int a = 1; a <= max_attempts; ++a)
    {
        auto r = cpr::Get(cpr::Url{url}, params, hdr_in, cpr::Timeout{10000});
        if (r.status_code == 200)
        {
            auto j = json::parse(r.text, nullptr, false);
            if (!j.is_discarded())
                return j;
        }
        else
        {
            std::cerr << "[HTTP] " << url << " -> " << r.status_code << " " << r.error.message << " (attempt " << a << ")\n";
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(backoff));
        backoff = std::min(backoff * 2, 3000);
    }
    return std::nullopt;
}

// ===================== CHAIN DB (локальные CSV) =====================
// chains.csv строки: exchange,base,chain[,contract]
// maintenance.csv:   exchange,base,chain,deposit_ok,withdraw_ok   (0/1)

struct ChainInfo
{
    std::string chain;
    std::string contract;
};
using ChainDB = std::unordered_map<std::string, std::unordered_map<std::string, ChainInfo>>;

struct MaintInfo
{
    int dep = -1, wdr = -1;
}; // -1 = неизвестно
using MaintDB = std::unordered_map<std::string, std::unordered_map<std::string, std::unordered_map<std::string, MaintInfo>>>;
// ex -> base -> chain -> flags

static ChainDB load_chain_db(const std::string &path = "chains.csv")
{
    ChainDB db;
    std::ifstream f(path);
    if (!f)
    {
        std::cerr << "[Chains] " << path << " not found (using defaults)\n";
        return db;
    }
    std::string line;
    int n = 0;
    while (std::getline(f, line))
    {
        auto pos = line.find('#');
        if (pos != std::string::npos)
            line = line.substr(0, pos);
        if (line.empty())
            continue;
        std::stringstream ss(line);
        std::string ex, base, chain, contract;
        if (!std::getline(ss, ex, ','))
            continue;
        if (!std::getline(ss, base, ','))
            continue;
        if (!std::getline(ss, chain, ','))
            continue;
        std::getline(ss, contract, ',');
        ex = upper(ex);
        base = upper(base);
        chain = upper(chain);
        contract = upper(contract);
        if (ex.empty() || base.empty() || chain.empty())
            continue;
        db[ex][base] = ChainInfo{chain, contract};
        ++n;
    }
    std::cerr << "[Chains] loaded " << n << " rows\n";
    return db;
}

static MaintDB load_maint_db(const std::string &path = "maintenance.csv")
{
    MaintDB db;
    std::ifstream f(path);
    if (!f)
    {
        std::cerr << "[Maint] " << path << " not found (assuming all OK)\n";
        return db;
    }
    std::string line;
    int n = 0;
    while (std::getline(f, line))
    {
        auto pos = line.find('#');
        if (pos != std::string::npos)
            line = line.substr(0, pos);
        if (line.empty())
            continue;
        std::stringstream ss(line);
        std::string ex, base, chain, dep, wdr;
        if (!std::getline(ss, ex, ','))
            continue;
        if (!std::getline(ss, base, ','))
            continue;
        if (!std::getline(ss, chain, ','))
            continue;
        if (!std::getline(ss, dep, ','))
            continue;
        if (!std::getline(ss, wdr, ','))
            continue;
        ex = upper(ex);
        base = upper(base);
        chain = upper(chain);
        db[ex][base][chain] = MaintInfo{dep == "1" ? 1 : 0, wdr == "1" ? 1 : 0};
        ++n;
    }
    std::cerr << "[Maint] loaded " << n << " rows\n";
    return db;
}

static std::string default_chain_guess(const std::string &baseU)
{
    if (baseU == "BTC")
        return "BTC";
    if (baseU == "ETH")
        return "ERC20";
    if (baseU == "SOL")
        return "SOL";
    // популярные ERC20 — считаем ERC20
    static const std::unordered_set<std::string> erc20 = {
        "USDT", "USDC", "LINK", "UNI", "SHIB", "PEPE", "WLD", "ARB", "OP", "LDO", "AAVE", "MKR", "COMP", "SNX", "SUSHI", "CRV", "IMX", "APE", "LRC", "RNDR", "TIA"};
    if (erc20.count(baseU))
        return "ERC20";
    // популярные BTC L2/обёртки на споте
    if (baseU == "RUNECOIN")
        return "BTCRUNES";
    return ""; // неизвестно
}

static std::string get_chain(const ChainDB &db, const std::string &ex, const std::string &baseU)
{
    auto exU = upper(ex);
    auto it1 = db.find(exU);
    if (it1 != db.end())
    {
        auto it2 = it1->second.find(baseU);
        if (it2 != it1->second.end())
            return it2->second.chain;
    }
    return default_chain_guess(baseU);
}

static bool is_deposit_ok(const MaintDB &mdb, const std::string &ex, const std::string &baseU, const std::string &chain)
{
    auto exU = upper(ex);
    auto it1 = mdb.find(exU);
    if (it1 == mdb.end())
        return true;
    auto it2 = it1->second.find(baseU);
    if (it2 == it1->second.end())
        return true;
    auto it3 = it2->second.find(upper(chain));
    if (it3 == it2->second.end())
        return true;
    return (it3->second.dep != 0);
}
static bool is_withdraw_ok(const MaintDB &mdb, const std::string &ex, const std::string &baseU, const std::string &chain)
{
    auto exU = upper(ex);
    auto it1 = mdb.find(exU);
    if (it1 == mdb.end())
        return true;
    auto it2 = it1->second.find(baseU);
    if (it2 == it1->second.end())
        return true;
    auto it3 = it2->second.find(upper(chain));
    if (it3 == it2->second.end())
        return true;
    return (it3->second.wdr != 0);
}

// ===================== МОДЕЛЬ =====================
struct Quote
{
    std::string ex;
    double bid = 0, ask = 0, vol = 0, fee = 0, mid = 0;
    std::string chain;
};
using Book = std::map<std::string, std::vector<Quote>>;

static void add_quote(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &chains,
                      const std::string &baseU, const std::string &exch,
                      double bid, double ask, double vol, double fee)
{
    if (bid <= 0 || ask <= 0)
        return;
    if (bl.count(baseU))
        return;
    if (COLLISION_TICKERS.count(baseU))
        return; // отсекаем коллизии по умолчанию
    if (looks_dirty_symbol(baseU))
        return;

    double rel = (ask - bid) / ask;
    if (rel > MAX_REL_INNER_SPREAD)
        return;

    Quote q{exch, bid, ask, vol, fee, (bid + ask) / 2.0, get_chain(chains, exch, baseU)};
    book[baseU + "_USDT"].push_back(std::move(q));
}

// ===================== ЛОАДЕРЫ БИРЖ =====================
static void load_binance(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
                add_quote(book, bl, ch, baseU, "Binance", bid, ask, qv, FEE_BINANCE);
                ++kept;
            }
            catch (...)
            {
            }
        }
        std::cerr << "[Binance] quotes " << kept << "\n";
    }
}

static void load_okx(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
            add_quote(book, bl, ch, baseU, "OKX", bid, ask, qv, FEE_OKX);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[OKX] quotes " << kept << "\n";
}

static void load_kucoin(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
            add_quote(book, bl, ch, baseU, "KuCoin", bid, ask, qv, FEE_KUCOIN);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[KuCoin] quotes " << kept << "\n";
}

static void load_bybit(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
            add_quote(book, bl, ch, baseU, "Bybit", bid, ask, qv, FEE_BYBIT);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[Bybit] quotes " << kept << "\n";
}

static void load_gate(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
            add_quote(book, bl, ch, baseU, "Gate", bid, ask, qv, FEE_GATE);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[Gate] quotes " << kept << "\n";
}

static void load_mexc(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
            add_quote(book, bl, ch, baseU, "MEXC", bid, ask, qv, FEE_MEXC);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[MEXC] quotes " << kept << "\n";
}

static void load_bitget(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
        auto su = upper(sym);
        if (!(ends_with(su, "USDT") || ends_with(su, "_USDT")))
            continue;
        std::string baseU = ends_with(su, "_USDT") ? su.substr(0, su.size() - 5) : su.substr(0, su.size() - 4);
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
            add_quote(book, bl, ch, baseU, "Bitget", bid, ask, qv, FEE_BITGET);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[Bitget] quotes " << kept << "\n";
}

static void load_htx(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
        std::string sym = t.value("symbol", "");
        auto su = upper(sym);
        if (su.size() < 6 || !ends_with(su, "USDT"))
            continue;
        std::string baseU = su.substr(0, su.size() - 4);
        try
        {
            double bid = t.value("bid", 0.0);
            double ask = t.value("ask", 0.0);
            double qv = 0.0;
            add_quote(book, bl, ch, baseU, "HTX", bid, ask, qv, FEE_HTX);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[HTX] quotes " << kept << "\n";
}

// ===== Экспериментальные =====
static void load_bitmart(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
        std::string sym = t.value("symbol", "");
        auto su = upper(sym);
        if (!ends_with(su, "_USDT"))
            continue;
        std::string baseU = su.substr(0, su.size() - 5);
        try
        {
            double bid = std::stod(t.value("best_bid", "0"));
            double ask = std::stod(t.value("best_ask", "0"));
            double qv = std::stod(t.value("quote_volume_24h", "0"));
            add_quote(book, bl, ch, baseU, "Bitmart", bid, ask, qv, FEE_BITMART);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[Bitmart] quotes " << kept << "\n";
}

static void load_bingx(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
{
    auto j = get_json("https://open-api.bingx.com/openApi/spot/v1/ticker/24hr");
    if (!j)
        return;
    auto arr = (*j)["data"];
    if (!arr.is_array())
        return;
    size_t kept = 0;
    for (auto &t : arr)
    {
        std::string sym = t.value("symbol", "");
        auto su = upper(sym);
        if (!(ends_with(su, "USDT") || ends_with(su, "-USDT")))
            continue;
        std::string baseU = ends_with(su, "-USDT") ? su.substr(0, su.size() - 5) : su.substr(0, su.size() - 4);
        try
        {
            double bid = 0, ask = 0, qv = 0;
            if (t.contains("bidPrice"))
                bid = std::stod(t.value("bidPrice", "0"));
            if (t.contains("askPrice"))
                ask = std::stod(t.value("askPrice", "0"));
            if (t.contains("quoteVolume"))
                qv = std::stod(t.value("quoteVolume", "0"));
            add_quote(book, bl, ch, baseU, "BingX", bid, ask, qv, FEE_BINGX);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[BingX] quotes " << kept << "\n";
}

static void load_xt(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
        std::string sym = t.value("s", "");
        auto su = upper(sym);
        if (!ends_with(su, "_USDT"))
            continue;
        std::string baseU = su.substr(0, su.size() - 5);
        try
        {
            double bid = std::stod(t.value("b", "0"));
            double ask = std::stod(t.value("a", "0"));
            double qv = std::stod(t.value("qv", "0"));
            add_quote(book, bl, ch, baseU, "XT", bid, ask, qv, FEE_XT);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[XT] quotes " << kept << "\n";
}

static void load_lbank(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
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
        std::string sym = t.value("symbol", "");
        auto su = upper(sym);
        if (!ends_with(su, "_USDT"))
            continue;
        std::string baseU = su.substr(0, su.size() - 5);
        try
        {
            double bid = std::stod(t.value("bestBid", "0"));
            double ask = std::stod(t.value("bestAsk", "0"));
            double qv = std::stod(t.value("quoteVolume", "0"));
            add_quote(book, bl, ch, baseU, "LBank", bid, ask, qv, FEE_LBANK);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[LBank] quotes " << kept << "\n";
}

static void load_coinex(Book &book, const std::unordered_set<std::string> &bl, const ChainDB &ch)
{
    // v1 /market/ticker/all: data -> { date, ticker: { "BTCUSDT": {...} } }
    auto j = get_json("https://api.coinex.com/v1/market/ticker/all");
    if (!j)
        return;
    auto data = (*j)["data"];
    if (!data.is_object())
        return;
    auto tick = data["ticker"];
    if (!tick.is_object())
        return;
    size_t kept = 0;
    for (auto it = tick.begin(); it != tick.end(); ++it)
    {
        std::string sym = upper(it.key());
        if (!ends_with(sym, "USDT"))
            continue;
        std::string baseU = sym.substr(0, sym.size() - 4);
        const auto &v = it.value();
        try
        {
            double bid = v.value("buy", 0.0);
            double ask = v.value("sell", 0.0);
            double qv = 0.0;
            if (v.contains("vol") && v.contains("last"))
            {
                double vol_base = std::stod(v.value("vol", "0"));
                double last = std::stod(v.value("last", "0"));
                if (last > 0)
                    qv = vol_base * last;
            }
            add_quote(book, bl, ch, baseU, "CoinEx", bid, ask, qv, FEE_COINEX);
            ++kept;
        }
        catch (...)
        {
        }
    }
    std::cerr << "[CoinEx] quotes " << kept << "\n";
}

// Ourbit — выключено (нестабильный публичный REST)
// static void load_ourbit(...){}

// ===================== Telegram =====================
static void sendTelegram(const std::string &token, const std::string &chat_id, const std::string &text)
{
    auto r = cpr::Post(
        cpr::Url{"https://api.telegram.org/bot" + token + "/sendMessage"},
        cpr::Payload{{"chat_id", chat_id}, {"text", text}, {"parse_mode", "Markdown"}});
    if (r.status_code != 200)
    {
        std::cerr << "[Telegram] send failed: " << r.status_code << " " << r.error.message << "\n";
    }
}

// ===================== Сигналы =====================
struct Hit
{
    std::string pair, buyEx, sellEx, chain;
    double ask, bid, gross, net, buyVol, sellVol;
};

struct Key
{
    std::string pair, buyEx, sellEx;
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

    // локальные БД
    auto chains = load_chain_db("chains.csv");
    auto maint = load_maint_db("maintenance.csv");

    auto lastHeartbeat = std::chrono::system_clock::now();
    std::unordered_set<std::string> blacklist; // опционально: load from file, если нужно

    while (true)
    {
        Book book;

        // Core
        load_binance(book, blacklist, chains);
        load_okx(book, blacklist, chains);
        load_kucoin(book, blacklist, chains);
        load_bybit(book, blacklist, chains);
        load_gate(book, blacklist, chains);
        load_mexc(book, blacklist, chains);
        load_bitget(book, blacklist, chains);
        load_htx(book, blacklist, chains);

        if (ENABLE_EXPERIMENTAL)
        {
            load_bitmart(book, blacklist, chains);
            load_bingx(book, blacklist, chains);
            load_xt(book, blacklist, chains);
            load_lbank(book, blacklist, chains);
            load_coinex(book, blacklist, chains);
            // load_ourbit(book, blacklist, chains);
        }

        // --- формируем сигналы ---
        std::vector<Hit> hits;
        hits.reserve(8000);

        for (auto &kv : book)
        {
            const std::string &pair = kv.first;
            auto &quotes = kv.second;
            if (quotes.size() < 2)
                continue;

            // mids
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

            double ref = mids_t1.empty() ? median(mids_all) : ([&]
                                                               { double r=median(mids_t1); return r; })();

            double m_all = mad(mids_all, ref);
            double k_t1 = 6.0, k_non = 4.0;
            double band_t1_low = ref - k_t1 * m_all;
            double band_t1_high = ref + k_t1 * m_all;
            double band_non_low = ref - k_non * m_all;
            double band_non_high = ref + k_non * m_all;

            std::vector<const Quote *> filtered;
            filtered.reserve(all.size());
            bool have_t1_anchor = !mids_t1.empty();
            for (const Quote *q : all)
            {
                bool is_t1 = TIER1.count(q->ex) > 0;
                double lo = is_t1 ? band_t1_low : band_non_low;
                double hi = is_t1 ? band_t1_high : band_non_high;
                if (q->mid >= lo && q->mid <= hi)
                    filtered.push_back(q);
            }
            if (filtered.size() < 2)
                continue;

            if (have_t1_anchor)
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

            // Доп. критерии «как у Лопаты»
            std::unordered_set<std::string> exchset;
            int tier1_cnt = 0;
            for (auto *q : filtered)
            {
                exchset.insert(q->ex);
                if (TIER1.count(q->ex))
                    ++tier1_cnt;
            }
            if ((int)exchset.size() < MIN_EXCH_FOR_PAIR)
                continue;
            if (tier1_cnt < MIN_TIER1_FOR_PAIR)
                continue;

            // BUY↔SELL
            for (const Quote *sell : filtered)
            {
                if (sell->bid <= 0)
                    continue;
                for (const Quote *buy : filtered)
                {
                    if (buy == sell)
                        continue;
                    if (buy->ask <= 0)
                        continue;

                    // стало (разрешаем неизвестную сеть; если обе известны — требуем совпадение)
                    if (!buy->chain.empty() && !sell->chain.empty() &&
                        upper(buy->chain) != upper(sell->chain))
                        continue;

                    std::string chain_for_msg =
                        !buy->chain.empty() ? buy->chain : (!sell->chain.empty() ? sell->chain : "UNKNOWN");

                    // депозиты/выводы доступны?
                    if (!is_withdraw_ok(maint, buy->ex, pair.substr(0, pair.size() - 5), buy->chain))
                        continue;
                    if (!is_deposit_ok(maint, sell->ex, pair.substr(0, pair.size() - 5), sell->chain))
                        continue;

                    // объёмы
                    if (buy->vol < MIN_BUY_VOL_USD)
                        continue;
                    if (sell->vol < MIN_SELL_VOL_USD)
                        continue;

                    double grossPct = (sell->bid - buy->ask) / buy->ask * 100.0;
                    double netPct = grossPct - (buy->fee + sell->fee);
                    if (netPct < MIN_NET_SPREAD_PCT)
                        continue;

                    hits.push_back(Hit{
                        pair, buy->ex, sell->ex, chain_for_msg,
                        buy->ask, sell->bid, grossPct, netPct, buy->vol, sell->vol});
                }
            }
        }

        // --- персистентность ---
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

        if ((int)durable.size() > TG_TOP_K_PER_TICK)
        {
            durable.erase(durable.begin() + TG_TOP_K_PER_TICK, durable.end());
        }

        // --- вывод + TG ---
        auto tnow = std::chrono::system_clock::now();
        auto now_c = std::chrono::system_clock::to_time_t(tnow);
        std::cout << "\n--- " << std::put_time(std::localtime(&now_c), "%F %T") << " ---\n";
        std::cout << std::left
                  << std::setw(16) << "PAIR"
                  << std::setw(10) << "CHAIN"
                  << std::setw(10) << "BUY"
                  << std::setw(10) << "SELL"
                  << std::right
                  << std::setw(13) << "Ask"
                  << std::setw(13) << "Bid"
                  << std::setw(10) << "Gross%"
                  << std::setw(10) << "Net%"
                  << std::setw(14) << "BuyVol24h"
                  << std::setw(14) << "SellVol24h"
                  << "\n";

        if (durable.empty())
        {
            std::cout << "(no durable opportunities >= " << MIN_NET_SPREAD_PCT << "% net)\n";
        }

        for (const auto &h : durable)
        {
            std::cout << std::left
                      << std::setw(16) << h.pair
                      << std::setw(10) << h.chain
                      << std::setw(10) << h.buyEx
                      << std::setw(10) << h.sellEx
                      << std::right
                      << std::setw(13) << std::fixed << std::setprecision(8) << h.ask
                      << std::setw(13) << std::fixed << std::setprecision(8) << h.bid
                      << std::setw(10) << std::setprecision(3) << h.gross
                      << std::setw(10) << std::setprecision(3) << h.net
                      << std::setw(14) << std::setprecision(0) << h.buyVol
                      << std::setw(14) << std::setprecision(0) << h.sellVol
                      << std::setprecision(6) << "\n";

            if (!tg_token.empty() && !tg_chat.empty())
            {
                Key k{h.pair, h.buyEx, h.sellEx};
                bool shouldSend = false;
                auto it = lastSent.find(k);
                if (it == lastSent.end())
                    shouldSend = true;
                else
                {
                    auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(tnow - it->second).count();
                    if (elapsed > MIN_SEND_INTERVAL_SEC)
                        shouldSend = true;
                }
                if (shouldSend)
                {
                    std::ostringstream msg;
                    msg << "*" << h.pair << "*  " << std::fixed << std::setprecision(2) << h.net
                        << "% net (" << h.gross << "% gross)\n"
                        << "CHAIN: " << h.chain << "\n"
                        << "BUY  " << h.buyEx << "  @" << std::fixed << std::setprecision(8) << h.ask << "\n"
                        << "SELL " << h.sellEx << "  @" << std::fixed << std::setprecision(8) << h.bid << "\n"
                        << "Vol24h: " << (long long)h.buyVol << " / " << (long long)h.sellVol;
                    sendTelegram(tg_token, tg_chat, msg.str());
                    lastSent[k] = tnow;
                }
            }
        }

        // Heartbeat
        if (!tg_token.empty() && !tg_chat.empty())
        {
            auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(tnow - lastHeartbeat).count();
            if (elapsed >= HEARTBEAT_INTERVAL_SEC)
            {
                auto nowc = std::chrono::system_clock::to_time_t(tnow);
                std::ostringstream msg;
                msg << "✅ Bot alive. Time: " << std::put_time(std::localtime(&nowc), "%F %T");
                sendTelegram(tg_token, tg_chat, msg.str());
                lastHeartbeat = tnow;
            }
        }

        std::this_thread::sleep_for(std::chrono::seconds(POLL_INTERVAL_SEC));
    }

    return 0;
}
