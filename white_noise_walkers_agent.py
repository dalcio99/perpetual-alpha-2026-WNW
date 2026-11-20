"""
White-Noise-Walkers - Perpetual Alpha 2026 trading agent
=======================================================

One-file version of the agent described in the technical report
"Time-series momentum with a rank-optimal sizing policy" (PA26-White-Noise-Walkers-report.pdf).
Section and equation numbers in the comments refer to that report.

What the agent does, once per day at 12:10 UTC (ten minutes after the daily scoring snapshot):

  1. SIGNAL (report Eq. 1). For each of the ten markets, take the sign of the return of the
     corresponding Hyperliquid MAINNET market over the last 720 hourly candles:
     long if the one-month return is positive, short if negative.

  2. SIZE (report Eq. 3). Read the official standings (leaderboard.json, which publishes the
     score Q of every team) and choose the size multiplier k:
         k = 0.25  if our Q exceeds the 4th-best Q by more than 0.02   (safely in the top three)
         k = 2.5   if the 3rd-best Q exceeds ours by more than 0.01    (clearly outside the top three)
         k = 1     otherwise                                           (in contention)
     k = 1 corresponds to $10,000 per market, i.e. C0/10 with C0 = $100,000 the initial capital.

  3. TARGETS. Target notional per market N_i = sign_i * k * C0 / 10 (equal weight across markets),
     with hard caps on the notional per market and on gross exposure.

  4. EXECUTION (report, Execution section). For up to 60 minutes keep one passive post-only
     (ALO) child order per market, at most $2,500, one tick inside the spread and never worse
     than mainnet fair value +/- 5 bps. Afterwards take any remainder with immediate-or-cancel
     (IOC) slices of at most $2,500 within 0.3% of mid. Trades smaller than 10% of the
     per-market target are skipped (no-trade band).

Safety and operations: every HTTP request has a 30 s timeout; positions are always re-read from
the exchange, so a rebalance is idempotent and can be retried; orphaned orders are cancelled;
stale or implausible standings keep the previous size; a manual override file can force any k
(including 0 = flat); an optional heartbeat URL (e.g. healthchecks.io) acts as a dead-man's switch.

Relation to the files that ran live: this is a consolidated and commented version of
bot_trend_v1.py (signal, targets, execution, operations) and endgame_size.py (sizing policy),
which ran as two programs during the scored phase; the sizing policy is now called directly
instead of through a size file.

Usage
-----
  Credentials in a .env file next to this script (never commit it):
      TEAM_WALLET_ADDRESS=0x...      # team account (positions, orders, balances)
      API_WALLET_KEY=0x...           # API wallet private key (signing only; needed for --live)
      HEALTHCHECK_URL=https://...    # optional dead-man's switch

  python white_noise_walkers_agent.py --once            # dry run: print signals, size, targets, first orders
  python white_noise_walkers_agent.py --once --live     # one live rebalance now
  python white_noise_walkers_agent.py --live            # run forever, rebalancing daily at 12:10 UTC

Requirements: Python 3.10+, hyperliquid-python-sdk==0.24.0, requests, python-dotenv, eth-account.
"""
import argparse
import csv
import json
import logging
import math
import os
import socket
import time
from datetime import datetime, timedelta, timezone

import requests
from dotenv import load_dotenv

log = logging.getLogger("agent")

# =============================================================================================
# Parameters (all values as used in the scored phase)
# =============================================================================================

# Competition venue (builder-deployed perp DEX on Hyperliquid testnet) and quote asset
DEX = "pas"
QUOTE = "USDP"

# Venue market -> Hyperliquid mainnet market it replicates (source of the trading signal)
MARKETS = {
    "BTC": "BTC", "ETH": "ETH", "HYPE": "HYPE",
    "SP500": "xyz:SP500", "EWY": "xyz:EWY", "EWJ": "xyz:EWJ",
    "BRENT": "xyz:BRENTOIL", "GOLD": "xyz:GOLD",
    "USDEUR": "xyz:EUR", "USDJPY": "xyz:JPY",
}

# --- Signal (report Eq. 1)
LOOKBACK_HOURS = 720                  # one month of hourly candles

# --- Position size
INITIAL_CAPITAL = 100_000.0           # C0; positions are sized on the initial capital, not on equity
UNIT_FRACTION = 1 / len(MARKETS)      # k = 1 -> C0/10 = $10,000 per market (unit gross leverage)

# --- Sizing policy (report Eq. 3)
K_LOW, K_MID, K_HIGH = 0.25, 1.0, 2.5
SAFE_MARGIN = 0.02                    # our Q - Q(4th) above this -> K_LOW
FAR_MARGIN = 0.01                     # Q(3rd) - our Q above this -> K_HIGH
POLICY_START = datetime(2026, 10, 22, 12, tzinfo=timezone.utc)   # first sample the policy acted on
COMPETITION_START = datetime(2026, 10, 19, 12, tzinfo=timezone.utc)
TEAM_NAME = "White-Noise-Walkers"
LEADERBOARD_URL = "https://d23m2l9bjnbgul.cloudfront.net/public/leaderboard.json"

# --- Hard risk limits (enforced in code, report Risk management)
MAX_NOTIONAL_PER_MARKET = 25_000.0    # = 2.5 x $10k
MAX_GROSS_MULTIPLE = 2.6              # refuse to start if the largest possible book exceeds this x C0
MARGIN_LEVERAGE = 5                   # cross-margin leverage set on every market (exchange max: 10-50)

# --- Execution
REBALANCE_HOUR, REBALANCE_MINUTE = 12, 10    # UTC, just after the 12:00 scoring snapshot
NO_TRADE_BAND = 0.10                  # skip trades smaller than 10% of the per-market target
PATIENT_WINDOW_MIN = 60               # minutes of passive (post-only) execution
PATIENT_STEP_S = 60                   # seconds between updates of the child orders
SLICE_USD = 2_500.0                   # maximum child-order size
FAIR_CAP_BPS = 5.0                    # never post worse than mainnet fair value +/- 5 bps
IOC_SLIPPAGE = 0.003                  # IOC price limit: 0.3% from mid
IOC_PAUSE_S = 20                      # pause between IOC slices so the book can refill
IOC_MAX_SLICES = 10

# --- Operations
HTTP_TIMEOUT_S = 30
REBALANCE_ATTEMPTS = 9                # a failed rebalance is retried (cancel everything first)
RETRY_WAIT_S = 600
MAINNET_INFO = "https://api.hyperliquid.xyz/info"
OVERRIDE_FILE = "size_override.json"  # {"k": 0.0} forces a size (e.g. flat); delete to resume the policy
STATE_FILE = "agent_state.json"       # last size decision, kept if the standings cannot be read
TRADE_LOG = "trades.csv"


# =============================================================================================
# Small helpers
# =============================================================================================

def round_price(px, sz_decimals):
    """Hyperliquid price rule: at most 5 significant figures and at most (6 - szDecimals) decimals."""
    return round(float(f"{px:.5g}"), 6 - sz_decimals)


def price_tick(px, sz_decimals):
    """Smallest valid price increment at this price level."""
    sig = 10 ** (math.floor(math.log10(px)) - 4) if px > 0 else 0
    return max(sig, 10 ** -(6 - sz_decimals))


def floor_size(size, sz_decimals):
    """Round a size DOWN to the market's lot size (never trade more than intended)."""
    q = 10 ** sz_decimals
    return math.floor(abs(size) * q + 1e-9) / q


def venue(coin):
    """Venue name of a market, e.g. 'BTC' -> 'pas:BTC'."""
    return coin if coin.startswith(f"{DEX}:") else f"{DEX}:{coin}"


def order_statuses(res):
    if not isinstance(res, dict) or res.get("status") != "ok":
        return None, f"request failed: {res}"
    return res.get("response", {}).get("data", {}).get("statuses", []), None


def install_request_timeout(seconds):
    """Give every HTTP request (including the SDK's own) a time limit, so a dropped connection
    raises an error instead of freezing the agent."""
    socket.setdefaulttimeout(seconds)
    original = requests.Session.request

    def request(self, method, url, **kw):
        if kw.get("timeout") is None:
            kw["timeout"] = seconds
        return original(self, method, url, **kw)
    requests.Session.request = request


def ping(kind="", message=""):
    """Dead-man's switch (e.g. healthchecks.io): '' = alive, 'start', 'fail'. Never raises."""
    url = os.environ.get("HEALTHCHECK_URL", "")
    if not url:
        return
    try:
        requests.post(url.rstrip("/") + (f"/{kind}" if kind else ""), data=message.encode()[:10_000], timeout=10)
    except Exception as e:
        log.warning("heartbeat ping failed (%s) - trading continues", e)


# =============================================================================================
# 1. Signal: sign of the one-month mainnet return (report Eq. 1)
# =============================================================================================

def mainnet_post(body):
    r = requests.post(MAINNET_INFO, json=body, timeout=HTTP_TIMEOUT_S)
    r.raise_for_status()
    return r.json()


def one_month_signal(mainnet_coin, now_ms):
    """+1 / -1 / 0 = sign of the return over the last LOOKBACK_HOURS completed hourly candles.
    Only closed candles are used, so no future information enters the signal."""
    req = {"coin": mainnet_coin, "interval": "1h",
           "startTime": now_ms - (LOOKBACK_HOURS + 48) * 3_600_000, "endTime": now_ms}
    candles = [c for c in mainnet_post({"type": "candleSnapshot", "req": req}) if int(c["T"]) <= now_ms]
    closes = [float(c["c"]) for c in sorted(candles, key=lambda c: int(c["t"]))]
    if len(closes) <= LOOKBACK_HOURS:
        raise ValueError(f"only {len(closes)} candles, need {LOOKBACK_HOURS + 1}")
    ret = closes[-1] / closes[-1 - LOOKBACK_HOURS] - 1
    return (1 if ret > 0 else -1 if ret < 0 else 0), ret


def all_signals():
    now_ms = int(time.time() * 1000)
    signals = {}
    for coin, ref in MARKETS.items():
        try:
            s, ret = one_month_signal(ref, now_ms)
            log.info("signal %-7s (mainnet %-12s) 720h return %+6.2f%% -> %s",
                     coin, ref, 100 * ret, {1: "LONG", -1: "SHORT", 0: "FLAT"}[s])
        except Exception as e:                       # missing data: stay flat in that market
            log.warning("signal %-7s unavailable (%s) -> FLAT", coin, e)
            s = 0
        signals[venue(coin)] = s
    return signals


# =============================================================================================
# 2. Size: rank-optimal threshold policy on the official standings (report Eq. 3)
# =============================================================================================

def size_policy(q_ours, scores, sample_time):
    """Pure decision rule. scores = Q of all ranked teams. Returns (k, reason)."""
    if sample_time < POLICY_START:
        return K_MID, "policy not active yet"
    q_sorted = sorted(scores, reverse=True)
    third, fourth = q_sorted[2], q_sorted[3]
    if q_ours - fourth > SAFE_MARGIN:
        return K_LOW, f"safely in the top three: Q {q_ours:.4f} is {q_ours - fourth:+.4f} above 4th place"
    if third - q_ours > FAR_MARGIN:
        return K_HIGH, f"outside the top three: Q {q_ours:.4f} is {third - q_ours:.4f} below 3rd place"
    return K_MID, f"in contention: margin to 4th {q_ours - fourth:+.4f}, gap to 3rd {third - q_ours:+.4f}"


def read_standings(sample_time):
    """Download leaderboard.json and return (our Q, list of all Q). Raises if the data are stale or
    implausible, so that the caller keeps the previous size."""
    data = requests.get(LEADERBOARD_URL, timeout=HTTP_TIMEOUT_S,
                        headers={"User-Agent": "Mozilla/5.0 (white-noise-walkers agent)"}).json()
    generated = datetime.strptime(data["generated_at"][:19], "%Y-%m-%dT%H:%M:%S").replace(tzinfo=timezone.utc)
    if generated < sample_time:
        raise RuntimeError(f"standings generated {generated:%Y-%m-%d %H:%M} UTC, before today's sample")
    teams = [t for t in data["teams"] if t.get("ranked") and t.get("q") is not None]
    if len(teams) < 5 or not all(0 <= t["q"] <= 1 for t in teams):
        raise RuntimeError(f"implausible standings ({len(teams)} ranked teams)")
    key = lambda s: "".join(ch for ch in str(s).lower() if ch.isalnum())   # noqa: E731
    me = next((t for t in teams if key(t["name"]) == key(TEAM_NAME)), None)
    if me is None:
        raise RuntimeError(f"team {TEAM_NAME!r} not in the standings")
    # The leaderboard publishes s (volatility) and sigma = s*sqrt(n) (volatility_horizon), so
    # (sigma/s)^2 = n is the number of daily returns included: it must contain today's sample.
    if me.get("volatility") and me.get("volatility_horizon"):
        n_reported = round((me["volatility_horizon"] / me["volatility"]) ** 2)
        n_expected = (sample_time - COMPETITION_START).days
        if n_reported < n_expected:
            raise RuntimeError(f"standings contain {n_reported} daily returns, expected {n_expected}")
    return me["q"], [t["q"] for t in teams]


def choose_size(persist=True):
    """Size multiplier k for today's rebalance: manual override > policy > previous decision."""
    if os.path.exists(OVERRIDE_FILE):
        k = float(json.load(open(OVERRIDE_FILE))["k"])
        log.info("size: MANUAL OVERRIDE k = %g (%s)", k, OVERRIDE_FILE)
        return k
    now = datetime.now(timezone.utc)
    sample = now.replace(hour=12, minute=0, second=0, microsecond=0)
    if now < sample:
        sample -= timedelta(days=1)
    previous = json.load(open(STATE_FILE))["k"] if os.path.exists(STATE_FILE) else K_MID
    try:
        q_ours, scores = read_standings(sample)
        k, reason = size_policy(q_ours, scores, sample)
    except Exception as e:
        log.warning("size: standings unusable (%s) -> keeping previous k = %g", e, previous)
        ping("fail", f"standings unusable ({e}); previous size kept")
        return previous
    log.info("size: k = %g (%s)", k, reason)
    if not persist:                                   # dry run: decide, but do not record
        return k
    tmp = STATE_FILE + ".tmp"
    json.dump({"k": k, "reason": reason, "decided_at": now.isoformat()}, open(tmp, "w"))
    os.replace(tmp, STATE_FILE)                       # atomic write
    return k


# =============================================================================================
# 3 + 4. Targets and execution on the competition venue
# =============================================================================================

class Agent:
    def __init__(self, live):
        from hyperliquid.info import Info
        from hyperliquid.utils import constants
        self.address = os.environ.get("TEAM_WALLET_ADDRESS", "")
        self.info = Info(constants.TESTNET_API_URL, skip_ws=True, perp_dexs=[DEX])
        self.exchange = None
        if live:
            import eth_account
            from hyperliquid.exchange import Exchange
            wallet = eth_account.Account.from_key(os.environ["API_WALLET_KEY"])
            self.exchange = Exchange(wallet, constants.TESTNET_API_URL, account_address=self.address,
                                     perp_dexs=[DEX])
        self.markets = [venue(c) for c in MARKETS]
        self.spec = {m["name"]: m for m in self.info.meta(dex=DEX)["universe"]}
        missing = [m for m in self.markets if m not in self.spec]
        if missing:
            raise SystemExit(f"markets not listed on {DEX}: {missing}")
        self.resting = {}          # coin -> (order id, is_buy, price) of our passive child order
        self.leverage_set = False

    # ---------------- exchange state (the exchange is always the source of truth)
    def positions(self):
        if not self.address:
            return {}
        st = self.info.user_state(self.address, dex=DEX)
        return {venue(p["position"]["coin"]): float(p["position"]["szi"]) for p in st.get("assetPositions", [])}

    def mids(self):
        return {k: float(v) for k, v in self.info.all_mids(dex=DEX).items()}

    def best_bid_ask(self, coin):
        levels = self.info.l2_snapshot(coin).get("levels", [[], []])
        bid = float(levels[0][0]["px"]) if levels[0] else None
        ask = float(levels[1][0]["px"]) if levels[1] else None
        return bid, ask

    def mainnet_fair(self):
        """Mainnet mid prices, used as fair value to cap our passive prices."""
        mids = {}
        for dex in ("", "xyz"):
            try:
                mids.update(mainnet_post({"type": "allMids", **({"dex": dex} if dex else {})}))
            except Exception as e:
                log.warning("mainnet mids (%s) failed: %s", dex or "main", e)
        return {venue(c): float(mids[ref]) for c, ref in MARKETS.items() if ref in mids}

    # ---------------- step 3: targets (report Eq. 1 with the size from Eq. 3)
    def targets(self, signals, k):
        """Target position (in coins) per market: sign * k * C0/10, capped per market."""
        per_market = min(k * UNIT_FRACTION * INITIAL_CAPITAL, MAX_NOTIONAL_PER_MARKET)
        mids = self.mids()
        target = {}
        for coin in self.markets:
            if mids.get(coin, 0) <= 0:
                log.warning("%s: no mid price, skipped", coin)
                continue
            target[coin] = signals.get(coin, 0) * floor_size(per_market / mids[coin], self.spec[coin]["szDecimals"])
        return target, mids, per_market

    def remaining(self, target, mids, per_market):
        """Signed size still to trade per market; differences below the no-trade band are ignored."""
        pos = self.positions()
        out = {}
        for coin, tgt in target.items():
            delta = tgt - pos.get(coin, 0.0)
            size = floor_size(delta, self.spec[coin]["szDecimals"])
            if size * mids[coin] >= max(10.0, NO_TRADE_BAND * per_market):
                out[coin] = math.copysign(size, delta)
        return out, pos

    # ---------------- orders
    def set_leverage(self):
        if self.leverage_set or not self.exchange:
            return
        for coin in self.markets:
            self.exchange.update_leverage(int(min(MARGIN_LEVERAGE, self.spec[coin]["maxLeverage"])), coin,
                                          is_cross=True)
        self.leverage_set = True

    def place(self, coin, is_buy, size, px, tif, reduce_only=False):
        """Send one limit order. tif = 'Alo' (post-only) or 'Ioc'. Returns the order id if it rests."""
        d = self.spec[coin]["szDecimals"]
        px = round_price(px, d)
        if size * px < 10:                            # exchange minimum order value
            return None
        if not self.exchange:
            log.info("[dry run] %s %s %.6g @ %s (%s)", coin, "BUY " if is_buy else "SELL", size, px, tif)
            return None
        try:
            res = self.exchange.order(coin, is_buy, size, px, {"limit": {"tif": tif}}, reduce_only=reduce_only)
        except Exception as e:
            log.warning("%s %s order failed (%s) - retried at the next step", coin, tif, e)
            return None
        st, err = order_statuses(res)
        if err:
            log.error("%s %s: %s", coin, tif, err)
            return None
        s = st[0] if st else {}
        with open(TRADE_LOG, "a", newline="") as f:
            csv.writer(f).writerow([datetime.now(timezone.utc).isoformat(), coin,
                                    "BUY" if is_buy else "SELL", size, px, tif, s])
        if "resting" in s:
            return s["resting"]["oid"]
        if "filled" in s:
            log.info("%s %s filled %s @ %s", coin, tif, s["filled"]["totalSz"], s["filled"]["avgPx"])
        return None

    def cancel(self, coin, oid):
        """Errors are logged, not raised: a failed cancel usually means the order just filled."""
        if not self.exchange:
            return
        try:
            self.exchange.cancel(coin, oid)
        except Exception as e:
            log.warning("cancel %s %s failed (%s)", coin, oid, e)

    def cancel_all(self):
        if not self.exchange:
            return
        for o in self.info.open_orders(self.address, dex=DEX):
            if venue(o["coin"]) in self.markets:
                self.cancel(venue(o["coin"]), o["oid"])
        self.resting.clear()

    def passive_price(self, coin, is_buy, fair):
        """One tick inside the spread (best price on the book), capped against mainnet fair value,
        and never crossing the spread (a post-only order that would cross is rejected)."""
        bid, ask = self.best_bid_ask(coin)
        d = self.spec[coin]["szDecimals"]
        ref = bid if is_buy else ask
        if ref is None:
            return None
        tk = price_tick(ref, d)
        if is_buy:
            px = bid + tk if (ask is None or bid + tk < ask) else bid
            if fair:
                px = min(px, fair * (1 + FAIR_CAP_BPS / 1e4))
            if ask is not None and px >= ask:
                px = ask - tk
        else:
            px = ask - tk if (bid is None or ask - tk > bid) else ask
            if fair:
                px = max(px, fair * (1 - FAIR_CAP_BPS / 1e4))
            if bid is not None and px <= bid:
                px = bid + tk
        return round_price(px, d)

    def patient_step(self, rem, target, mids):
        """Keep exactly one passive child order per market that still needs trading. An order that is
        still at the right price is left alone, so it keeps its place in the queue."""
        fair = self.mainnet_fair()
        live = {o["oid"]: o for o in self.info.open_orders(self.address, dex=DEX)} if self.exchange else {}
        tracked = {v[0] for v in self.resting.values()}
        for oid, o in live.items():                   # orphans (e.g. after a failed cancel)
            if oid not in tracked and venue(o["coin"]) in self.markets:
                self.cancel(venue(o["coin"]), oid)
        for coin in self.markets:
            want, old = rem.get(coin), self.resting.get(coin)
            if old and old[0] not in live:            # filled or gone
                self.resting.pop(coin, None)
                old = None
            if want is None:                          # nothing (more) to do here
                if old:
                    self.cancel(coin, old[0])
                    self.resting.pop(coin, None)
                continue
            is_buy = want > 0
            size = floor_size(min(abs(want), SLICE_USD / mids[coin]), self.spec[coin]["szDecimals"])
            px = self.passive_price(coin, is_buy, fair.get(coin))
            if px is None or size <= 0:
                continue
            if old and old[1] == is_buy and abs(old[2] - px) < 1e-12:
                continue
            if old:
                self.cancel(coin, old[0])
                self.resting.pop(coin, None)
            oid = self.place(coin, is_buy, size, px, "Alo", reduce_only=(target[coin] == 0))
            if oid is not None:
                self.resting[coin] = (oid, is_buy, px)

    def take_remainder(self, target, per_market):
        """Fallback after the patient window: IOC slices within IOC_SLIPPAGE of mid."""
        mids = self.mids()
        rem, _ = self.remaining(target, mids, per_market)
        for _ in range(IOC_MAX_SLICES):
            if not rem:
                break
            for coin, want in rem.items():
                is_buy = want > 0
                size = floor_size(min(abs(want), SLICE_USD / mids[coin]), self.spec[coin]["szDecimals"])
                px = mids[coin] * (1 + IOC_SLIPPAGE if is_buy else 1 - IOC_SLIPPAGE)
                self.place(coin, is_buy, size, px, "Ioc", reduce_only=(target[coin] == 0))
            time.sleep(IOC_PAUSE_S)
            mids = self.mids()
            rem, _ = self.remaining(target, mids, per_market)

    # ---------------- one daily rebalance
    def rebalance(self):
        t0 = int(time.time() * 1000)
        log.info("=" * 70)
        log.info("rebalance %s UTC (%s)", datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M"),
                 "LIVE" if self.exchange else "DRY RUN")
        self.set_leverage()
        self.cancel_all()
        k = choose_size(persist=self.exchange is not None)        # step 2
        signals = all_signals()                                   # step 1
        target, mids, per_market = self.targets(signals, k)       # step 3
        rem, pos = self.remaining(target, mids, per_market)
        log.info("size k = %g -> $%.0f per market", k, per_market)
        for coin in self.markets:
            if coin in target:
                log.info("%-11s position %+12.4f  target %+12.4f  to trade %+12.4f (~$%.0f)", coin,
                         pos.get(coin, 0.0), target[coin], rem.get(coin, 0.0), abs(rem.get(coin, 0.0)) * mids[coin])
        if not rem:
            log.info("nothing to trade")
            return
        # step 4a: patient passive execution
        deadline = time.time() + PATIENT_WINDOW_MIN * 60
        while rem and time.time() < deadline:
            try:
                self.patient_step(rem, target, mids)
            except Exception as e:
                log.warning("patient step failed (%s) - retried at the next step", e)
            if not self.exchange:
                log.info("[dry run] the passive orders above would be refreshed every %d s for %d min",
                         PATIENT_STEP_S, PATIENT_WINDOW_MIN)
                return
            time.sleep(PATIENT_STEP_S)
            try:
                mids = {**mids, **self.mids()}
                rem, _ = self.remaining(target, mids, per_market)
            except Exception as e:
                log.warning("could not refresh positions (%s)", e)
        # step 4b: take what is left
        self.cancel_all()
        self.take_remainder(target, per_market)
        self.report(t0)

    def report(self, t0):
        """Maker share and fees of this rebalance, from our own fills."""
        try:
            fills = self.info.post("/info", {"type": "userFillsByTime", "user": self.address, "startTime": t0}) or []
        except Exception as e:
            log.warning("could not read fills: %s", e)
            return
        fills = [f for f in fills if str(f.get("coin", "")).startswith(f"{DEX}:")]
        if not fills:
            return
        maker = sum(float(f["px"]) * float(f["sz"]) for f in fills if not f.get("crossed"))
        total = sum(float(f["px"]) * float(f["sz"]) for f in fills)
        fees = sum(float(f["fee"]) for f in fills)
        log.info("traded $%.0f | maker %.0f%% | fees $%.2f (%.2f bps)", total, 100 * maker / total, fees,
                 1e4 * fees / total)


# =============================================================================================
# Operations: retries and daily schedule
# =============================================================================================

def run_rebalance(agent):
    """A failed rebalance is retried after cancelling all resting orders. This is safe because every
    rebalance starts from the actual positions on the exchange."""
    for attempt in range(1, REBALANCE_ATTEMPTS + 1):
        try:
            agent.rebalance()
            ping("", f"rebalance OK {datetime.now(timezone.utc):%Y-%m-%d %H:%M} UTC")
            return
        except Exception:
            log.exception("rebalance attempt %d/%d failed", attempt, REBALANCE_ATTEMPTS)
            try:
                agent.cancel_all()
            except Exception:
                log.exception("cancel_all failed too - check open orders")
            if attempt < REBALANCE_ATTEMPTS:
                time.sleep(RETRY_WAIT_S)
    ping("fail", "rebalance failed after all attempts - check the log")


def next_rebalance_time():
    now = datetime.now(timezone.utc)
    nxt = now.replace(hour=REBALANCE_HOUR, minute=REBALANCE_MINUTE, second=0, microsecond=0)
    return nxt if nxt > now else nxt + timedelta(days=1)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--live", action="store_true", help="send orders (default: dry run, nothing is sent)")
    ap.add_argument("--once", action="store_true", help="rebalance once now and exit")
    a = ap.parse_args()

    logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s",
                        handlers=[logging.FileHandler("agent.log"), logging.StreamHandler()])
    logging.Formatter.converter = time.gmtime
    load_dotenv()
    install_request_timeout(HTTP_TIMEOUT_S)

    # Hard limit: the largest size the policy can choose must stay within MAX_GROSS_MULTIPLE x capital.
    largest_book = len(MARKETS) * min(K_HIGH * UNIT_FRACTION * INITIAL_CAPITAL, MAX_NOTIONAL_PER_MARKET)
    if largest_book > MAX_GROSS_MULTIPLE * INITIAL_CAPITAL:
        raise SystemExit("configuration exceeds the gross-exposure limit; refusing to start")

    agent = Agent(live=a.live)
    if a.once:
        run_rebalance(agent)
        return
    ping("start", "agent started")
    if a.live:
        agent.cancel_all()          # clear anything left by a crash or restart
    while True:
        nxt = next_rebalance_time()
        log.info("next rebalance %s UTC", nxt.strftime("%Y-%m-%d %H:%M"))
        last_beat = time.time()
        # Check the wall clock every minute instead of one long sleep (a long sleep can be paused
        # while the machine sleeps and silently skip a rebalance); send an hourly heartbeat.
        while datetime.now(timezone.utc) < nxt:
            time.sleep(max(1.0, min(60.0, (nxt - datetime.now(timezone.utc)).total_seconds())))
            if time.time() - last_beat >= 3600:
                ping("", f"alive, next rebalance {nxt:%Y-%m-%d %H:%M} UTC")
                last_beat = time.time()
        run_rebalance(agent)


if __name__ == "__main__":
    main()
