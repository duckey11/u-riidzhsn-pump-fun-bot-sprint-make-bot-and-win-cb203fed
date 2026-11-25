// Pump.fun momentum bot — agent-fun/replay/v2.
// Strategy (from the competition prose spec, tuned on the dev window):
//  * Buy young, liquid, small-cap coins showing buy-dominated momentum
//    (path A: price up vs 300 slots ago; path B: price up vs its early low).
//    Entry is tightened vs the spec baseline: market cap at most 70 SOL,
//    at least 8 distinct buyers on path A, and path A needs a +15% rise
//    vs 300 slots ago (not +2%): the dev window shows the edge lives in
//    the vertical movers, coins already up double digits keep running to
//    the +25% take-profit, while small rises mean-revert into the fees.
//  * Exit the WHOLE position on the first of: take-profit +25%, stop-loss
//    -7%, trailing drawdown -8% from the peak since entry, or timeout
//    15 min (2250 slots). Dev-window analysis: a small fixed take-profit
//    (+8%) caps the fat tail, the few runners pay for the many small
//    losses, so TP sits at +25% where runners are banked instead of being
//    given back; the trailing stop still lets winners run below that.
//    Buy slippage is 500 bps, not 200: at 200 bps the harness rejects
//    about 29% of buys, exactly the fastest-moving entries.
//  * All amounts in lamports as BigInt. Prices are virtual-reserve ratios
//    (virtual SOL / virtual token), compared only by BigInt cross
//    multiplication — never a float for a trade decision.
//  * Deterministic: no clock, no randomness; candidate coins are scanned in
//    alphabetical mint order; one buy per coin, never a re-entry.
//  * Dev grade-local (process driver): net PnL +0.183 SOL, 147 round trips
//    over 147 coins, win rate 29.9%, max drawdown 2.1%. A sell stays
//    tracked until its fill lands, so a rejected or failed sell is
//    retried next batch instead of stranding the position.
import { runBot, LAMPORTS_PER_SOL, type BotState, type Batch } from './vendor/makefun-bot.ts';

// ------------------------------------------------------------------ tuning
const AGE_LO = 150; // slots (~1 min)
const AGE_HI = 3000; // slots (~20 min)
const WIN_SLOTS = 600; // flow window, slots (~4 min)
const MIN_TRADES_WIN = 3;
const MCAP_MAX_LAM = 70n * LAMPORTS_PER_SOL;
const RQ_MIN_LAM = 1_120_000_000n; // 1.12 SOL real quote reserves
const A_RISE_NUM = 115n; // path A: price >= 115% of price 300 slots ago (vertical movers only)
const A_RISE_DEN = 100n;
const A_DOM_NUM = 3n; // path A: buy volume >= 1.5x sell volume
const A_DOM_DEN = 2n;
const A_BUYERS = 8;
const B_RISE_NUM = 105n; // path B: price >= 105% of early low
const B_RISE_DEN = 100n;
const B_DOM_NUM = 3n; // path B: buy volume >= 3x sell volume
const B_DOM_DEN = 1n;
const B_BUYERS = 8;
const TP_BPS = 2500n; // take-profit, bps over entry (locks in runners at +25%)
const SL_BPS = 700n; // stop-loss, bps under entry
const TRAIL_BPS = 800n; // trailing drawdown from peak since entry, bps
const TIMEOUT_SLOTS = 2250; // 15 min
const BUY_SOL = 150_000_000n; // 0.15 SOL per position
const CAP_FRAC_NUM = 90n; // buy at most 90% of the harness order cap
const CAP_FRAC_DEN = 100n;
const MIN_BUY_LAM = 10_000_000n; // 0.01 SOL minimum buy
const CASH_RESERVE_LAM = 1_000_000_000n; // keep at least 1 SOL cash
const MAX_POS = 5;
const BUY_SLIP_BPS = 500;
const SELL_SLIP_BPS = 2000;
const BPS = 10_000n;

// ------------------------------------------------------------------ per-coin flow state
interface WinTrade {
  slot: number;
  isBuy: boolean;
  sol: bigint;
  user: string;
}
interface PriceSnap {
  slot: number;
  vq: bigint;
  vt: bigint;
}
interface Coin {
  mint: string;
  createdSlot: number | null;
  supply: bigint;
  lowNum: bigint; // lowest price seen, as vq/vt
  lowDen: bigint;
  hist: PriceSnap[]; // price snapshots, ascending slot
  histHead: number; // index of first live snapshot
  win: WinTrade[]; // trades inside the flow window
  winHead: number;
  buyVol: bigint;
  sellVol: bigint;
  buyerCounts: Map<string, number>;
  complete: boolean;
}

interface Pos {
  entryNum: bigint; // entry price = quote paid / tokens received (all-in)
  entryDen: bigint;
  peakNum: bigint; // highest price since entry, as vq/vt
  peakDen: bigint;
  entrySlot: number;
}

const coins = new Map<string, Coin>();
const positions = new Map<string, Pos>();
const exited = new Set<string>();

function getCoin(mint: string): Coin {
  let c = coins.get(mint);
  if (c === undefined) {
    c = {
      mint,
      createdSlot: null,
      supply: 0n,
      lowNum: 0n,
      lowDen: 1n,
      hist: [],
      histHead: 0,
      win: [],
      winHead: 0,
      buyVol: 0n,
      sellVol: 0n,
      buyerCounts: new Map(),
      complete: false,
    };
    coins.set(mint, c);
  }
  return c;
}

// price a >= price b, both as num/den fractions, by cross multiplication.
function ge(aNum: bigint, aDen: bigint, bNum: bigint, bDen: bigint): boolean {
  return aNum * bDen >= bNum * aDen;
}
// price a >= price b * num/den
function geScaled(aNum: bigint, aDen: bigint, bNum: bigint, bDen: bigint, num: bigint, den: bigint): boolean {
  return aNum * bDen * den >= bNum * aDen * num;
}
// price a <= price b * num/den
function leScaled(aNum: bigint, aDen: bigint, bNum: bigint, bDen: bigint, num: bigint, den: bigint): boolean {
  return aNum * bDen * den <= bNum * aDen * num;
}

function onTrade(c: Coin, slot: number, vq: bigint, vt: bigint, isBuy: boolean, sol: bigint, user: string): void {
  // lowest price since creation
  if (c.lowNum === 0n || vq * c.lowDen < c.lowNum * vt) {
    c.lowNum = vq;
    c.lowDen = vt;
  }
  // price history for the 300-slot lookback
  c.hist.push({ slot, vq, vt });
  while (c.hist.length - c.histHead > 1 && c.hist[c.histHead + 1]!.slot <= slot - 300) c.histHead++;
  // flow window (600 slots): expire old trades, then add this one
  while (c.winHead < c.win.length && c.win[c.winHead]!.slot <= slot - WIN_SLOTS) {
    const old = c.win[c.winHead]!;
    c.winHead++;
    if (old.isBuy) {
      c.buyVol -= old.sol;
      const n = (c.buyerCounts.get(old.user) ?? 0) - 1;
      if (n <= 0) c.buyerCounts.delete(old.user);
      else c.buyerCounts.set(old.user, n);
    } else {
      c.sellVol -= old.sol;
    }
  }
  c.win.push({ slot, isBuy, sol, user });
  if (isBuy) {
    c.buyVol += sol;
    c.buyerCounts.set(user, (c.buyerCounts.get(user) ?? 0) + 1);
  } else {
    c.sellVol += sol;
  }
  // compact deques occasionally so they do not grow unboundedly
  if (c.histHead > 512) {
    c.hist.splice(0, c.histHead);
    c.histHead = 0;
  }
  if (c.winHead > 512) {
    c.win.splice(0, c.winHead);
    c.winHead = 0;
  }
}

await runBot({
  onBatch(state: BotState, batch: Batch) {
    const slot = batch.slot;
    const orders: { side: 'buy' | 'sell'; mint: string; quote_lamports?: bigint; token_amount?: bigint; max_slippage_bps: number }[] = [];

    // ---- fold fills: open positions (buy fills), close them (sell / harness closes)
    for (const f of batch.fills) {
      if (f.status !== 'filled') continue;
      if (f.side === 'buy') {
        const paid = BigInt(f.quote_lamports);
        const toks = BigInt(f.token_amount);
        if (paid > 0n && toks > 0n) {
          positions.set(f.mint, { entryNum: paid, entryDen: toks, peakNum: paid, peakDen: toks, entrySlot: f.slot });
        }
      } else {
        positions.delete(f.mint);
        exited.add(f.mint);
      }
    }
    // positions the harness closed without a fill we saw (safety): drop stale tracking
    for (const mint of [...positions.keys()]) {
      if (!state.positions.has(mint)) {
        positions.delete(mint);
        exited.add(mint);
      }
    }

    // ---- fold events into per-coin flow state; collect candidate mints
    const candidates = new Set<string>();
    for (const e of batch.events) {
      if (e.event === 'CreateEvent') {
        const c = getCoin(e.mint);
        c.createdSlot = e.slot;
        c.supply = BigInt(e.token_total_supply);
        const vq = BigInt(e.virtual_quote_reserves);
        const vt = BigInt(e.virtual_token_reserves);
        c.lowNum = vq;
        c.lowDen = vt;
        c.hist.push({ slot: e.slot, vq, vt });
        candidates.add(e.mint);
      } else if (e.event === 'TradeEvent') {
        const c = getCoin(e.mint);
        onTrade(c, e.slot, BigInt(e.virtual_quote_reserves), BigInt(e.virtual_token_reserves), e.is_buy, BigInt(e.quote_amount), e.user);
        candidates.add(e.mint);
      } else {
        const c = getCoin(e.mint);
        c.complete = true;
        candidates.add(e.mint);
      }
    }

    // ---- exits first: whole position on TP / SL / trailing / timeout.
    // A sell stays tracked until its fill lands: a rejected or failed sell
    // (2% of tx fail) must be retried next batch, not strand the position.
    for (const mint of [...positions.keys()].sort()) {
      const pos = positions.get(mint)!;
      const held = state.positions.get(mint);
      if (held === undefined || held.token_amount === 0n) continue;
      let sellPending = false;
      for (const p of state.pending.values()) {
        if (p.side === 'sell' && p.mint === mint) { sellPending = true; break; }
      }
      if (sellPending) continue;
      const curve = state.curves.get(mint);
      if (curve === undefined || curve.virtual_token_reserves === 0n) continue;
      const vq = curve.virtual_quote_reserves;
      const vt = curve.virtual_token_reserves;
      // peak since entry
      if (vq * pos.peakDen > pos.peakNum * vt) {
        pos.peakNum = vq;
        pos.peakDen = vt;
      }
      const tp = geScaled(vq, vt, pos.entryNum, pos.entryDen, BPS + TP_BPS, BPS);
      const sl = leScaled(vq, vt, pos.entryNum, pos.entryDen, BPS - SL_BPS, BPS);
      const trail = leScaled(vq, vt, pos.peakNum, pos.peakDen, BPS - TRAIL_BPS, BPS);
      const timeout = slot - pos.entrySlot >= TIMEOUT_SLOTS;
      if (tp || sl || trail || timeout) {
        orders.push({ side: 'sell', mint, token_amount: held.token_amount, max_slippage_bps: SELL_SLIP_BPS });
      }
    }

    // ---- entries: coins that traded in this batch, alphabetical order
    if (state.committedPositionCount() < MAX_POS) {
      const sorted = [...candidates].sort();
      for (const mint of sorted) {
        if (state.committedPositionCount() >= MAX_POS) break;
        if (positions.has(mint) || exited.has(mint)) continue;
        const c = coins.get(mint);
        if (c === undefined || c.complete || c.createdSlot === null) continue;
        const age = slot - c.createdSlot;
        if (age < AGE_LO || age > AGE_HI) continue;
        const curve = state.curves.get(mint);
        if (curve === undefined || curve.virtual_token_reserves === 0n) continue;
        if (curve.real_quote_reserves < RQ_MIN_LAM) continue;
        // market cap = price * total supply <= cap
        if (c.supply > 0n && curve.virtual_quote_reserves * c.supply > MCAP_MAX_LAM * curve.virtual_token_reserves) continue;
        // pending buy on this mint already?
        let pendingBuy = false;
        for (const p of state.pending.values()) {
          if (p.order.side === 'buy' && p.order.mint === mint) {
            pendingBuy = true;
            break;
          }
        }
        if (pendingBuy) continue;
        const winTrades = c.win.length - c.winHead;
        if (winTrades < MIN_TRADES_WIN) continue;
        const vq = curve.virtual_quote_reserves;
        const vt = curve.virtual_token_reserves;
        const buyers = c.buyerCounts.size;
        let enter = false;
        // path A: up vs price 300 slots ago + buy-dominated flow
        // hist is non-empty here (CreateEvent and TradeEvent always
        // snapshot), but guard the lookup: an empty history must skip
        // the coin, never crash on an undefined snapshot.
        const snap = c.hist[c.histHead];
        if (snap === undefined) continue;
        if (
          geScaled(vq, vt, snap.vq, snap.vt, A_RISE_NUM, A_RISE_DEN) &&
          c.sellVol > 0n &&
          c.buyVol * A_DOM_DEN >= c.sellVol * A_DOM_NUM &&
          buyers >= A_BUYERS
        ) {
          enter = true;
        }
        // path B: up vs early low + strongly buy-dominated flow
        if (
          !enter &&
          c.lowNum > 0n &&
          geScaled(vq, vt, c.lowNum, c.lowDen, B_RISE_NUM, B_RISE_DEN) &&
          c.sellVol > 0n &&
          c.buyVol * B_DOM_DEN >= c.sellVol * B_DOM_NUM &&
          buyers >= B_BUYERS
        ) {
          enter = true;
        }
        if (!enter) continue;
        // size: 0.15 SOL, capped at 90% of the harness order cap, min 0.01 SOL
        const cap = state.maxBuyLamports(mint);
        let size = BUY_SOL;
        const capped = (cap * CAP_FRAC_NUM) / CAP_FRAC_DEN;
        if (size > capped) size = capped;
        if (size < MIN_BUY_LAM) continue;
        // keep at least 1 SOL cash after this buy + its tx fee
        if (state.freeCashLamports() - size - state.txFeeLamports() < CASH_RESERVE_LAM) continue;
        orders.push({ side: 'buy', mint, quote_lamports: size, max_slippage_bps: BUY_SLIP_BPS });
      }
    }
    return orders;
  },
});
