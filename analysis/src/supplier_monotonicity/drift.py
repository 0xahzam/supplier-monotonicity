"""Exposure of real suppliers on two Drift spot markets (USDC and SOL).

Inputs are the pseudonymized snapshot in ``data/drift``:

* ``markets.csv.gz``: the last ``SpotInterestRecord`` of each hour, from 2024-11-11 to
  2026-04-01. Scaled deposit and borrow balances, cumulative interest indices and the
  rate curve parameters in force.
* ``balances.csv.gz``: for each account and each hour with a deposit or withdrawal from
  2025-12-01 on, the account's balance after the last event of the hour and before the
  first one, with the interest indices at those events. Accounts are numbered, and
  subaccounts of one owner share a supplier number.
* ``suppliers.csv``: whether a supplier settled perpetual futures profit or loss in the
  window, which marks deposits that also serve as trading collateral.

Every hour gets equal weight. The protected share uses the slope of the segment below
the current utilization, the side a deposit moves to.
"""

from __future__ import annotations

import csv
import gzip
import math
from collections import defaultdict
from pathlib import Path

import numpy as np

P = 1_000_000
YEAR = 365.25 * 24 * 3600
#: INTEREST_RATE_SEGMENT_AND_WEIGHTS: breakpoints above the kink and their share of the
#: rate range, in thousandths.
SEGMENTS = [(850_000, 50), (900_000, 100), (950_000, 150), (990_000, 200), (995_000, 250)]
SEGMENTS.append((1_000_000, 250))
#: Release v2.121.0, the first with the segmented curve. Before it the curve is one line
#: from the kink to the maximum. Below the kink both are identical.
SWITCH = 1748476800
DECIMALS = {"USDC": 6, "SOL": 9}
#: First hour with recorded balances after each deposit or withdrawal.
WINDOW_START = 1764547200


def knots(optu: int, optr: int, maxr: int, segmented: bool) -> list[tuple[float, float]]:
    """Breakpoints ``(utilization, borrow rate)`` of the curve, as fractions of one."""
    pts = [(0.0, 0.0), (optu / P, optr / P)]
    if not segmented:
        return pts + [(1.0, maxr / P)]
    rate, prev = optr, optu
    for bp, weight in SEGMENTS:
        if bp > prev:
            rate += (maxr - optr) * weight / 1000
            pts.append((bp / P, rate / P))
            prev = bp
    return pts


def rate_and_slope(u: float, pts: list[tuple[float, float]]) -> tuple[float, float]:
    """Rate at ``u`` and the slope of the segment that ends at or above ``u``."""
    for (u0, r0), (u1, r1) in zip(pts, pts[1:]):
        if u <= u1:
            m = (r1 - r0) / (u1 - u0)
            return r0 + m * (u - u0), m
    return pts[-1][1], 0.0


def _rows(path: Path):
    with gzip.open(path, "rt") as f:
        yield from csv.DictReader(f)


def load_markets(data: Path) -> dict[str, list[dict]]:
    out = defaultdict(list)
    for r in _rows(data / "markets.csv.gz"):
        out[r["market"]].append({k: (v if k == "market" else int(v)) for k, v in r.items()})
    for rows in out.values():
        rows.sort(key=lambda r: r["hour"])
    return dict(out)


def utilization(r: dict) -> float:
    dep = r["depositbalance"] * r["cumdep"]
    return r["borrowbalance"] * r["cumbor"] / dep if dep else 0.0


def curve(r: dict) -> list[tuple[float, float]]:
    return knots(r["optu"], r["optr"], r["maxr"], r["hour"] >= SWITCH)


def fit(rows: list[dict]) -> dict[str, float]:
    """Median relative error of the curve against the borrow rate implied by the growth of
    the borrow index between consecutive hours, above and below the kink."""
    above, below = [], []
    for a, b in zip(rows, rows[1:]):
        dt = (b["last_ts"] - a["last_ts"]) / YEAR
        if dt <= 0 or b["hour"] - a["hour"] != 3600 or b["cumbor"] <= a["cumbor"]:
            continue
        implied = math.log(b["cumbor"] / a["cumbor"]) / dt
        u = (utilization(a) + utilization(b)) / 2
        r, _ = rate_and_slope(u, curve(a))
        (above if u > a["optu"] / P + 0.01 else below).append(abs(r - implied) / implied)
    med = lambda v: float(np.median(v)) if v else float("nan")
    return {"above_kink": med(above), "below_kink": med(below), "hours_above": len(above)}


def hourly(rows: list[dict], start: int | None = None) -> list[dict]:
    """One state per hour, the last record carried forward through hours without one."""
    out, i = [], 0
    h = rows[0]["hour"] if start is None else start
    while h <= rows[-1]["hour"]:
        while i + 1 < len(rows) and rows[i + 1]["hour"] <= h:
            i += 1
        out.append({**rows[i], "hour": h})
        h += 3600
    return out


def safe_share(r: dict) -> tuple[float, float]:
    """Utilization and the largest protected share at that state."""
    u = utilization(r)
    rate, slope = rate_and_slope(u, curve(r))
    eta = u * slope / rate if rate > 0 else 0.0
    return u, 1 / (1 + eta)


def market_summary(rows: list[dict], start: int | None = None) -> dict[str, float]:
    grid = hourly(rows, start)
    us = np.array([safe_share(r) for r in grid])
    above = us[:, 0] > np.array([r["optu"] / P for r in grid])
    return {
        "start": grid[0]["hour"],
        "end": grid[-1]["hour"],
        "hours": len(grid),
        "above_kink": float(above.mean()),
        "safe_below_5": float((us[:, 1] < 0.05).mean()),
        "safe_below_1": float((us[:, 1] < 0.01).mean()),
        "median_safe_above_kink": float(np.median(us[above, 1])) if above.any() else float("nan"),
    }


def _scaled(token: float, depidx: float, boridx: float) -> float:
    return token / depidx if token >= 0 else token / boridx


def suppliers(data: Path, market: str, rows: list[dict]) -> dict:
    """Rebuild supplier balances from recorded balances and measure exposure."""
    grid = hourly(rows, WINDOW_START)
    hours = np.array([r["hour"] for r in grid])
    depidx = np.array([float(r["cumdep"]) for r in grid])
    boridx = np.array([float(r["cumbor"]) for r in grid])
    total = np.array(
        [r["depositbalance"] * r["cumdep"] / 10 ** (19 - DECIMALS[market]) for r in grid]
    )
    util, safe = np.array([safe_share(r) for r in grid]).T
    with open(data / "suppliers.csv") as f:
        trader = {r["supplier"]: r["perp_trader"] == "1" for r in csv.DictReader(f)}

    events = defaultdict(lambda: defaultdict(list))
    for r in _rows(data / "balances.csv.gz"):
        if r["market"] == market:
            events[r["supplier"]][r["account"]].append(r)

    rebuilt = np.zeros(len(hours))
    largest = np.zeros(len(hours))
    largest_lender = np.zeros(len(hours))
    exposed_any = np.zeros(len(hours), bool)
    exposed_lender = np.zeros(len(hours), bool)
    gaps, profile = [], []
    for supplier, accounts in events.items():
        balance = np.zeros(len(hours))
        for evs in accounts.values():
            evs.sort(key=lambda r: int(r["hour"]))
            f = evs[0]
            steps = [
                (
                    WINDOW_START,
                    _scaled(
                        float(f["first_before"]), float(f["first_depidx"]), float(f["first_boridx"])
                    ),
                )
            ]
            for a, b in zip(evs, evs[1:]):
                s = _scaled(
                    float(a["last_after"]), float(a["last_depidx"]), float(a["last_boridx"])
                )
                carried = s * (float(b["first_depidx"]) if s >= 0 else float(b["first_boridx"]))
                actual = float(b["first_before"])
                if max(abs(carried), abs(actual)) > 0:
                    gaps.append((supplier, abs(carried - actual) / max(abs(carried), abs(actual))))
            for r in evs:
                steps.append(
                    (
                        int(r["hour"]) + 3600,
                        _scaled(
                            float(r["last_after"]), float(r["last_depidx"]), float(r["last_boridx"])
                        ),
                    )
                )
            times = np.array([t for t, _ in steps])
            values = np.array([v for _, v in steps])
            k = np.searchsorted(times, hours, side="right") - 1
            s = np.where(k >= 0, values[np.clip(k, 0, None)], 0.0)
            balance += np.where(s >= 0, s * depidx, s * boridx)
        supply = np.clip(balance, 0, None)
        share = supply / total
        rebuilt += supply
        largest = np.maximum(largest, share)
        hit = share > safe
        exposed_any |= hit
        if not trader.get(supplier, False):
            largest_lender = np.maximum(largest_lender, share)
            exposed_lender |= hit
        if hit.any():
            profile.append(
                {
                    "supplier": supplier,
                    "perp_trader": trader.get(supplier, False),
                    "hours": int(hit.sum()),
                    "max_share": float(share.max()),
                    "max_share_exposed": float(share[hit].max()),
                }
            )

    coverage = rebuilt / total
    # Continuity matters for the suppliers the bound rests on: the exposed ones.
    exposed = {e["supplier"] for e in profile}
    gap_all = [g for s, g in gaps if s in exposed]
    gap_lender = [g for s, g in gaps if s in exposed and not trader.get(s, False)]
    return {
        "start": int(hours[0]),
        "end": int(hours[-1]),
        "hours": len(hours),
        "above_kink": float((util > np.array([r["optu"] / P for r in grid])).mean()),
        "coverage_median": float(np.median(coverage)),
        "coverage_p5": float(np.percentile(coverage, 5)),
        "coverage_p95": float(np.percentile(coverage, 95)),
        "continuity_exact_all": float(np.mean(np.array(gap_all) <= 0.01)),
        "continuity_exact_lenders": float(np.mean(np.array(gap_lender) <= 0.01)),
        "exposed_hours_any": float(exposed_any.mean()),
        "exposed_hours_lender": float(exposed_lender.mean()),
        "exposed_suppliers": [{k: v for k, v in e.items() if k != "supplier"} for e in profile],
        "series": {
            "hour": hours.tolist(),
            "utilization": util.tolist(),
            "alpha_safe": safe.tolist(),
            "largest_share": largest.tolist(),
            "largest_lender_share": largest_lender.tolist(),
        },
    }


def run(data: Path) -> dict:
    markets = load_markets(data)
    out = {}
    for name in ("SOL", "USDC"):
        rows = markets[name]
        out[name] = {
            "fit": fit(rows),
            "market": market_summary(rows),
            "market_window": market_summary(rows, WINDOW_START),
            "suppliers": suppliers(data, name, rows),
        }
    return out
