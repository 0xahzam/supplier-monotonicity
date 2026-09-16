"""Illustrative USDT market analysis and publication-sized figures.

Uses only numpy/matplotlib and the existing supplier_monotonicity package. Outputs stay
beside this script. Source files are hashed in data/provenance.json.
"""

import csv
import hashlib
import json
import re
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib import font_manager
from matplotlib.ticker import PercentFormatter
from supplier_monotonicity.curve import SEGMENTS, Market, borrow_rate_int, breakpoints
from supplier_monotonicity.envelope import fixed_share_cap

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "data"
OUT.mkdir(exist_ok=True)
FIGDIR = ROOT.parent / "figures"
FIGDIR.mkdir(exist_ok=True)
param_path = ROOT / "config/market.json"
params = json.loads(param_path.read_text())
assert [tuple(row) for row in params["segments"]] == SEGMENTS
market = Market(
    "USDT",
    params["optimal_utilization"],
    params["optimal_borrow_rate"],
    params["max_borrow_rate"],
    params["min_borrow_rate"],
)
pts = breakpoints(market)
U = np.array([float(u) / 1e6 for u, r in pts])
BASE = np.array([float(r) / 1e6 for u, r in pts])
# Include the analytical floor crossing as a fixed knot for every comparison.
W = np.r_[np.diff(U)[0] / 2, (U[2:] - U[:-2]) / 2, np.diff(U)[-1] / 2]
FEE = params["carveout_factor"] / 1e6
LENDER = 1 - FEE  # any additional fee beyond this carveout is assumed zero
checks = []
figures = []


def write_csv(name, data):
    with (OUT / f"{name}.csv").open("w") as f:
        writer = csv.writer(f)
        writer.writerow(data.keys())
        writer.writerows(zip(*data.values()))


def curve(r, u):
    u = np.asarray(u)
    i = np.clip(np.searchsorted(U, u, side="left") - 1, 0, len(U) - 2)
    return np.interp(u, U, r), np.diff(r)[i] / np.diff(U)[i]


def caps(policy, alpha=0.05):
    fresh = 1 + np.diff(U) / (1 - U[:-1])
    fixed = np.array(
        [
            fixed_share_cap(float(lo), float(hi), (1 - alpha) / alpha)
            for lo, hi in zip(U[:-1], U[1:])
        ]
    )
    return fresh if policy == "fresh" else fixed if policy == "fixed" else np.minimum(fresh, fixed)


def mixed_projection(cap):
    """Unique weighted least-squares projection of knot APRs onto constraints.

    Objective sum_i W_i (r_i-baseline_i)^2, trapezoidal node weights W.
    Dykstra's algorithm for Euclidean projection after diagonal rescaling.
    These weights define a node-based objective, not exact continuous L2 error.
    """
    sw = np.sqrt(W)
    n = len(U)
    rows = []
    rhs = []
    for i, c in enumerate(cap):
        row = np.zeros(n)
        row[i] = 1 / sw[i]
        row[i + 1] = -1 / sw[i + 1]
        rows.append(row)
        rhs.append(0.0)
        if np.isfinite(c):
            row = np.zeros(n)
            row[i] = -c / sw[i]
            row[i + 1] = 1 / sw[i + 1]
            rows.append(row)
            rhs.append(0.0)
    row = np.zeros(n)
    row[-1] = 1 / sw[-1]
    rows.append(row)
    rhs.append(BASE[-1])
    A = np.array(rows)
    b = np.array(rhs)
    norm = np.linalg.norm(A, axis=1)
    A /= norm[:, None]
    b /= norm
    x = sw * BASE
    correction = np.zeros(len(A))
    for _iteration in range(100000):
        previous = x.copy()
        for i, row in enumerate(A):
            v = x + correction[i] * row
            distance = float(row @ v - b[i])
            if i != len(A) - 1:
                distance = max(0.0, distance)
            x = v - distance * row
            correction[i] = distance
        if np.max(abs(x - previous)) < 1e-13 and np.max(A[:-1] @ x - b[:-1]) < 1e-11:
            break
    else:
        raise RuntimeError("Mixed projection failed to converge")
    r = x / sw
    # KKT certificate: feasible x, nonnegative multipliers, complementarity,
    # and x + sum(lambda_i normal_i) = original point.
    assert np.min(correction[:-1]) >= -1e-12
    assert np.max(abs(correction[:-1] * (A[:-1] @ x - b[:-1]))) < 1e-9
    assert np.max(abs(x + A.T @ correction - sw * BASE)) < 1e-9
    return r


def repairs(policy, alpha=0.05, mixed=True):
    c = caps(policy, alpha)
    floor = np.zeros_like(BASE)
    up = BASE.copy()
    down = BASE.copy()
    floor[-1] = BASE[-1]
    for i in range(len(c) - 1, -1, -1):
        floor[i] = floor[i + 1] / c[i]
        up[i] = max(BASE[i], up[i + 1] / c[i])
    # Greatest compliant minorant preserving the original base (top is free).
    for i in range(len(c)):
        down[i + 1] = min(BASE[i + 1], down[i] * c[i]) if np.isfinite(c[i]) else BASE[i + 1]
    result = {"Baseline": BASE, "Floor": floor, "Raise only": up, "Lower only": down}
    if mixed:
        result["Mixed"] = mixed_projection(c)
    for name, r in result.items():
        if name == "Baseline":
            continue
        assert np.min(np.diff(r)) >= -1e-9 and np.min(r) >= -1e-10
        finite = np.isfinite(c)
        assert np.max(r[1:][finite] - c[finite] * r[:-1][finite]) < 1e-8
        if name != "Lower only":
            assert abs(r[-1] - BASE[-1]) < 1e-10
    assert np.min(up - BASE) >= -1e-10 and np.max(down - BASE) <= 1e-10
    if mixed:
        cost = lambda r: np.sum(W * (r - BASE) ** 2)
        assert cost(result["Mixed"]) <= min(cost(up), cost(floor)) + 1e-9
    return result


def supplier(r, x, initial=0.0, supply=1e6, borrows=990000.0):
    total = supply + x
    balance = initial + x
    util = borrows / total
    rate, slope = curve(r, util)
    return LENDER * balance * util * rate, LENDER * util * (
        rate - balance / total * (rate + util * slope)
    )


# All utilization ticks, including every breakpoint and floor transition.
ticks = np.arange(1000001)
onchain = np.fromiter((borrow_rate_int(int(u), market) for u in ticks), dtype=np.int64)
rational = np.interp(ticks / 1e6, U, BASE)
err = np.max(abs(onchain / 1e6 - rational))
assert err < 1e-6
checks.append(
    f"Integer port compared with rational interpolation at all 1,000,001 utilization ticks; maximum APR difference {err:.12g}."
)
sets = {policy: repairs(policy) for policy in ["fresh", "fixed", "both"]}
for policy, rs in sets.items():
    for name, r in rs.items():
        if name == "Baseline":
            continue
        for j in range(len(U) - 1):
            slope = (r[j + 1] - r[j]) / (U[j + 1] - U[j])
            if policy in ["fresh", "both"]:
                assert (1 - U[j]) * slope <= r[j] + 1e-8
            if policy in ["fixed", "both"]:
                assert U[j] * slope <= 19 * r[j] + 1e-8
                assert U[j + 1] * slope <= 19 * r[j + 1] + 1e-8
        x = np.linspace(100, 200000, 200)
        v = 990000 / (1e6 + x)
        away = np.min(abs(v[:, None] - U[None, :]), axis=1) > 1e-5
        numerical = (supplier(r, x + 0.01)[0] - supplier(r, x - 0.01)[0]) / 0.02
        assert np.allclose(numerical[away], supplier(r, x)[1][away], atol=1e-7)
checks.append(
    "All repairs pass exact segment-endpoint envelope checks; mixed solutions satisfy KKT certificates and beat floor/raise-only squared-error objectives; income derivatives agree with finite differences."
)

import shutil
import subprocess

if shutil.which("kpsewhich"):
    font = subprocess.check_output(["kpsewhich", "lmroman10-regular.otf"], text=True).strip()
    if font:
        font_manager.fontManager.addfont(font)
plt.rcParams.update(
    {
        "font.family": "serif",
        "font.serif": ["Latin Modern Roman", "DejaVu Serif"],
        "font.size": 8,
        "axes.labelsize": 8,
        "xtick.labelsize": 7,
        "ytick.labelsize": 7,
        "legend.fontsize": 7,
        "lines.linewidth": 1.1,
        "axes.linewidth": 0.55,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.grid": False,
        "xtick.major.width": 0.5,
        "ytick.major.width": 0.5,
        "xtick.major.size": 3,
        "ytick.major.size": 3,
        "text.parse_math": False,
        "pdf.fonttype": 42,
        "svg.fonttype": "none",
        "savefig.facecolor": "white",
        "legend.frameon": False,
    }
)
COL = {
    "Baseline": "#202020",
    "Floor": "#a65e42",
    "Raise only": "#346e91",
    "Mixed": "#687743",
    "Lower only": "#80577b",
}
LS = {
    "Baseline": "-",
    "Floor": "--",
    "Raise only": "-.",
    "Mixed": ":",
    "Lower only": (0, (5, 2, 1, 2)),
}
LABEL = {
    "fresh": "Fresh-depositor constraint",
    "fixed": "Fixed share (5%)",
    "both": "Both constraints",
}


def figgrid(rows=1, cols=2, legend=True, names=None, legend_labels=None):
    f, axes = plt.subplots(rows, cols, figsize=(5.9, 2.55 if rows == 1 else 4.7), squeeze=False)
    f.subplots_adjust(
        left=0.12,
        right=0.955,
        bottom=0.20 if rows == 1 else 0.12,
        top=(0.80 if rows == 1 else 0.87) if legend else 0.90,
        wspace=0.42,
        hspace=0.55,
    )
    for i, ax in enumerate(axes.flat):
        ax.text(0, 1.035, f"({chr(97 + i)})", transform=ax.transAxes, fontsize=8)
    if legend:
        from matplotlib.lines import Line2D

        names = names or ["Baseline", "Floor", "Raise only", "Mixed"]
        f.legend(
            [Line2D([], [], color=COL[n], ls=LS[n], lw=1.2) for n in names],
            legend_labels or names,
            loc="upper center",
            bbox_to_anchor=(0.54, 0.99),
            ncol=len(names),
            columnspacing=1.1,
            handlelength=2.5,
        )
    return f, axes


def plot(ax, u, rs, names=None):
    for n in names or rs.keys():
        ax.plot(u, np.interp(u, U, rs[n]), color=COL[n], ls=LS[n], label=n)


def pct(ax, x=True, y=True):
    if x:
        ax.xaxis.set_major_formatter(PercentFormatter(1, decimals=0))
        ax.set_xlabel("Utilization")
    if y:
        ax.yaxis.set_major_formatter(PercentFormatter(1, decimals=0))


def save(f, name, caption):
    from matplotlib.text import Text

    for artist in f.findobj(match=Text):
        artist.set_text(re.sub(r"(?<=[A-Za-z])-(?=[A-Za-z])", " ", artist.get_text()))
    for ext in ("pdf", "svg"):
        f.savefig(FIGDIR / f"{name}.{ext}")
    plt.close(f)
    figures.append((name, caption))


f, axes = figgrid(legend=False)
v = np.unique(np.r_[np.linspace(0, 1, 2500), U])
for ax, limits in zip(axes[0], [(0, 1), (0.975, 1)]):
    mask = (v >= limits[0]) & (v <= limits[1])
    ax.plot(v[mask], np.interp(v[mask], U, BASE), color=COL["Baseline"])
    nodes = U[(limits[0] <= U) & (limits[1] >= U)]
    ax.plot(nodes, np.interp(nodes, U, BASE), "o", ms=2.4, color=COL["Baseline"])
    ax.set(xlim=limits, ylabel="Borrow APR")
    pct(ax)
axes[0, 1].xaxis.set_major_formatter(PercentFormatter(1, decimals=1))
save(
    f,
    "01-usdt-baseline",
    "USDT borrow-rate configuration from the packaged illustrative configuration. (a) Full range, including the 0.5% floor and 80% kink. (b) Detail near the final knots. Markers show analytical breakpoints. The 99–99.5% interval accounts for 21.1875 percentage points of borrow APR. These are illustrative parameters, not a deployed configuration.",
)

f, axes = figgrid(rows=2, cols=3)
names = ["Baseline", "Floor", "Raise only", "Mixed"]
for col, policy in enumerate(sets):
    rs = sets[policy]
    for row, limits in enumerate([(0, 1), (0.8, 1)]):
        ax = axes[row, col]
        local = np.linspace(*limits, 1800)
        plot(ax, local, rs, names)
        ax.set(xlim=limits, ylabel="Borrow APR" if col == 0 else "")
        pct(ax)
        ax.set_xlabel("Utilization (full range)" if row == 0 else "Utilization (80–100% detail)")
        if row == 0:
            ax.set_title(LABEL[policy], fontsize=7, pad=12)
        if policy == "both":
            ax.text(0.04, 0.9, "Floor = raise = mixed", transform=ax.transAxes, fontsize=6.5)
save(
    f,
    "02-floor-and-repairs",
    "Baseline, minimum-rate compliant floor, least pointwise raise-only repair, and mixed repair under three guarantees. All preserve the analytical knot positions and 90% top APR. The floor is a lower bound conditional on these choices; it is not a recommended pricing curve. The mixed repair minimizes a trapezoid-weighted sum of squared changes to knot APRs. Top row: full range. Bottom row: high-utilization detail. Fixed-share and combined guarantees use a 5% share target. Under both constraints the floor lies everywhere above baseline, so all three repairs coincide; the overlapping lines are not three independent outcomes.",
)

f, axes = figgrid(names=["Baseline", "Raise only", "Lower only"])
rs = sets["both"]
local = np.linspace(0, 1, 2400)
for n in ["Raise only", "Lower only"]:
    axes[0, 0].plot(
        local,
        100 * (np.interp(local, U, rs[n]) - np.interp(local, U, BASE)),
        color=COL[n],
        ls=LS[n],
    )
    axes[0, 1].plot(local, np.interp(local, U, rs[n]), color=COL[n], ls=LS[n])
axes[0, 0].axhline(0, color="black", lw=0.5)
pct(axes[0, 0], y=False)
axes[0, 0].set_ylabel("APR change (percentage points)")
axes[0, 1].plot(local, np.interp(local, U, BASE), color=COL["Baseline"])
pct(axes[0, 1])
axes[0, 1].set_ylabel("Borrow APR")
save(
    f,
    "03-direction-of-repair",
    "Both constraints, at a 5% fixed-share target. (a) Changes relative to baseline. (b) Resulting rate curves. Raise-only retains the 90% top APR and equals the floor and mixed repair in this case. Lower-only is the greatest compliant curve nowhere above baseline, preserving its 0.5% base; it must abandon the 90% top APR. Keeping both that base and top is infeasible for these knots and constraints. All are continuous piecewise-linear illustrations, not integer parameter updates.",
)

f, axes = figgrid(
    names=["Baseline", "Mixed"], legend_labels=["Baseline", "Compliant (floor = raise = mixed)"]
)
local = np.unique(np.r_[np.linspace(0.78, 1, 3500), U[U >= 0.78]])
for n in ["Baseline", "Mixed"]:
    rate, slope = curve(rs[n], local)
    axes[0, 0].plot(local, 1 / (1 + local * slope / rate), color=COL[n], ls=LS[n])
x = np.linspace(0, 200000, 2500)
for n in ["Baseline", "Mixed"]:
    axes[0, 1].plot(x / 1000, supplier(rs[n], x)[1], color=COL[n], ls=LS[n])
axes[0, 0].set(xlim=(0.78, 1), ylim=(0, 0.3), ylabel="Protected supplier share")
pct(axes[0, 0])
axes[0, 0].axhline(0.05, color="gray", ls="--", lw=0.5)
axes[0, 1].set(xlabel="Deposit (USDT thousands)", ylabel="Income change per USDT (per year)")
axes[0, 1].axhline(0, color="gray", lw=0.5)
save(
    f,
    "04-protection-and-marginal-income",
    "Both constraints. (a) Actual local protected share, 1/(1+η), with the 5% target marked. (b) Marginal whole-position supplier income for a fresh depositor entering a pool with 1m USDT supply and 990k USDT borrowing. Borrowing remains fixed. Income includes the assumed 5% carveout. The baseline can have negative marginal income; all three repairs satisfy the fresh-depositor condition. At knots the plotted value uses the derivative from lower utilization, the direction entered by a deposit.",
)


def history(steps=3650, kind="market"):
    t = np.arange(steps + 1) * 365 / steps
    if kind == "market":
        principal = np.full_like(t, 10000.0)
        supply = np.full_like(t, 1e6)
        util = np.interp(t, [0, 90, 180, 270, 365], [0.8, 0.95, 0.995, 0.85, 0.8])
    else:
        extra = np.minimum(np.floor((t + 1e-9) / 60), 5) * 20000
        principal = 10000 + extra
        supply = 1e6 + extra
        util = 990000 / supply
    return t, principal, supply, util


def earnings(r, steps=3650, kind="market"):
    t, p, s, u = history(steps, kind)
    annual = LENDER * p * u * np.interp(u, U, r)
    paid = np.r_[0, np.cumsum(annual[:-1] * np.diff(t) / 365)]
    borrower_annual = s * u * np.interp(u, U, r)
    borrower_paid = np.r_[0, np.cumsum(borrower_annual[:-1] * np.diff(t) / 365)]
    return paid, borrower_paid


f, axes = figgrid(
    rows=2,
    cols=2,
    names=["Baseline", "Mixed"],
    legend_labels=["Baseline", "Compliant (floor = raise = mixed)"],
)
summary = {}
for row, kind in enumerate(["market", "topups"]):
    t, p, s, u = history(kind=kind)
    base_earned = earnings(BASE, kind=kind)[0]
    data = {"day": t, "principal_usdt": p, "supply_usdt": s, "utilization": u}
    summary[kind] = {}
    for n in names:
        paid, borrower = earnings(rs[n], kind=kind)
        fine, _ = earnings(rs[n], steps=7300, kind=kind)
        assert abs(paid[-1] - fine[-1]) < 5
        if n in ["Baseline", "Mixed"]:
            axes[row, 0].plot(t, paid, color=COL[n], ls=LS[n])
            axes[row, 1].plot(t, paid - base_earned, color=COL[n], ls=LS[n])
        data[n + "_earned_usdt"] = paid
        summary[kind][n] = {
            "supplier_interest": float(paid[-1]),
            "difference": float(paid[-1] - base_earned[-1]),
            "pool_borrower_interest": float(borrower[-1]),
        }
    for col in range(2):
        axes[row, col].set(xlabel="Day", xlim=(0, 365))
    axes[row, 0].set_ylabel("Accumulated interest (USDT)")
    axes[row, 1].set_ylabel("Difference from baseline (USDT)")
    axes[row, 1].axhline(0, color="gray", lw=0.5)
    write_csv("05-" + kind, data)
save(
    f,
    "05-lifecycle-comparison",
    "Both constraints; identical histories under all pricing choices. (a,b) A 10k USDT depositor holds for one year while utilization moves through 80%, 95%, 99.5%, 85%, 80% on days 0, 90, 180, 270, 365. Pool supply is 1m USDT. (c,d) A 10k depositor adds 20k on days 60, 120, 180, 240, 300 into an initial 1m pool with fixed 990k borrowing. Left: accumulated supplier interest. Right: difference from baseline. Interest is paid out rather than compounded; 5% carveout assumed. These histories do not model demand response. Numerical integration uses 0.1-day steps, checked at 0.05-day steps.",
)

f, axes = figgrid(names=["Floor", "Raise only", "Mixed"])
targets = np.linspace(0.015, 0.10, 25)
series = {n: [] for n in ["Floor", "Raise only", "Mixed"]}
borrow_series = {n: [] for n in series}
base_paid, base_borrow = earnings(BASE)
for alpha in targets:
    trial = repairs("both", float(alpha))
    for n in series:
        paid, borrower = earnings(trial[n])
        series[n].append(paid[-1] - base_paid[-1])
        borrow_series[n].append(borrower[-1] - base_borrow[-1])
for n in series:
    axes[0, 0].plot(targets, series[n], color=COL[n], ls=LS[n])
    axes[0, 1].plot(targets, borrow_series[n], color=COL[n], ls=LS[n])
for ax in axes[0]:
    ax.xaxis.set_major_formatter(PercentFormatter(1, decimals=0))
    ax.set_xlabel("Fixed-share target")
    ax.axhline(0, color="gray", lw=0.5)
axes[0, 0].set_ylabel("Supplier interest change (USDT)")
axes[0, 1].set_ylabel("Pool borrower interest change (USDT)")
save(
    f,
    "06-protection-cost",
    "Both constraints as the fixed-share target varies. Each point recalculates the repair, keeping knot positions and 90% maximum APR. Changes use the deposit-once history in Figure 5(a,b). Left: annual interest difference for a 10k supplier. Right: total interest difference paid by all borrowers in the 1m-supply pool. Under this fixed 1% ownership and 5% carveout, supplier change is exactly 0.0095 times pool borrower change: protection does not create interest revenue. The mixed objective minimizes knot-rate changes, not lifecycle cost; its outcome depends on the stated market history.",
)

# Fresh-only permits distinct floors and repairs; expose the pricing choice directly.
f, axes = figgrid()
t, principal, supply, util = history()
base_paid, _ = earnings(BASE)
summary["fresh_market"] = {}
fresh_data = {"day": t, "principal_usdt": principal, "utilization": util}
for n in names:
    paid, borrower = earnings(sets["fresh"][n])
    axes[0, 0].plot(t, paid, color=COL[n], ls=LS[n])
    axes[0, 1].plot(t, paid - base_paid, color=COL[n], ls=LS[n])
    fresh_data[n + "_earned_usdt"] = paid
    summary["fresh_market"][n] = {
        "supplier_interest": float(paid[-1]),
        "difference": float(paid[-1] - base_paid[-1]),
        "pool_borrower_interest": float(borrower[-1]),
    }
for ax in axes[0]:
    ax.set(xlabel="Day", xlim=(0, 365))
axes[0, 0].set_ylabel("Accumulated interest (USDT)")
axes[0, 1].set_ylabel("Difference from baseline (USDT)")
axes[0, 1].axhline(0, color="gray", lw=0.5)
write_csv("07-fresh-lifecycle", fresh_data)
save(
    f,
    "07-fresh-pricing-choice",
    "Fresh-depositor guarantee only, using the same deposit-once history and fee assumptions as Figure 5(a,b). (a) Accumulated interest. (b) Difference from baseline. All three repairs are compliant and preserve the 90% maximum, yet they need not produce the same income outcome. The floor lowers intermediate rates; raise-only preserves or increases every baseline rate. This comparison separates a mathematical guarantee from the policy choice of where to set compliant rates.",
)

for policy, rs in sets.items():
    write_csv("knots-" + policy, {"utilization": U, **rs})
    cap = caps(policy)
    write_csv(
        "segments-" + policy,
        {
            "u_left": U[:-1],
            "u_right": U[1:],
            "baseline_ratio": BASE[1:] / BASE[:-1],
            "allowed_ratio": cap,
            "baseline_valid": (BASE[1:] <= cap * BASE[:-1] + 1e-10),
        },
    )
write_csv(
    "06-target-sweep",
    {
        "fixed_share": targets,
        **{n + "_supplier_difference": np.array(series[n]) for n in series},
        **{n + "_borrower_difference": np.array(borrow_series[n]) for n in series},
    },
)
audit = {
    "configuration": params,
    "source_sha256": {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in [param_path, ROOT / "src/supplier_monotonicity/curve.py"]
    },
    "integer_rational_max_apr_error": float(err),
    "checks": checks,
    "lifecycle": summary,
    "fee_assumption": {"carveout": FEE, "additional_fees": 0},
    "feasibility": {
        policy: {
            "minimum_base_with_fixed_top": float(rs["Floor"][0]),
            "largest_top_without_raising_baseline": float(rs["Lower only"][-1]),
            "fixed_base_and_top_feasible": bool(rs["Floor"][0] <= BASE[0] + 1e-10),
            "no_increase_fixed_top_feasible": bool(np.all(rs["Floor"] <= BASE + 1e-10)),
        }
        for policy, rs in sets.items()
    },
}
(OUT / "provenance.json").write_text(json.dumps(audit, indent=2))
print(
    json.dumps(
        {"feasibility": audit["feasibility"], "lifecycle": summary, "checks": checks}, indent=2
    )
)
print(f"Wrote {len(figures)} figures to {FIGDIR}")
