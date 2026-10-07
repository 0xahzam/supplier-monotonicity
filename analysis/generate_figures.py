"""Generate all figures and audit the analytic multi-kink extension.

Run with the supplier-monotonicity Python environment. Inputs are recorded in analysis/.
"""

import json
import re
import runpy
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import PercentFormatter

ROOT = Path(__file__).resolve().parent
g = runpy.run_path(str(ROOT / "generate_market.py"))
from supplier_monotonicity.envelope import SmoothBranch
from supplier_monotonicity.proposal import Kink, rejoin

U = g["U"]
BASE = g["BASE"]
sets = g["sets"]
figgrid = g["figgrid"]
pct = g["pct"]
COL = g["COL"]
LS = g["LS"]
FIG = ROOT.parent / "figures"
FIG.mkdir(exist_ok=True)
audit = {}


def save(f, name):
    from matplotlib.text import Text

    for artist in f.findobj(match=Text):
        artist.set_text(re.sub(r"(?<=[A-Za-z])-(?=[A-Za-z])", " ", artist.get_text()))
    f.savefig(FIG / f"{name}.pdf")
    f.savefig(FIG / f"{name}.svg")
    plt.close(f)


def legend(f, names, colors=None, styles=None):
    from matplotlib.lines import Line2D

    colors = colors or [COL["Baseline"], COL["Raise only"], COL["Mixed"]]
    styles = styles or ["-", "--", ":"]
    f.legend(
        [
            Line2D([], [], color=c, ls=s, lw=1.1)
            for c, s in zip(colors[: len(names)], styles[: len(names)])
        ],
        names,
        loc="upper center",
        bbox_to_anchor=(0.54, 0.99),
        ncol=len(names),
        handlelength=2.4,
    )


def frame(rows=1, cols=2, names=None, colors=None):
    f, ax = figgrid(rows, cols, legend=False)
    if names:
        f.subplots_adjust(top=0.80 if rows == 1 else 0.87)
        legend(f, names, colors=colors)
    return f, ax


C = Kink(0.8, 0.05, 1.0)
K = 19.0
UC = rejoin(C, K)


def single(u, new=False):
    u = np.asarray(u)
    r = np.where(u <= 0.8, 0.05 * u / 0.8, 0.05 + C.slope * (u - 0.8))
    s = np.where(u <= 0.8, 0.05 / 0.8, C.slope)
    if new:
        active = (u > 0.8) & (u <= UC)
        p = 0.05 * (u / 0.8) ** K
        r = np.where(active, p, r)
        s = np.where(active, K * 0.05 / 0.8 * (u / 0.8) ** (K - 1), s)
    return r, s


def income(rate, x, b0, S0, B, fee=0.0):
    u = B / (S0 + x)
    r, s = rate(u)
    b = b0 + x
    alpha = b / (S0 + x)
    return (1 - fee) * b * u * r, (1 - fee) * u * (r - alpha * (r + u * s))


# Original failure mode, with the same inputs as the prose.
f, ax = frame()
v = np.linspace(0, 1, 1200)
ax[0, 0].plot(v, single(v)[0], color="black")
pct(ax[0, 0])
ax[0, 0].set_ylabel("Borrow APR")
x = np.linspace(-6e5, 1.5e6, 2800)
inc, mar = income(single, x, 1e6, 1e7, 8.3e6)
# Income-maximizing withdrawal: on the steep branch income is -15/4 + c1/S - c2/S^2 times B
# in supply S (USD millions), maximized at S = 2 c2 / c1, where alpha(1 + eta) = 1.
c1, c2 = 19 / 4 * 8.3 + 15 / 4 * 9, 9 * 19 / 4 * 8.3
best = (10 - 2 * c2 / c1) * 1e6
best_income = income(single, np.array([-best]), 1e6, 1e7, 8.3e6)[0][0]
ax[0, 1].plot(x / 1000, inc / 1000, color="black")
ax[0, 1].axvline(375, color="gray", ls="--", lw=0.6)
ax[0, 1].axvline(0, color="gray", lw=0.4)
ax[0, 1].plot(-best / 1000, best_income / 1000, "o", color="black", ms=3.5)
ax[0, 1].set(xlabel="Change in balance (USD thousands)", ylabel="Annual income (USD thousands)")
audit["failure"] = {
    "before": float(income(single, np.array([0.0]), 1e6, 1e7, 8.3e6)[0][0]),
    "at_kink": float(income(single, np.array([375000]), 1e6, 1e7, 8.3e6)[0][0]),
    "best_withdrawal": float(best),
    "best_withdrawal_income": float(best_income),
}
save(f, "T01-failure")

f, ax = frame(names=["Fresh depositor", "Fixed share", "Both"])
v = np.linspace(0.001, 0.999, 2000)
for vals, a in [
    ([1 - v, np.full_like(v, 0.05), np.maximum(1 - v, 0.05)], ax[0, 0]),
    ([v / (1 - v), np.full_like(v, 19), np.minimum(v / (1 - v), 19)], ax[0, 1]),
]:
    for y, c, s in zip(vals, [COL["Baseline"], COL["Raise only"], COL["Mixed"]], ["-", "--", ":"]):
        a.plot(v, y, color=c, ls=s)
    pct(a, y=False)
ax[0, 0].set_ylabel("Protection profile")
ax[0, 0].yaxis.set_major_formatter(PercentFormatter(1))
ax[0, 1].set(ylabel="Elasticity envelope", ylim=(0, 40))
save(f, "T02-envelopes")

f, ax = frame(names=["Fresh depositor", "Fixed share", "Both"])
v = np.linspace(0.8, 0.999, 1600)
fresh = 0.01 / (1 - v)
fixed = 0.05 * (v / 0.8) ** 19
both = np.where(v <= 0.95, fresh, 0.2 * (v / 0.95) ** 19)
for y, c, s in zip(
    [fresh, fixed, both], [COL["Baseline"], COL["Raise only"], COL["Mixed"]], ["-", "--", ":"]
):
    ax[0, 0].plot(v, y, color=c, ls=s)
pct(ax[0, 0])
ax[0, 0].set(ylabel="Boundary borrow APR", ylim=(0, 1.5))
ax[0, 0].axhline(1, color="gray", ls="--", lw=0.6)
v = np.linspace(0.5, 0.95, 300)
ax[0, 1].plot(v, 1 / (1 + np.log(20) / np.log(1 / v)), color=COL["Raise only"], ls="--")
pct(ax[0, 1])
ax[0, 1].set(xlabel="Kink utilization", ylabel="Endpoint share bound")
save(f, "T03-boundaries-endpoints")

TU = np.array([0, 0.8, 0.9, 0.95, 0.98, 0.995, 0.9999, 1.0])
TR = np.array([0.05, 0.09, 0.135, 0.2, 0.32, 0.56, 1.1, 1.1])


def table(u):
    u = np.asarray(u)
    i = np.clip(np.searchsorted(TU, u, side="left") - 1, 0, len(TU) - 2)
    return np.interp(u, TU, TR), np.diff(TR)[i] / np.diff(TU)[i]


def boundary(u):
    u = np.asarray(u)
    r = np.minimum(0.05 / (1 - u), 1.0)
    s = np.where(u < 0.95, 0.05 / (1 - u) ** 2, 0.0)
    return r, s


f, ax = frame()
v = np.linspace(0, 1, 1800)
for a, lim in zip(ax[0], [(0, 1), (0.94, 1)]):
    a.plot(v, table(v)[0], color="black")
    a.plot(TU, TR, "o", ms=2, color="black")
    pct(a)
    a.set(xlim=lim, ylabel="Borrow APR")
save(f, "T04-piecewise-example")
f, ax = frame(names=["Standard kink", "Table 1 curve", "Fresh boundary"])
x = np.linspace(0, 9.99e6 / 0.85 - 1e7, 3000)
for fn, c, s in zip(
    [single, table, boundary], [COL["Baseline"], COL["Raise only"], COL["Mixed"]], ["-", "--", ":"]
):
    inc, mar = income(fn, x, 0, 1e7, 9.99e6)
    ax[0, 0].plot(x / 1e6, inc / 1000, color=c, ls=s)
    ax[0, 1].plot(x / 1e6, mar, color=c, ls=s)
for a in ax[0]:
    a.set_xlabel("Deposit (USD millions)")
ax[0, 0].set_ylabel("Annual income (USD thousands)")
ax[0, 1].set_ylabel("Income change per USD (per year)")
ax[0, 1].axhline(0, color="gray", lw=0.6)
save(f, "T05-fresh-income")

f, ax = frame(names=["Standard kink", "Power repair"])
v = np.linspace(0.001, 1, 2000)
for new, c, s in zip([False, True], [COL["Baseline"], COL["Raise only"]], ["-", "--"]):
    r, _ = single(v, new)
    ax[0, 0].plot(v, r, color=c, ls=s)
    ax[0, 1].plot(v, v * r, color=c, ls=s)
for a in ax[0]:
    pct(a)
ax[0, 0].set_ylabel("Borrow APR")
ax[0, 1].set_ylabel("Supply APR")
save(f, "T06-single-rates")
f, ax = frame(names=["Standard kink", "Power repair"])
x = np.linspace(0, (0.05 * 1e7 - 1e5) / 0.95, 2000)
for new, c, s in zip([False, True], [COL["Baseline"], COL["Raise only"]], ["-", "--"]):
    inc, mar = income(lambda u: single(u, new), x, 1e5, 1e7, 8.5e6)
    ax[0, 0].plot(x / 1000, inc / 1000, color=c, ls=s)
    ax[0, 1].plot(x / 1000, mar, color=c, ls=s)
for a in ax[0]:
    a.set_xlabel("Additional deposit (USD thousands)")
ax[0, 0].set_ylabel("Annual income (USD thousands)")
ax[0, 1].set_ylabel("Income change per USD (per year)")
ax[0, 1].axhline(0, color="gray", lw=0.6)
audit["single_path"] = {
    str(new): [
        float(v) for v in income(lambda u: single(u, new), np.array([0, x[-1]]), 1e5, 1e7, 8.5e6)[0]
    ]
    for new in [False, True]
}
save(f, "T07-single-income")


class AnalyticRepair:
    """Exact running-envelope majorant/minorant of a piecewise linear baseline.

    F'=E F/U. Rminus=F min_{v<=U}(R0/F); Rplus=F max_{v>=U}(R0/F).
    All interior extrema of R0/F are included, not only sampled knots.
    """

    def __init__(self, policy="fixed", alpha=0.05, direction="lower"):
        self.policy = policy
        self.k = (1 - alpha) / alpha
        self.t = 1 - alpha
        self.direction = direction
        candidates = list(U[U > 0])
        if policy == "both":
            candidates.append(self.t)
        for lo, hi, rl, rh in zip(U[:-1], U[1:], BASE[:-1], BASE[1:]):
            m = (rh - rl) / (hi - lo)
            b = rl - m * lo
            if m == 0:
                continue
            if self.k > 1:
                z = -self.k * b / ((self.k - 1) * m)
                if lo < z < hi and (policy == "fixed" or z >= self.t):
                    candidates.append(z)
            if policy == "both":
                z = (m - b) / (2 * m)
                if lo < z < hi and z <= self.t:
                    candidates.append(z)
        if policy == "both":
            candidates.append(0.0)
        self.candidates = np.unique(candidates)
        self.q = np.interp(self.candidates, U, BASE) / self.F(self.candidates)

    def F(self, u):
        u = np.asarray(u)
        if self.policy == "fixed":
            return u**self.k
        return np.where(
            u <= self.t,
            1 / (1 - np.minimum(u, self.t)),
            (1 / (1 - self.t)) * (u / self.t) ** self.k,
        )

    def __call__(self, u):
        u = np.asarray(u, dtype=float)
        safe = np.maximum(u, 1e-12)
        original, slope = g["curve"](BASE, safe)
        f = self.F(safe)
        quotient = original / f
        if self.direction == "lower":
            q = np.min(
                np.where(self.candidates[None, :] <= safe[..., None], self.q, np.inf), axis=-1
            )
            best = np.minimum(quotient, q)
        else:
            q = np.max(
                np.where(self.candidates[None, :] >= safe[..., None], self.q, -np.inf), axis=-1
            )
            best = np.maximum(quotient, q)
        r = f * best
        active = abs(r - original) > 1e-10
        e = (
            np.full_like(safe, self.k)
            if self.policy == "fixed"
            else np.minimum(self.k, safe / (1 - np.minimum(safe, 1 - 1e-15)))
        )
        derivative = np.where(active, e * r / safe, np.minimum(slope, e * r / safe))
        if self.policy == "fixed":
            r = np.where(u == 0, BASE[0], r)
            derivative = np.where(u == 0, 0, derivative)
        return r, derivative


minus = AnalyticRepair()
plus = AnalyticRepair(direction="raise")
combined = AnalyticRepair("both", direction="raise")
v = np.unique(np.r_[np.linspace(0.000001, 1, 30000), U[1:] - 1e-9, U[1:-1] + 1e-9])
for obj in [minus, plus, combined]:
    r, s = obj(v)
    base, _ = g["curve"](BASE, v)
    assert np.max(v * s / r) <= 19 + 1e-7
    if obj.policy == "both":
        assert np.max((1 - v) * s - r) < 1e-8
    if obj.direction == "lower":
        assert np.max(r - base) < 1e-8
    else:
        assert np.min(r - base) > -1e-8
    assert np.min(np.diff(r)) >= -1e-8
    # Independent dense running extrema verify candidate-extrema evaluation.
    q = base / obj.F(v)
    dense = obj.F(v) * (
        np.minimum.accumulate(q)
        if obj.direction == "lower"
        else np.maximum.accumulate(q[::-1])[::-1]
    )
    assert np.max(abs(dense - r)) < 1e-7
    # Independent centered derivatives, excluding the small neighbourhoods of joins.
    interior = np.linspace(0.0001, 0.9999, 15000)
    rr, dd = obj(interior)
    h = 1e-7
    numeric = (obj(interior + h)[0] - obj(interior - h)[0]) / (2 * h)
    left = (rr - obj(interior - h)[0]) / h
    right = (obj(interior + h)[0] - rr) / h
    away = abs(left - right) < 1e-3
    assert np.allclose(numeric[away], dd[away], rtol=1e-5, atol=1e-6)
    x = np.linspace(0, 2e5, 5000)
    inc, mar = income(obj, x, 0, 1e6, 990000, 0.05)
    if obj.policy == "both":
        assert np.min(mar) > -1e-8
    valid = x / (1e6 + x) <= 0.05
    assert np.min(mar[valid]) > -1e-8
audit["analytic"] = {
    name: {
        "base": float(obj(np.array([0.0]))[0][0]),
        "kink": float(obj(np.array([0.8]))[0][0]),
        "top": float(obj(np.array([1.0]))[0][0]),
    }
    for name, obj in [("power_lower", minus), ("power_raise", plus), ("both_raise", combined)]
}
f, ax = frame(names=["Baseline", "Power minorant", "Power majorant"])
vv = np.linspace(0.78, 1, 8000)
for fn, c, s in zip(
    [lambda u: g["curve"](BASE, u), minus, plus],
    [COL["Baseline"], COL["Raise only"], COL["Mixed"]],
    ["-", "--", ":"],
):
    r, d = fn(vv)
    ax[0, 0].plot(vv, r, color=c, ls=s)
    ax[0, 1].plot(vv, vv * d / r, color=c, ls=s)
for a in ax[0]:
    pct(a, y=False)
ax[0, 0].yaxis.set_major_formatter(PercentFormatter(1))
ax[0, 0].set_ylabel("Borrow APR")
ax[0, 1].set_ylabel("Elasticity")
ax[0, 1].axhline(19, color="gray", ls="--", lw=0.6)
save(f, "M08-analytic-power")

f, ax = frame(names=["Baseline", "Both, fixed knots", "Both, analytic"])
for fn, c, s in zip(
    [lambda u: g["curve"](BASE, u), lambda u: g["curve"](sets["both"]["Raise only"], u), combined],
    [COL["Baseline"], COL["Raise only"], COL["Mixed"]],
    ["-", "--", ":"],
):
    v = np.linspace(0.00001, 1, 6000)
    r, d = fn(v)
    ax[0, 0].plot(v, r, color=c, ls=s)
    ax[0, 1].plot(v, 1 / (1 + v * d / r), color=c, ls=s)
for a in ax[0]:
    pct(a)
ax[0, 0].set_ylabel("Borrow APR")
ax[0, 1].set_ylabel("Protected supplier share")
save(f, "M09-analytic-combined")

# Sensitivity of the lower bound to an explicitly refined knot grid.
refinements = [1, 2, 4, 8, 16, 32, 64]
base_fresh = []
base_both = []
for n in refinements:
    nodes = np.unique(np.concatenate([np.linspace(lo, hi, n + 1) for lo, hi in zip(U[:-1], U[1:])]))
    fresh = 1 + np.diff(nodes) / (1 - nodes[:-1])
    fixed = np.array(
        [g["fixed_share_cap"](float(lo), float(hi), 19) for lo, hi in zip(nodes[:-1], nodes[1:])]
    )
    base_fresh.append(float(0.9 / np.prod(fresh)))
    base_both.append(float(0.9 / np.prod(np.minimum(fresh, fixed))))
f, ax = frame(names=["Fresh depositor", "Both"])
for vals, c, s in zip([base_fresh, base_both], [COL["Baseline"], COL["Raise only"]], ["-", "--"]):
    ax[0, 0].plot(refinements, vals, color=c, ls=s, marker="o", ms=2)
ax[0, 0].set_xscale("log", base=2)
ax[0, 0].set(xlabel="Subsegments per original segment", ylabel="Minimum base APR")
ax[0, 0].yaxis.set_major_formatter(PercentFormatter(1, decimals=1))
ax[0, 0].set_xticks(refinements, labels=[str(n) for n in refinements])
ax[0, 0].minorticks_off()
continuous = 0.9 * 0.95**19 / 20
ax[0, 0].axhline(continuous, color="gray", ls=":", lw=0.7)
alpha = np.linspace(0.01, 0.15, 150)
ax[0, 1].plot(
    alpha, 0.9 * (1 - alpha) ** ((1 - alpha) / alpha) * alpha, color=COL["Raise only"], ls="--"
)
ax[0, 1].set(xlabel="Fixed-share target", ylabel="Continuous combined base bound")
pct(ax[0, 1], x=False)
ax[0, 1].xaxis.set_major_formatter(PercentFormatter(1))
audit["knot_sensitivity"] = {
    "subsegments": refinements,
    "fresh_min_base": base_fresh,
    "both_min_base": base_both,
    "continuous_combined_min_base": continuous,
}
save(f, "M10-knot-sensitivity")

# Exposure mix, with no behavioural model: one year divided between U=.8 and U=.99.
f, ax = frame(
    names=["Floor", "Raise only", "Mixed"], colors=[COL["Floor"], COL["Raise only"], COL["Mixed"]]
)
w = np.linspace(0, 1, 201)
for name, c, s in zip(
    ["Floor", "Raise only", "Mixed"],
    [COL["Floor"], COL["Raise only"], COL["Mixed"]],
    ["-", "--", ":"],
):
    r = sets["fresh"][name]
    dif = (
        0.95
        * 10000
        * np.array([0.8, 0.99])
        * (np.interp([0.8, 0.99], U, r) - np.interp([0.8, 0.99], U, BASE))
    )
    ax[0, 0].plot(w, (1 - w) * dif[0] + w * dif[1], color=c, ls=s)
    # Right panel shows the distinct fixed-share analytic repair cost.
v = np.linspace(0.8, 0.999, 700)
for obj, c, s, label in [
    (minus, COL["Raise only"], "--", "Power minorant"),
    (plus, COL["Mixed"], ":", "Power majorant"),
]:
    rr, _ = obj(v)
    diff = 0.95 * 10000 * v * (rr - np.interp(v, U, BASE))
    ax[0, 1].plot(v, diff, color=c, ls=s, label=label)
ax[0, 0].set(
    xlabel="Fraction of year at 99% utilization", ylabel="Annual interest difference (USDT)"
)
ax[0, 0].xaxis.set_major_formatter(PercentFormatter(1))
ax[0, 1].set(xlabel="Constant utilization", ylabel="Annual interest difference (USDT)")
ax[0, 1].xaxis.set_major_formatter(PercentFormatter(1))
ax[0, 1].legend(loc="upper left", fontsize=6)
for a in ax[0]:
    a.axhline(0, color="gray", lw=0.6)
save(f, "M11-exposure-sensitivity")

# Supporting figures, all in the same type and physical dimensions.
f, ax = frame()
x = np.linspace(0, 1e7, 2500)
fn = lambda u: (np.maximum(single(u)[0], 0.01), np.where(single(u)[0] > 0.01, single(u)[1], 0.0))
inc, mar = income(fn, x, 1e7, 1e7, 9.5e6)
ax[0, 0].plot(x / 1e6, inc / 1e6, color="black")
ax[0, 1].plot(x / 1e6, mar, color="black")
for a in ax[0]:
    a.set_xlabel("Additional deposit (USD millions)")
ax[0, 0].set_ylabel("Annual income (USD millions)")
ax[0, 1].set_ylabel("Income change per USD (per year)")
save(f, "A01-full-supplier")

f, ax = frame(names=["Exact power law", "Linear chord"])
v = np.linspace(0.8, 0.9, 1200)
r = 0.05 * (v / 0.8) ** 19
m = (r[-1] - r[0]) / 0.1
chord = r[0] + m * (v - 0.8)
for vals, a in [([r, chord], ax[0, 0]), ([np.full_like(v, 19), v * m / chord], ax[0, 1])]:
    for y, c, s in zip(vals, [COL["Baseline"], COL["Raise only"]], ["-", "--"]):
        a.plot(v, y, color=c, ls=s)
    pct(a, y=False)
ax[0, 0].set_ylabel("Borrow APR")
ax[0, 0].yaxis.set_major_formatter(PercentFormatter(1))
ax[0, 1].set_ylabel("Elasticity")
save(f, "A02-discretization")

smooth0 = SmoothBranch(0.8, 0.05, 1, 0)
smooth = SmoothBranch(0.8, 0.05, 1, smooth0.max_width(19))
f, ax = frame(names=["Standard kink", "Power repair", "Smooth branch"])
v = np.linspace(0.78, 1, 2500)
for fn, c, s in zip(
    [
        single,
        lambda u: single(u, True),
        lambda u: (
            np.array([smooth.rate(z) for z in u]),
            np.array([smooth.eta(z) * smooth.rate(z) / z for z in u]),
        ),
    ],
    [COL["Baseline"], COL["Raise only"], COL["Mixed"]],
    ["-", "--", ":"],
):
    r, d = fn(v)
    ax[0, 0].plot(v, v * d / r, color=c, ls=s)
    ax[0, 1].plot(v, 1 / (1 + v * d / r), color=c, ls=s)
for a in ax[0]:
    pct(a, y=False)
ax[0, 0].set_ylabel("Elasticity")
ax[0, 1].set_ylabel("Protected supplier share")
ax[0, 1].yaxis.set_major_formatter(PercentFormatter(1))
save(f, "A03-smooth-protection")
f, ax = frame()
width = np.linspace(0, smooth0.log_span, 300)
peaks = np.array([SmoothBranch(0.8, 0.05, 1, float(w)).eta_max for w in width])
ax[0, 0].plot(width, peaks, color="black")
ax[0, 0].set(xlabel="Ramp width in log utilization", ylabel="Plateau elasticity")
ax[0, 1].plot(0.8 * np.exp(width), 1 / (1 + peaks), color="black")
pct(ax[0, 1])
ax[0, 1].set(xlabel="Utilization at end of ramp", ylabel="Protected supplier share")
save(f, "A04-smoothing-cost")
audit["checks"] = (
    "Analytic repairs: exact extrema construction, dense independent running-envelope comparison, elasticity bounds, direction of rate changes, finite protected deposit paths. Existing fixed-knot KKT and integer/rational checks also run."
)
(ROOT / "data/final-audit.json").write_text(json.dumps(audit, indent=2))
print(json.dumps(audit, indent=2))
