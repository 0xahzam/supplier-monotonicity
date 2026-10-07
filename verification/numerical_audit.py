#!/usr/bin/env python3
"""Independent exact-rational checks; no manuscript generator is executed.

Transcendental enclosures use rational series with explicit geometric tails.
These Python calculations are separate evidence, not Lean-certified numerics.
"""

import csv
import json
import math
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DATA = ROOT.parent / "analysis/data"


class Interval:
    def __init__(self, lo, hi=None):
        self.lo, self.hi = Q(lo), Q(lo if hi is None else hi)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = box(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -box(other)

    def __rsub__(self, other):
        return box(other) + -self

    def __mul__(self, other):
        other = box(other)
        vals = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = box(other)
        assert not other.lo <= 0 <= other.hi
        return self * Interval(1 / other.hi, 1 / other.lo)

    def __rtruediv__(self, other):
        return box(other) / self


def box(v):
    return v if isinstance(v, Interval) else Interval(v)


def ln_unit(q, n=48):
    assert 1 <= q <= 2
    z = (q - 1) / (q + 1)
    s = 2 * sum((z ** (2 * k + 1) / Q(2 * k + 1) for k in range(n)), Q(0))
    tail = 2 * z ** (2 * n + 1) / (Q(2 * n + 1) * (1 - z * z))
    return Interval(s, s + tail)


def ln(q):
    q = Q(q)
    assert q > 0
    k = 0
    while q >= 2:
        q /= 2
        k += 1
    while q < 1:
        q *= 2
        k -= 1
    return ln_unit(q) + k * ln_unit(Q(2))


def exp_point(x, n=48):
    assert 0 <= x <= 1
    s = sum((x**k / Q(math.factorial(k)) for k in range(n + 1)), Q(0))
    tail = x ** (n + 1) / Q(math.factorial(n + 1)) / (1 - x / Q(n + 2))
    return Interval(s, s + tail)


def exp(v):
    v = box(v)
    # Outward rational rounding keeps series denominator sizes manageable.
    den = 10**25
    lo = Q(v.lo.numerator * den // v.lo.denominator, den)
    hi = Q(-((-v.hi.numerator * den) // v.hi.denominator), den)
    return Interval(exp_point(lo).lo, exp_point(hi).hi)


results = []


def record(name, value, printed=None, tolerance=None, note=""):
    v = box(value)
    row = {
        "name": name,
        "computed_lower": float(v.lo),
        "computed_upper": float(v.hi),
        "enclosure_width_upper": float(v.hi - v.lo),
        "method": "exact rational" if v.lo == v.hi else "rational series enclosure",
        "note": note,
    }
    if v.lo == v.hi:
        row["exact"] = str(v.lo)
    if printed is not None:
        p, t = Q(str(printed)), Q(str(tolerance))
        row.update(
            printed=printed,
            tolerance=tolerance,
            status="PASS" if p - t <= v.lo and v.hi <= p + t else "OUTSIDE_TOLERANCE",
        )
    else:
        row["status"] = "COMPUTED"
    results.append(row)


U = list(map(Q, ["0", "0", ".8", ".85", ".9", ".95", ".99", ".995", "1"]))
U[1] = Q(8, 105)
BASE = list(
    map(
        Q,
        [
            ".005",
            ".005",
            ".0525",
            ".094875",
            ".179625",
            ".30675",
            ".47625",
            ".688125",
            ".9",
        ],
    )
)


def caps(grid, policy):
    out = []
    for a, b in zip(grid, grid[1:]):
        options = []
        if policy in ("fresh", "both"):
            options.append(1 + (b - a) / (1 - a))
        if policy in ("fixed", "both"):
            if a:
                options.append(1 + 19 * (b - a) / a)
            if b - 19 * (b - a) > 0:
                options.append(b / (b - 19 * (b - a)))
        out.append(min(options) if options else None)
    return out


def repairs(policy, grid=U, base=BASE):
    cap = caps(grid, policy)
    floor = [Q(0)] * len(grid)
    up = base.copy()
    down = base.copy()
    floor[-1] = base[-1]
    for i in reversed(range(len(cap))):
        floor[i] = floor[i + 1] / cap[i] if cap[i] else Q(0)
        up[i] = max(base[i], up[i + 1] / cap[i]) if cap[i] else base[i]
    for i in range(len(cap)):
        down[i + 1] = min(base[i + 1], down[i] * cap[i]) if cap[i] else base[i + 1]
    return {"Baseline": base, "Floor": floor, "Raise only": up, "Lower only": down}


def rate(u, rr, grid=U):
    for a, b, r, s in zip(grid, grid[1:], rr, rr[1:]):
        if a <= u <= b:
            return r + (s - r) * (u - a) / (b - a)
    raise ValueError(u)


def gauss(A, b):
    n = len(b)
    aug = [list(row) + [rhs] for row, rhs in zip(A, b)]
    for i in range(n):
        pivot = next(j for j in range(i, n) if aug[j][i])
        aug[i], aug[pivot] = aug[pivot], aug[i]
        d = aug[i][i]
        aug[i] = [v / d for v in aug[i]]
        for j in range(n):
            if j != i:
                c = aug[j][i]
                aug[j] = [x - c * y for x, y in zip(aug[j], aug[i])]
    return [row[-1] for row in aug]


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), Q(0))


def exact_projection(policy):
    # CSV values select candidate active constraints only. The solution and all
    # KKT conditions are then reconstructed and checked with exact rationals.
    rows = list(csv.DictReader((DATA / f"knots-{policy}.csv").open()))
    guess = [float(row["Mixed"]) for row in rows]
    n = len(U)
    A = []
    for i, c in enumerate(caps(U, policy)):
        row = [Q(0)] * n
        row[i] = 1
        row[i + 1] = -1
        A.append(row)
        if c:
            row = [Q(0)] * n
            row[i] = -c
            row[i + 1] = 1
            A.append(row)
    active = [row for row in A if abs(sum(float(a) * b for a, b in zip(row, guess))) < 1e-8]
    top = [Q(0)] * n
    top[-1] = 1
    C = active + [top]
    rhs = [Q(0)] * len(active) + [BASE[-1]]
    W = (
        [(U[1] - U[0]) / 2]
        + [(U[i + 1] - U[i - 1]) / 2 for i in range(1, n - 1)]
        + [(U[-1] - U[-2]) / 2]
    )
    gram = [[sum((a * b / w for a, b, w in zip(row, col, W)), Q(0)) for col in C] for row in C]
    lam = gauss(gram, [dot(row, BASE) - b for row, b in zip(C, rhs)])
    r = [BASE[i] - sum((lam[j] * C[j][i] for j in range(len(C))), Q(0)) / W[i] for i in range(n)]
    assert all(dot(row, r) <= 0 for row in A)
    assert r[-1] == BASE[-1]
    assert all(v >= 0 for v in lam[:-1])
    assert all(lam[j] * (dot(row, r) - rhs[j]) == 0 for j, row in enumerate(C))
    assert all(
        W[i] * (r[i] - BASE[i]) + sum((lam[j] * C[j][i] for j in range(len(C))), Q(0)) == 0
        for i in range(n)
    )
    record(
        f"{policy}: exact KKT certificate",
        0,
        0,
        0,
        "Strictly positive weights; primal/dual feasibility, stationarity and complementarity checked exactly. Convex-QP sufficiency interpreted mathematically, not formalized in Lean.",
    )
    return r


def year_interest(rr):
    days = [0, 90, 180, 270, 365]
    util = list(map(Q, [".8", ".95", ".995", ".85", ".8"]))
    ans = Q(0)
    for d0, d1, u0, u1 in zip(days, days[1:], util, util[1:]):
        lo, hi = sorted([u0, u1])
        splits = sorted(set([lo, hi] + [u for u in U if lo < u < hi]))
        integral = Q(0)
        for a, b in zip(splits, splits[1:]):
            ra, rb = rate(a, rr), rate(b, rr)
            m = (rb - ra) / (b - a)
            c = ra - m * a
            integral += m * (b**3 - a**3) / 3 + c * (b**2 - a**2) / 2
        ans += Q(d1 - d0, 365) * integral / (hi - lo)
    return Q(19, 20) * 10000 * ans


def topup_interest(rr):
    ans = Q(0)
    for n in range(6):
        u = Q(990000, 1000000 + 20000 * n)
        ans += Q(60 if n < 5 else 65, 365) * Q(19, 20) * (10000 + 20000 * n) * u * rate(u, rr)
    return ans


def main():
    # Core example and exact linear arithmetic.
    record(
        "Failure: initial annual income",
        Q(1000000) * Q(83, 100) * (Q(1, 20) + Q(19, 4) * Q(3, 100)),
        159800,
        50,
    )
    record("Failure: income at kink", Q(1375000) * Q(4, 5) * Q(1, 20), 55000, 0)
    record("Failure: deposit to kink", Q(8300000) / Q(4, 5) - 10000000, 375000, 0)
    record("Failure: balance increase percent", Q(375000, 1000000) * 100, 37.5, 0)
    record("Failure: income decline percent", (1 - Q(55000) / Q(159775)) * 100, 66, 1)
    # Best withdrawal. Above the kink, with supply S in USD millions, income is
    # B(S - 9)(19/4 B/S - 15/4)/S = B(-15/4 + c1/S - c2/S^2), maximized at S = 2 c2 / c1.
    wB = Q(83, 10)
    c1, c2 = Q(19, 4) * wB + Q(15, 4) * 9, 9 * Q(19, 4) * wB
    wS = 2 * c2 / c1
    wU = wB / wS
    rate_at = Q(19, 4) * wU - Q(15, 4)
    best = (wS - 9) * wU * rate_at * 1000000
    record("Withdrawal: amount", (10 - wS) * 1000000, 302000, 100)
    record("Withdrawal: income", best, 188300, 50)
    record("Withdrawal: income gain percent", (best / Q(159775) - 1) * 100, 18, 0.5)
    record("Withdrawal: share of balance percent", (10 - wS) * 100, 30, 0.5)
    record("Withdrawal: utilization percent", wU * 100, 85.6, 0.05)
    record(
        "Withdrawal: alpha(1+eta) at optimum", (wS - 9) / wS * (1 + wU * Q(19, 4) / rate_at), 1, 0
    )
    record("Single kink: elasticity at foot", Q(4, 5) * Q(19, 4) / Q(1, 20), 76, 0)
    record("Single kink: elasticity at full utilization", Q(19, 4), 4.75, 0)
    record("Envelope crossing utilization percent", Q(19, 20) * 100, 95, 0)
    for eta, alpha in [(9, 10), (19, 5), (99, 1)]:
        record(f"Safe share eta={eta} percent", 100 / Q(1 + eta), alpha, 0)
    A, L = ln(20), ln(Q(5, 4))
    ks = A / L
    record("Kstar", ks, 13.43, 0.005)
    record("Maximum protected share percent", 100 / (1 + ks), 6.93, 0.005)
    wmax = 2 * L * (19 - ks) / 18
    record("Maximum smoothing width", wmax, 0.1382, 0.00005)
    for w, printed_end, printed_eta, printed_share in [
        (Interval(0), 80, 13.43, 6.93),
        (Interval(".05"), 84.10, 14.99, 6.25),
        (Interval(".1"), 88.41, 17.01, 5.55),
        (wmax, 91.86, 19, 5),
        (L, 100, 25.85, 3.72),
    ]:
        M = (A - w / 2) / (L - w / 2)
        record(
            f"Smoothing table: endpoint for w~{float(w.lo):.5f}",
            80 * exp(w),
            printed_end,
            0.005,
        )
        record(f"Smoothing table: plateau for w~{float(w.lo):.5f}", M, printed_eta, 0.005)
        record(
            f"Smoothing table: share for w~{float(w.lo):.5f}",
            100 / (1 + M),
            printed_share,
            0.005,
        )

    # Nontrivial rejoin bracket, away from the trivial root at O.
    def eq(u):
        return Q(1, 20) * (u / Q(4, 5)) ** 19 - Q(1, 20) - Q(19, 4) * (u - Q(4, 5))

    lo, hi = Q("0.90915"), Q("0.90925")
    assert eq(lo) < 0 < eq(hi)
    for _ in range(80):
        mid = (lo + hi) / 2
        if eq(mid) < 0:
            lo = mid
        else:
            hi = mid
    record(
        "Rejoin utilization percent",
        Interval(lo * 100, hi * 100),
        90.92,
        0.005,
        "Exact sign bracket. Uniqueness is not certified by this numerical bracket.",
    )
    record("Chord elasticity from 80 to 90 percent", 8 * ((Q(9, 8)) ** 19 - 1), 67, 1)
    # Table A fresh curve.
    tu = list(map(Q, ["0", ".8", ".9", ".95", ".98", ".995", ".9999"]))
    tr = list(map(Q, [".05", ".09", ".135", ".2", ".32", ".56", "1.1"]))
    for i, (a, b, r, s) in enumerate(zip(tu, tu[1:], tr, tr[1:])):
        assert s / r <= 1 + (b - a) / (1 - a)
        record(
            f"Fresh table segment {i + 1}: ratio",
            s / r,
            [1.800, 1.500, 1.481, 1.600, 1.750, 1.964][i],
            0.0005,
        )
    endu = Q(85, 100)
    x = Q(9990000) / endu - 10000000
    record(
        "Fresh deposit: table final annual income",
        x * endu * rate(endu, tr, tu),
        168000,
        500,
    )
    record(
        "Fresh deposit: original final annual income",
        x * endu * (Q(1, 20) + Q(19, 4) * (endu - Q(4, 5))),
        428000,
        500,
    )
    record(
        "Fresh deposit: boundary final annual income",
        x * endu * Q(1, 20) / (1 - endu),
        497000,
        500,
    )
    # The marginal-zero fresh baseline root has an exact rational utilization.
    u0 = Q(999, 1000)
    m = Q(19, 4)
    intercept = Q(1, 20) - m * Q(4, 5)
    uz = (m * u0 - intercept) / (2 * m)
    record("Fresh original: turning deposit", Q(9990000) / uz - 10000000, 1170000, 5000)
    rs = {p: repairs(p) for p in ["fresh", "fixed", "both"]}
    for p in rs:
        rs[p]["Mixed"] = exact_projection(p)
    for p, choice, printed in [
        ("fresh", "Floor", 3.47),
        ("fresh", "Raise only", 6.39),
        ("both", "Floor", 8.68),
    ]:
        record(f"{p}: {choice} base APR percent", 100 * rs[p][choice][0], printed, 0.005)
    for p, printed in [("fresh", 12.04), ("both", 4.82)]:
        record(
            f"{p}: lower-only top percent",
            100 * rs[p]["Lower only"][-1],
            printed,
            0.005,
        )
    assert rs["both"]["Floor"] == rs["both"]["Raise only"] == rs["both"]["Mixed"]
    record(
        "Continuous combined minimum base percent",
        100 * Q(9, 10) * (Q(19, 20) ** 19) / 20,
        1.70,
        0.005,
    )
    record(
        "Analytic fixed minorant top percent",
        100 * Q(".47625") / Q(".99") ** 19,
        57.65,
        0.005,
    )
    # Analytic combined majorant at zero: maximize R0/F over each exact segment.
    candidates = set(U + [Q(19, 20)])
    for a, b, r, s in zip(U, U[1:], BASE, BASE[1:]):
        m = (s - r) / (b - a)
        c = r - m * a
        if not m:
            continue
        z = (m - c) / (2 * m)
        if a < z < b and z <= Q(19, 20):
            candidates.add(z)
        z = -19 * c / (18 * m)
        if a < z < b and z >= Q(19, 20):
            candidates.add(z)

    def boundary(u):
        return 1 / (1 - u) if u <= Q(19, 20) else 20 * (u / Q(19, 20)) ** 19

    record(
        "Analytic combined majorant base percent",
        100 * max(rate(u, BASE) / boundary(u) for u in candidates),
        1.85,
        0.005,
    )
    fine = []
    for a, b in zip(U, U[1:]):
        fine.extend(a + (b - a) * Q(i, 64) for i in range(64))
    fine.append(U[-1])
    fb = [rate(u, BASE) for u in fine]
    record(
        "64-subsegment combined floor base percent",
        100 * repairs("both", fine, fb)["Floor"][0],
        1.80,
        0.005,
    )
    for choice, printed in [
        ("Baseline", 1983),
        ("Floor", 1287),
        ("Raise only", 2231),
        ("Mixed", 1680),
    ]:
        record(
            f"Fresh history: {choice} yearly interest",
            year_interest(rs["fresh"][choice]),
            printed,
            0.5,
        )
    record(
        "Combined history: yearly interest",
        year_interest(rs["both"]["Floor"]),
        3165,
        0.5,
    )
    record("Topups baseline: yearly interest", topup_interest(BASE), 13453, 0.5)
    record(
        "Topups combined: yearly interest",
        topup_interest(rs["both"]["Floor"]),
        19667,
        0.5,
    )
    record("Borrower-to-supplier incremental transfer", Q(1, 100) * Q(19, 20), 0.0095, 0)
    output = {
        "scope": "Independent rational numerical audit; not Lean-certified. Table comparison tolerances represent last printed digit unless noted. Exact integrals replace time stepping. KKT candidates seeded from CSV, then certified exactly.",
        "checks": results,
        "out_of_tolerance": [r["name"] for r in results if r["status"] == "OUTSIDE_TOLERANCE"],
    }
    (ROOT / "evidence/numerical-audit.json").write_text(json.dumps(output, indent=2) + "\n")
    print(f"{len(results)} numerical checks; outside tolerance: {output['out_of_tolerance']}")


if __name__ == "__main__":
    main()
