"""Numeric checks for the mixed-repair optimisation, lifecycle histories and analytic repairs.

Covers the mixed-repair QP, the deposit-once and repeated-deposit histories, the
analytic combined majorant, knot refinement and the appendix deposit paths.
"""

import numpy as np
from mpmath import exp, findroot, log, mp, mpf
from scipy.optimize import minimize

mp.dps = 30

RES = []


def chk(cid, desc, got, printed, tol, note=""):
    ok = abs(mpf(got) - mpf(printed)) <= mpf(tol)
    RES.append((cid, ok, desc, f"computed {mp.nstr(mpf(got), 8)}  printed {printed}", note))


K = mpf(19)
u_ramp = mpf("0.005") * mpf("0.8") / mpf("0.0525")
knots = [
    mpf(0),
    u_ramp,
    mpf("0.8"),
    mpf("0.85"),
    mpf("0.9"),
    mpf("0.95"),
    mpf("0.99"),
    mpf("0.995"),
    mpf("1.0"),
]
rates = [
    mpf("0.005"),
    mpf("0.005"),
    mpf("0.0525"),
    mpf("0.094875"),
    mpf("0.179625"),
    mpf("0.30675"),
    mpf("0.47625"),
    mpf("0.688125"),
    mpf("0.90"),
]
INF = mpf("1e30")


def c_fresh(i):
    return 1 + (knots[i + 1] - knots[i]) / (1 - knots[i]) if knots[i] < 1 else INF


def c_fixed(i, Kv=K):
    du = knots[i + 1] - knots[i]
    left = 1 + Kv * du / knots[i] if knots[i] > 0 else INF
    den = knots[i + 1] - Kv * du
    return min(left, knots[i + 1] / den if den > 0 else INF)


caps_fresh = [c_fresh(i) for i in range(len(knots) - 1)]
caps_both = [min(c_fresh(i), c_fixed(i)) for i in range(len(knots) - 1)]


def floor_curve(c):
    l = [mpf(0)] * len(rates)
    l[-1] = rates[-1]
    for i in range(len(c) - 1, -1, -1):
        l[i] = l[i + 1] / c[i]
    return l


def raise_only(c):
    r = [mpf(0)] * len(rates)
    r[-1] = rates[-1]
    for i in range(len(c) - 1, -1, -1):
        r[i] = max(rates[i], r[i + 1] / c[i])
    return r


# ---------------- mixed repair: QP with trapezoidal utilization weights -------
def trapezoid_weights(u):
    n = len(u)
    w = [0.0] * n
    for i in range(n):
        lo = u[i] - u[i - 1] if i > 0 else 0.0
        hi = u[i + 1] - u[i] if i < n - 1 else 0.0
        w[i] = float(lo + hi) / 2.0
    return w


def mixed_repair(c):
    u = [float(x) for x in knots]
    r0 = [float(x) for x in rates]
    cc = [float(x) for x in c]
    w = trapezoid_weights(u)
    n = len(r0)

    def obj(r):
        return sum(w[i] * (r[i] - r0[i]) ** 2 for i in range(n))

    def jac(r):
        return np.array([2 * w[i] * (r[i] - r0[i]) for i in range(n)])

    cons = [{"type": "eq", "fun": (lambda r: r[n - 1] - r0[n - 1])}]
    for i in range(n - 1):
        cons.append({"type": "ineq", "fun": (lambda r, i=i: r[i + 1] - r[i])})  # nondecreasing
        if cc[i] < 1e20:
            cons.append(
                {"type": "ineq", "fun": (lambda r, i=i: cc[i] * r[i] - r[i + 1])}
            )  # ratio cap
    x0 = np.array(floor_curve(c), dtype=float)
    res = minimize(
        obj,
        x0,
        jac=jac,
        constraints=cons,
        method="SLSQP",
        bounds=[(1e-9, 5.0)] * n,
        options={"maxiter": 2000, "ftol": 1e-16},
    )
    assert res.success, res.message
    return [mpf(float(v)) for v in res.x], res


mixed_fresh, rf = mixed_repair(caps_fresh)


# KKT / feasibility audit of the returned point
def feasible(r, c, tol=1e-9):
    for i in range(len(r) - 1):
        if float(r[i + 1] - r[i]) < -tol:
            return False, f"decreasing at {i}"
        if c[i] < INF and float(c[i] * r[i] - r[i + 1]) < -tol:
            return False, f"cap violated at {i}"
    return True, "ok"


ok, msg = feasible(mixed_fresh, caps_fresh)
RES.append(
    (
        "QP-feas",
        ok,
        "mixed repair (fresh only) satisfies every segment constraint",
        msg,
        "",
    )
)


# ---------------- lifecycle histories ----------------
def curve_eval(rs, U):
    U = mpf(U)
    for i in range(len(knots) - 1):
        if knots[i + 1] >= U:
            a, b = knots[i], knots[i + 1]
            return rs[i] if b == a else rs[i] + (rs[i + 1] - rs[i]) * (U - a) / (b - a)
    return rs[-1]


days = [0, 90, 180, 270, 365]
Us = [mpf("0.80"), mpf("0.95"), mpf("0.995"), mpf("0.85"), mpf("0.80")]


def accrued_single(rs, principal=mpf("10000"), f=mpf("0.05"), n=400000):
    tot = mpf(0)
    for k in range(len(days) - 1):
        t0, t1 = days[k], days[k + 1]
        steps = int(n * (t1 - t0) / 365)
        for j in range(steps):
            frac = (mpf(j) + mpf("0.5")) / steps
            U = Us[k] + (Us[k + 1] - Us[k]) * frac
            tot += U * curve_eval(rs, U) * (mpf(t1 - t0) / 365) / steps
    return principal * (1 - f) * tot


chk(
    "A4d",
    "fresh-only MIXED repair, accrued interest (USDT)",
    accrued_single(mixed_fresh),
    "1680",
    "8",
)
chk(
    "A4e",
    "both guarantees, repairs coincide, accrued interest (USDT)",
    accrued_single(floor_curve(caps_both)),
    "3165",
    "8",
)
# the three "both" repairs must coincide
co = max(abs(float(a - b)) for a, b in zip(floor_curve(caps_both), raise_only(caps_both)))
RES.append(
    (
        "X-coincide",
        co < 1e-12,
        "under both guarantees the floor and raise-only repairs coincide",
        f"max |floor - raise| = {co:.2e}",
        "",
    )
)


# repeated-deposit history: 10k in 1M pool vs 990k borrowed, +20k on days 60..300
def accrued_repeated(rs, f=mpf("0.05")):
    B = mpf("990000")
    S = mpf("1000000")
    b = mpf("10000")
    marks = [0, 60, 120, 180, 240, 300, 365]
    tot = mpf(0)
    for k in range(len(marks) - 1):
        U = B / S
        tot += b * U * curve_eval(rs, U) * mpf(marks[k + 1] - marks[k]) / 365
        if marks[k + 1] < 365:
            S += mpf("20000")
            b += mpf("20000")
    return (1 - f) * tot


chk(
    "A4f",
    "repeated deposits, combined repair, annual interest (USDT)",
    accrued_repeated(floor_curve(caps_both)),
    "19667",
    "12",
)
chk(
    "A4g",
    "repeated deposits, baseline, annual interest (USDT)",
    accrued_repeated(rates),
    "13453",
    "12",
)

# ---------------- analytic combined majorant, base APR ----------------
t = K / (K + 1)


def F(U):
    U = mpf(U)
    return 1 / (1 - U) if t >= U else (K + 1) * (U / t) ** K


def R0(U):
    U = mpf(U)
    if knots[1] >= U:
        return rates[0]
    for i in range(1, len(knots) - 1):
        if knots[i + 1] >= U:
            a, b = knots[i], knots[i + 1]
            return rates[i] + (rates[i + 1] - rates[i]) * (U - a) / (b - a)
    return rates[-1]


def q0(U):
    return R0(U) / F(U)


# sup over [0,1]: knots, plus interior stationary points of R0*(1-v) below t
cands = [mpf("1e-9")] + [k for k in knots if k > 0] + [t]
for i in range(1, len(knots) - 1):
    a, b = knots[i], knots[i + 1]
    m = (rates[i + 1] - rates[i]) / (b - a)
    if m != 0 and b <= t:
        # d/dv [ (r_i+m(v-a))(1-v) ] = 0
        vs = (m * (1 + a) - rates[i]) / (2 * m)
        if a < vs < b:
            cands.append(vs)
    if a >= t and m != 0:
        # d/dv [ (r_i+m(v-a)) * t^K/((K+1) v^K) ] = 0  ->  v = K(r_i-m a)/(m(K-1))
        inter = rates[i] - m * a
        if inter != 0:
            vs = K * inter / (m * (K - 1))
            if a < vs < b:
                cands.append(vs)
cands = [c for c in cands if 0 < c <= 1]
qsup = max(q0(c) for c in cands)
chk(
    "X7g",
    "combined analytic majorant, base APR (%)",
    F(mpf("1e-12")) * qsup * 100,
    "1.85",
    "0.006",
)


# ---------------- knot refinement: 64 subsegments ----------------
def refined_floor_base(nsub):
    ku = []
    for i in range(len(knots) - 1):
        for j in range(nsub):
            ku.append(knots[i] + (knots[i + 1] - knots[i]) * mpf(j) / nsub)
    ku.append(knots[-1])

    def cf(i):
        du = ku[i + 1] - ku[i]
        cfr = 1 + du / (1 - ku[i]) if ku[i] < 1 else INF
        left = 1 + K * du / ku[i] if ku[i] > 0 else INF
        den = ku[i + 1] - K * du
        cfx = min(left, ku[i + 1] / den if den > 0 else INF)
        return min(cfr, cfx)

    l = rates[-1]
    for i in range(len(ku) - 2, -1, -1):
        l = l / cf(i)
    return l


chk(
    "X7h",
    "both guarantees, linear floor base APR at 64 subsegments (%)",
    refined_floor_base(64) * 100,
    "1.80",
    "0.006",
)

# ---------------- appendix fresh depositor path ----------------
S0 = mpf("10e6")
Bap = mpf("9.99e6")
Tend = Bap / mpf("0.85")
xend = Tend - S0
ku2 = [mpf(x) for x in ["0", "0.8", "0.9", "0.95", "0.98", "0.995", "0.9999"]]
kr2 = [mpf(x) for x in ["0.05", "0.09", "0.135", "0.20", "0.32", "0.56", "1.10"]]


def tbl(U):
    U = mpf(U)
    for i in range(len(ku2) - 1):
        if ku2[i + 1] >= U:
            return kr2[i] + (kr2[i + 1] - kr2[i]) * (U - ku2[i]) / (ku2[i + 1] - ku2[i])
    return kr2[-1]


O, Ro, Rmax = mpf("0.8"), mpf("0.05"), mpf("1.0")
mk = (Rmax - Ro) / (1 - O)


def kink(U):
    U = mpf(U)
    return Ro + mk * (U - O) if U > O else Ro * U / O


def clamped(U):
    return min(mpf("0.05") / (1 - mpf(U)), mpf("1.0"))


for cid, fn, printed in [
    ("APX-d", tbl, "168000"),
    ("APX-e", kink, "428000"),
    ("APX-f", clamped, "497000"),
]:
    chk(
        cid,
        "appendix fresh path, terminal annualized income (USD)",
        xend * mpf("0.85") * fn(mpf("0.85")),
        printed,
        "600",
    )


# deposit at which the standard kink's marginal income turns negative
def dIdx(x):
    x = mpf(x)
    h = mpf("1e-8")
    f = lambda z: z * (Bap / (S0 + z)) * kink(Bap / (S0 + z))
    return (f(x + h) - f(x - h)) / (2 * h)


xstar = findroot(dIdx, mpf("1.2e6"))
chk(
    "APX-g",
    "standard kink: deposit at which marginal income turns negative (USD millions)",
    xstar / mpf("1e6"),
    "1.17",
    "0.006",
)
# prose rounding of the smoothing spread
L = log(1 / O)
Kstar = log(Rmax / Ro) / log(1 / O)
chk(
    "APX-h",
    "K=19 transition spread ends at (%)",
    O * exp(2 * L * (K - Kstar) / (K - 1)) * 100,
    "91.9",
    "0.06",
)

print(f"{'ID':<12} {'STATUS':<6} {'DESCRIPTION':<62} VALUES")
print("-" * 150)
n = 0
for cid, ok, desc, vals, _note in RES:
    print(f"{cid:<12} {'PASS' if ok else 'FAIL':<6} {desc:<62} {vals}")
    n += ok
print("-" * 150)
print(f"{n}/{len(RES)} second-pass checks reproduce the printed value")

assert all(bool(row[1]) for row in RES), "Failed verification check"
