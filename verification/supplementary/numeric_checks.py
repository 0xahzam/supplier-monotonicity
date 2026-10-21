"""Independent recomputation of every numeric value printed in the manuscript.

Nothing is read from analysis/data/*.csv or the figure generators. Every value is
rebuilt from the parameters stated in the paper text, then compared to the printed
figure at the precision the paper prints it to.
"""

from mpmath import exp, findroot, log, mp, mpf

mp.dps = 40

RES = []


def chk(cid, desc, got, printed, tol=None, note=""):
    got = mpf(got)
    printed_v = mpf(printed)
    if tol is None:
        # agree to the precision the paper prints
        s = str(printed)
        dec = len(s.split(".")[1]) if "." in s else 0
        tol = mpf(10) ** (-dec) / 2 * mpf("1.0000001")
    ok = abs(got - printed_v) <= tol
    RES.append((cid, ok, desc, f"computed {mp.nstr(got, 8)}  printed {printed}", note))


# ================= single-kink illustrative market =================
O, Ro, Rmax = mpf("0.8"), mpf("0.05"), mpf("1.0")
m = (Rmax - Ro) / (1 - O)
chk("F1", "steep-branch slope m=(Rmax-Ro)/(1-O)", m, "4.75")
chk("F2", "elasticity just above the kink, O*m/Ro", O * m / Ro, "76")
chk("F3", "protected share there, 1/(1+76)", 100 / (1 + O * m / Ro), "1.3")
chk("F5", "elasticity at U=1, m/Rmax", m / Rmax, "4.75")

Rb = lambda U: Ro + m * (U - O) if U > O else Ro * U / O
T0, B, b0 = mpf("10e6"), mpf("8.3e6"), mpf("1e6")
U0 = B / T0
chk("F6a", "utilization before the deposit", U0 * 100, "83")
I_before = b0 * U0 * Rb(U0)
chk(
    "F6b",
    "annualized income before the deposit (USD)",
    I_before,
    "159800",
    tol=mpf("100"),
)
x = B / mpf("0.8") - T0
chk("F6c", "deposit that returns U to 80% (USD)", x, "375000", tol=mpf("1"))
I_after = (b0 + x) * mpf("0.8") * Rb(mpf("0.8"))
chk("F6d", "annualized income after the deposit (USD)", I_after, "55000", tol=mpf("1"))
chk("F6e", "balance growth (%)", ((b0 + x) / b0 - 1) * 100, "37.5", tol=mpf("1e-30"))
chk("F6f", "income fall (%)", (1 - I_after / I_before) * 100, "66", tol=mpf("0.5"))

# ================= endpoint bound =================
Kstar = log(Rmax / Ro) / log(1 / O)
chk("K6a", "K* = ln(Rmax/Ro)/ln(1/O)", Kstar, "13.43")
chk("K6b", "alphabar_max = 1/(1+K*) (%)", 100 / (1 + Kstar), "6.93")
for eta, share in [(9, "10"), (19, "5"), (99, "1")]:
    chk(f"C6-{eta}", f"eta={eta} protects 1/(1+eta) (%)", mpf(100) / (1 + eta), share)

# ================= fresh profile readings =================
for U, share in [("0.5", "50"), ("0.9", "10"), ("0.99", "1")]:
    chk(f"H5-{U}", f"fresh profile 1-U at U={U} (%)", (1 - mpf(U)) * 100, share)
K = mpf(19)
chk("H6n", "envelope crossing U=K/(1+K) (%)", K / (1 + K) * 100, "95")

# ================= minimal-change rejoin =================
Uc = findroot(lambda U: Ro * (U / O) ** K - (Ro + m * (U - O)), mpf("0.92"))
chk("M4", "power-law rejoin U_c for K=19 (%)", Uc * 100, "90.92")

# ================= discretisation chord =================
Rl, Rh = Ro, Ro * (mpf("0.9") / O) ** K
mc = (Rh - Rl) / mpf("0.1")
chk(
    "DSC",
    "chord elasticity at 80% after sampling the K=19 boundary at 80/90%",
    O * mc / Rl,
    "67",
    tol=mpf("0.5"),
)

# ================= multi-kink USDT market =================
# knots stated in the paper, including the point where the 0.5% floor meets the ramp
u_ramp = mpf("0.005") * mpf("0.8") / mpf("0.0525")
chk("X-ramp", "floor meets the initial ramp at (%)", u_ramp * 100, "7.619")
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
chk(
    "X-pp",
    "99% to 99.5% carries (percentage points)",
    (rates[7] - rates[6]) * 100,
    "21.1875",
)

INF = mpf("1e30")


def c_fresh(i):
    return 1 + (knots[i + 1] - knots[i]) / (1 - knots[i]) if knots[i] < 1 else INF


def c_fixed(i, Kv):
    du = knots[i + 1] - knots[i]
    left = 1 + Kv * du / knots[i] if knots[i] > 0 else INF
    den = knots[i + 1] - Kv * du
    right = knots[i + 1] / den if den > 0 else INF
    return min(left, right)


def caps(mode, Kv=K):
    n = len(knots) - 1
    if mode == "fresh":
        return [c_fresh(i) for i in range(n)]
    if mode == "fixed":
        return [c_fixed(i, Kv) for i in range(n)]
    return [min(c_fresh(i), c_fixed(i, Kv)) for i in range(n)]


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


def lower_only(c):
    r = [mpf(0)] * len(rates)
    r[0] = rates[0]
    for i in range(len(c)):
        r[i + 1] = min(rates[i + 1], c[i] * r[i])
    return r


cf, cb = caps("fresh"), caps("both")
chk("X7a", "fresh-only fixed-top floor, base APR (%)", floor_curve(cf)[0] * 100, "3.47")
chk("X7b", "fresh-only raise-only repair, base APR (%)", raise_only(cf)[0] * 100, "6.39")
chk(
    "X7c",
    "both guarantees, minimum base APR on these knots (%)",
    floor_curve(cb)[0] * 100,
    "8.68",
)
chk(
    "X7d",
    "fresh-only lower-only repair, top APR (%)",
    lower_only(cf)[-1] * 100,
    "12.04",
)
chk(
    "X7e",
    "both guarantees, lower-only repair, top APR (%)",
    lower_only(cb)[-1] * 100,
    "4.82",
)

# continuous combined bound
t = K / (K + 1)
chk(
    "X10n",
    "continuous combined base bound R_max t^K/(K+1) (%)",
    mpf("0.9") * t**K / (K + 1) * 100,
    "1.70",
)


# ---- analytic power minorant on the multi-kink baseline (fixed share, K=19) ----
def R0(U):
    U = mpf(U)
    if knots[1] >= U:
        return rates[0]
    for i in range(1, len(knots) - 1):
        if knots[i + 1] >= U:
            a, b_ = knots[i], knots[i + 1]
            return rates[i] + (rates[i + 1] - rates[i]) * (U - a) / (b_ - a)
    return rates[-1]


# q0 = R0/U^K ; running infimum over (0,1]. On each linear segment the extremum is
# interior or at an endpoint, so scan knots plus a dense sweep per segment.
def q0(U):
    return R0(U) / U**K


cands = []
for i in range(1, len(knots) - 1):
    a, b_ = knots[i], knots[i + 1]
    cands += [a, b_]
    # interior stationary point of (r_i + m(U-a))/U^K  =>  U* = K*(r_i - m*a)/(m*(K-1))
    mm = (rates[i + 1] - rates[i]) / (b_ - a)
    if mm != 0:
        inter = rates[i] - mm * a
        if K != 1 and inter != 0:
            Us = K * inter / (mm * (K - 1))
            if a < Us < b_:
                cands.append(Us)
qmin = min(q0(c) for c in cands if c > 0)
chk(
    "X7f",
    "fixed-share power minorant, APR at U=1 (%)",
    qmin * mpf(1) ** K * 100,
    "57.65",
)

# ================= smoothing table =================
L, A = log(1 / O), log(Rmax / Ro)
chk("S9a", "L = ln(1/O)", L, "0.2231")
chk("S9b", "A = ln(Rmax/Ro)", A, "2.9957")
eta0 = mpf(1)
etamax = lambda w: (A - eta0 * w / 2) / (L - w / 2)
wK = 2 * L * (K - Kstar) / (K - eta0)
chk("S9c", "widest admissible ramp width for K=19", wK, "0.1382")
for w, ends, em, share in [
    ("0.0000", "80.00", "13.43", "6.93"),
    ("0.0500", "84.10", "14.99", "6.25"),
    ("0.1000", "88.41", "17.01", "5.55"),
    ("0.1382", "91.86", "19.00", "5.00"),
    ("0.2231", "100.00", "25.85", "3.72"),
]:
    wv = mpf(w)
    chk(
        f"S9-{w}-end",
        f"w={w}: ramp ends at O*exp(w) (%)",
        O * exp(wv) * 100,
        ends,
        tol=mpf("0.02"),
    )
    chk(f"S9-{w}-eta", f"w={w}: plateau elasticity", etamax(wv), em, tol=mpf("0.011"))
    chk(
        f"S9-{w}-shr",
        f"w={w}: protected share (%)",
        100 / (1 + etamax(wv)),
        share,
        tol=mpf("0.011"),
    )

# ================= appendix piecewise-linear example table =================
ku = [mpf(x) for x in ["0", "0.8", "0.9", "0.95", "0.98", "0.995", "0.9999"]]
kr = [mpf(x) for x in ["0.05", "0.09", "0.135", "0.20", "0.32", "0.56", "1.10"]]
tbl = [
    ("1.800", "1.800"),
    ("1.500", "1.500"),
    ("1.481", "1.500"),
    ("1.600", "1.600"),
    ("1.750", "1.750"),
    ("1.964", "1.980"),
]
for i, (ratio, cap) in enumerate(tbl):
    chk(
        f"TBL{i}-r",
        f"segment {i} rate ratio",
        kr[i + 1] / kr[i],
        ratio,
        tol=mpf("0.0006"),
    )
    chk(
        f"TBL{i}-c",
        f"segment {i} maximum ratio 1+(du)/(1-u_L)",
        1 + (ku[i + 1] - ku[i]) / (1 - ku[i]),
        cap,
        tol=mpf("0.0006"),
    )

# ================= clamped fresh boundary readings =================
r0b = mpf("0.05")
chk(
    "APX-a",
    "clamped fresh boundary r0/(1-U) at U=85% (%)",
    r0b / (1 - mpf("0.85")) * 100,
    "33",
    tol=mpf("0.5"),
)
chk("APX-b", "standard kink at U=85% (%)", Rb(mpf("0.85")) * 100, "29", tol=mpf("0.5"))
chk(
    "APX-c",
    "clamped fresh boundary reaches 100% at U (%)",
    (1 - r0b / Rmax) * 100,
    "95",
)


# ================= lifecycle: fresh-only, single deposit history =================
def curve_eval(rs, U):
    U = mpf(U)
    for i in range(len(knots) - 1):
        if knots[i + 1] >= U:
            a, b_ = knots[i], knots[i + 1]
            if b_ == a:
                return rs[i]
            return rs[i] + (rs[i + 1] - rs[i]) * (U - a) / (b_ - a)
    return rs[-1]


days = [0, 90, 180, 270, 365]
Us = [mpf("0.80"), mpf("0.95"), mpf("0.995"), mpf("0.85"), mpf("0.80")]


def accrued(rs, principal=mpf("10000"), f=mpf("0.05"), n=200000):
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
    "A4a",
    "fresh-only baseline accrued interest (USDT)",
    accrued(rates),
    "1983",
    tol=mpf("6"),
)
chk(
    "A4b",
    "fresh-only floor accrued interest (USDT)",
    accrued(floor_curve(cf)),
    "1287",
    tol=mpf("6"),
)
chk(
    "A4c",
    "fresh-only raise-only accrued interest (USDT)",
    accrued(raise_only(cf)),
    "2231",
    tol=mpf("6"),
)

# ---- report ----
print(f"{'ID':<14} {'STATUS':<6} {'DESCRIPTION':<58} VALUES")
print("-" * 140)
np_ = 0
for cid, ok, desc, vals, note in RES:
    print(f"{cid:<14} {'PASS' if ok else 'FAIL':<6} {desc:<58} {vals}")
    if note:
        print(f"{'':<21} note: {note}")
    np_ += ok
print("-" * 140)
print(f"{np_}/{len(RES)} numeric checks reproduce the printed value")

assert all(bool(row[1]) for row in RES), "Failed verification check"
