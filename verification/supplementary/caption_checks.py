"""Check the quantitative claims made in figure captions against the plotted quantities."""

from mpmath import findroot, mp, mpf

mp.dps = 30
RES = []


def chk(cid, desc, ok, detail=""):
    RES.append((cid, bool(ok), desc, detail))


O, Ro, Rmax = mpf("0.8"), mpf("0.05"), mpf("1.0")
m = (Rmax - Ro) / (1 - O)
K = mpf(19)


def kink(u):
    u = mpf(u)
    return Ro + m * (u - O) if u > O else Ro * u / O


def kink_s(u):
    u = mpf(u)
    return m if u > O else Ro / O


UC = findroot(lambda u: Ro * (u / O) ** K - (Ro + m * (u - O)), mpf("0.92"))


def rep(u):
    u = mpf(u)
    return (
        (Ro * (u / O) ** K, K * Ro / O * (u / O) ** (K - 1))
        if (O < u <= UC)
        else (kink(u), kink_s(u))
    )


# --- Fig 3 caption: repaired branch rejoins at ~90.92% ---
chk(
    "cap3",
    "Fig 3: power repair rejoins at 90.92%",
    abs(UC * 100 - mpf("90.92")) < mpf("0.005"),
    f"UC={mp.nstr(UC * 100, 7)}%",
)

# --- Fig 10 (T07) caption: repaired marginal income reaches ZERO at 5% ownership;
#     the original becomes negative sooner ---
S0, B, b0 = mpf("1e7"), mpf("8.5e6"), mpf("1e5")
xend = (mpf("0.05") * S0 - b0) / mpf("0.95")
Uend = B / (S0 + xend)
alpha_end = (b0 + xend) / (S0 + xend)
chk(
    "cap10a",
    "Fig 10: path ends exactly at 5% ownership",
    abs(alpha_end - mpf("0.05")) < mpf("1e-12"),
    f"alpha={mp.nstr(alpha_end, 10)}, U={mp.nstr(Uend, 8)}",
)
r, s = rep(Uend)
eta_rep = Uend * s / r
marg_rep = Uend * r * (1 - alpha_end * (1 + eta_rep))
chk(
    "cap10b",
    "Fig 10: repaired marginal income is zero there (eta=K=19)",
    abs(eta_rep - K) < mpf("1e-12") and abs(marg_rep) < mpf("1e-15"),
    f"eta={mp.nstr(eta_rep, 10)}, marginal={mp.nstr(marg_rep, 4)}",
)
eta_orig = Uend * kink_s(Uend) / kink(Uend)
alpha_flip = 1 / (1 + eta_orig)
chk(
    "cap10c",
    "Fig 10: original turns negative at a SMALLER ownership than 5% (i.e. sooner)",
    alpha_flip < mpf("0.05"),
    f"original eta={mp.nstr(eta_orig, 7)}, flips at alpha={mp.nstr(alpha_flip * 100, 5)}%",
)

# --- Fig 7 (T03) caption: boundaries anchored at (80%,5%); combined cannot reach 100% ---
t = mpf("0.95")
fresh = lambda v: mpf("0.01") / (1 - mpf(v))
fixed = lambda v: Ro * (mpf(v) / O) ** K
both = lambda v: fresh(v) if mpf(v) <= t else mpf("0.2") * (mpf(v) / t) ** K
chk(
    "cap7a",
    "Fig 7: all three boundaries pass through (80%, 5%)",
    abs(fresh("0.8") - Ro) < mpf("1e-15")
    and abs(fixed("0.8") - Ro) < mpf("1e-15")
    and abs(both("0.8") - Ro) < mpf("1e-15"),
)
chk(
    "cap7b",
    "Fig 7: combined boundary is continuous at the 95% switch",
    abs(fresh(t) - mpf("0.2")) < mpf("1e-15"),
)
chk(
    "cap7c",
    "Fig 7: combined boundary cannot reach the 100% reference over the plotted range",
    both("0.999") < 1,
    f"combined(99.9%)={mp.nstr(both('0.999') * 100, 6)}%",
)

# --- Fig 17 (06-protection-cost) caption: panel (a) = 0.0095 x panel (b) ---
LENDER = 1 - mpf("0.05")
principal = mpf("10000")
supply = mpf("1e6")
chk(
    "cap17",
    "Fig 17: supplier change = 0.0095 x pool borrower change",
    abs(LENDER * principal / supply - mpf("0.0095")) < mpf("1e-18"),
    f"ratio={mp.nstr(LENDER * principal / supply, 8)}",
)

# --- Fig 19 (A02) caption: chord between 80% and 90% ---
rl, rh = fixed("0.8"), fixed("0.9")
mc = (rh - rl) / mpf("0.1")
chk(
    "cap19",
    "Fig 19: chord elasticity at 80% far exceeds the ceiling 19",
    O * mc / rl > K,
    f"chord eta(80%)={mp.nstr(O * mc / rl, 7)} vs ceiling 19",
)

# --- Fig 22 (A01) caption: plotted interval stays on rising branch (1% floor) ---
Sf, Bf = mpf("1e7"), mpf("9.5e6")
xmax = mpf("1e7")
Umin = Bf / (Sf + xmax)
chk(
    "cap22",
    "Fig 22: over the plotted deposit range the rate stays above the 1% floor (rising branch)",
    kink(Umin) > mpf("0.01"),
    f"U at max deposit={mp.nstr(Umin, 6)}, rate={mp.nstr(kink(Umin) * 100, 6)}% > 1%",
)

# --- Fig 9 (T05) caption: base rates 0 / 5% / 5%, maxima 100 / 110 / 100 ---
TU = [mpf(x) for x in ["0", "0.8", "0.9", "0.95", "0.98", "0.995", "0.9999"]]
TR = [mpf(x) for x in ["0.05", "0.09", "0.135", "0.20", "0.32", "0.56", "1.10"]]
clamp = lambda u: min(Ro / (1 - mpf(u)), mpf(1))
chk(
    "cap9",
    "Fig 9: standard kink base 0; table and clamped boundary base 5%; maxima 100/110/100",
    kink(0) == 0
    and TR[0] == Ro
    and clamp(0) == Ro
    and abs(kink(1) - 1) < mpf("1e-15")
    and TR[-1] == mpf("1.10")
    and clamp("0.95") == 1,
)

print(f"{'ID':<8} {'STATUS':<6} {'CLAIM':<70} DETAIL")
print("-" * 140)
n = 0
for cid, ok, desc, detail in RES:
    print(f"{cid:<8} {'PASS' if ok else 'FAIL':<6} {desc:<70} {detail}")
    n += ok
print("-" * 140)
print(f"{n}/{len(RES)} caption claims verified")

assert all(bool(row[1]) for row in RES), "Failed verification check"
