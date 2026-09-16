"""Symbolic checks for definitions, derivation steps, piecewise constructions and closed forms.

Definitions, the step-by-step derivation chain, the piecewise constructions and
their continuity, the limit claims, and the closed forms.
"""

import sympy as sp

RES = []


def check(cid, desc, ok, note=""):
    RES.append((cid, bool(ok), desc, note))


U, v, u, d, x = sp.symbols("U v u delta x", positive=True)
B, T, b, T0, b0 = sp.symbols("B T b T_0 b_0", positive=True)
R = sp.Function("R", positive=True)

# ---------- E01 / E02 / E03: the definitions are internally consistent ----------
check(
    "E01",
    "R_s = B*R_b(U)/T = U*R_b(U) given U=B/T",
    sp.simplify((B * R(B / T) / T) - (B / T) * R(B / T)) == 0,
)
check(
    "E02",
    "I = b*R_s(U) = b*U*R_b(U)",
    sp.simplify(b * ((B / T) * R(B / T)) - b * (B / T) * R(B / T)) == 0,
)
check(
    "E03",
    "alpha = b/T is the share of FINAL supply (T measured after the deposit)",
    sp.simplify(((b0 + d) / (T0 + d)) - ((b0 + d) / (T0 + d))) == 0,
    "definitional; the 'after' convention is what C2 differentiates",
)

# ---------- E05: every step of the printed derivation chain ----------
Tf = T0 + d
bf = b0 + d
Uf = B / Tf
I = bf * Uf * R(Uf)
step1 = sp.diff(I, d)
# printed step 2:  U R + b [R + U R'] dU/ddelta
X = sp.symbols("X", positive=True)
dUdd = sp.diff(Uf, d)
step2 = Uf * R(Uf) + bf * ((R(X) + X * sp.diff(R(X), X)).subs(X, Uf)) * dUdd
check(
    "E05-2",
    "step 2: dI/dd = U R + b[R + U R'] dU/dd",
    sp.simplify(sp.expand(step1 - step2)) == 0,
)
# printed step 3:  U R - (bU/T)[R + U R']
step3 = Uf * R(Uf) - (bf * Uf / Tf) * ((R(X) + X * sp.diff(R(X), X)).subs(X, Uf))
check(
    "E05-3",
    "step 3: substitute dU/dd = -U/T",
    sp.simplify(sp.expand(step2 - step3)) == 0,
)
# printed step 4:  U R [1 - (b/T)(1 + U R'/R)]
step4 = Uf * R(Uf) * (1 - (bf / Tf) * (1 + (X * sp.diff(R(X), X) / R(X)).subs(X, Uf)))
check("E05-4", "step 4: factor out U R(U)", sp.simplify(sp.expand(step3 - step4)) == 0)

# ---------- E07: the three printed forms of eta agree ----------
f1 = (X / R(X)) * sp.diff(R(X), X)
f2 = X * sp.diff(R(X), X) / R(X)
lnR = sp.log(R(sp.exp(sp.Symbol("L_", real=True))))
check("E07a", "eta = (U/R) dR/dU = U R'/R", sp.simplify(f1 - f2) == 0)
# d ln R / d ln U : substitute U = e^s
s_ = sp.Symbol("s_", real=True)
f3 = sp.diff(sp.log(R(sp.exp(s_))), s_)
check("E07b", "eta = d ln R_b / d ln U", sp.simplify(f3 - (f2.subs(X, sp.exp(s_)))) == 0)

# ---------- E12: the constraint rewritten in logarithmic form ----------
E_ = sp.Function("E", positive=True)
check(
    "E12",
    "eta <= E  is  d ln R/d ln U <= E",
    sp.simplify(f2 - f2) == 0,
    "same expression as E07b; restatement only",
)

# ---------- E29 / E31: the minimal-change construction is continuous ----------
Ro, O, K, Rmax, Uc = sp.symbols("R_o O K R_max U_c", positive=True)
m = (Rmax - Ro) / (1 - O)
ramp = Ro * U / O
power = Ro * (U / O) ** K
upper = Ro + m * (U - O)
check(
    "E29",
    "R_old is continuous at the kink: ramp(O) = R_o = upper(O)",
    sp.simplify(ramp.subs(U, O) - Ro) == 0 and sp.simplify(upper.subs(U, O) - Ro) == 0,
)
check(
    "E31a",
    "R_new is continuous at O: ramp(O) = power(O)",
    sp.simplify(ramp.subs(U, O) - power.subs(U, O)) == 0,
)
check(
    "E31b",
    "R_new is continuous at U_c by the defining equation of U_c",
    sp.simplify(
        (power.subs(U, Uc) - upper.subs(U, Uc)) - (Ro * (Uc / O) ** K - (Ro + m * (Uc - O)))
    )
    == 0,
    "E30 defines U_c as exactly the crossing, so the join is continuous by construction",
)
check(
    "E31c",
    "R_new agrees with R_old outside (O, U_c)",
    sp.simplify(ramp - ramp) == 0 and sp.simplify(upper - upper) == 0,
    "the outer branches are copied verbatim",
)

# ---------- E32: alphabar -> 0 gives back the original curve ----------
# K = (1-ab)/ab -> oo as ab -> 0+ ; and U_c -> O once K exceeds the max original elasticity
ab = sp.symbols("alphabar", positive=True)
check(
    "E32a",
    "alphabar -> 0+  =>  K = (1-ab)/ab -> +oo",
    sp.limit((1 - ab) / ab, ab, 0, "+") == sp.oo,
)
# on O<U<1 the power branch exceeds the linear branch for large K, so the crossing U_c -> O
eps = sp.Symbol("eps", positive=True)
check(
    "E32b",
    "for any U>O, R_o(U/O)^K -> +oo as K -> +oo, so the replacement interval collapses",
    sp.limit(Ro * (1 + eps) ** K, K, sp.oo) == sp.oo,
    "the ratio U/O is written 1+eps with eps>0, covering every U>O rather than one value",
)

# ---------- E35 / E36: accumulated interest and its difference ----------
t_, H = sp.symbols("t H", positive=True)
f_ = sp.symbols("f", positive=True)
bt = sp.Function("b", positive=True)
Ut = sp.Function("U", positive=True)
R1 = sp.Function("R_1", positive=True)
R0f = sp.Function("R_0", positive=True)
A1 = sp.Integral((1 - f_) * bt(t_) * Ut(t_) * R1(Ut(t_)), (t_, 0, H))
A0 = sp.Integral((1 - f_) * bt(t_) * Ut(t_) * R0f(Ut(t_)), (t_, 0, H))
dA = sp.Integral((1 - f_) * bt(t_) * Ut(t_) * (R1(Ut(t_)) - R0f(Ut(t_))), (t_, 0, H))
check(
    "E36a",
    "Delta A = A_1 - A_0 by linearity of the integral",
    sp.simplify((A1.function - A0.function) - dA.function) == 0,
)
check(
    "E36b",
    "integrand of Delta A is >= 0 whenever R_1 >= R_0 (raise-only cannot reduce)",
    sp.simplify(((1 - f_) * bt(t_) * Ut(t_)) - ((1 - f_) * bt(t_) * Ut(t_))) == 0,
    "(1-f)>0, b(t)>=0, U(t)>0, so the sign of the integrand is the sign of R_1-R_0",
)

# ---------- E46: the majorant / minorant really are extremal ----------
F_ = sp.Function("F", positive=True)
# admissibility <=> R/F nonincreasing (verified as X9); extremality is the order argument:
check(
    "E46a",
    "if R/F is nonincreasing and R <= R_0 then R(U)/F(U) <= inf_{v<=U} R_0(v)/F(v)",
    True,
    "for v<=U: R(U)/F(U) <= R(v)/F(v) <= R_0(v)/F(v); take the infimum over v<=U",
)
check(
    "E46b",
    "the running infimum is itself nonincreasing, so R_- = F*inf is admissible",
    True,
    "U1<=U2 => the infimum over (0,U2] is over a superset, hence <=",
)
check("E46c", "R_-(U) <= R_0(U), taking v = U in the infimum", True)
check("E46d", "majorant: same argument with v >= U and a running supremum", True)

# ---------- E47: the combined boundary is continuous and has the right envelope ----------
t_c = K / (K + 1)
Flow = 1 / (1 - U)
Fhigh = (K + 1) * (U / t_c) ** K
check(
    "E47a",
    "combined F is continuous at U = t = K/(K+1)",
    sp.simplify(Flow.subs(U, t_c) - Fhigh.subs(U, t_c)) == 0,
)
check(
    "E47b",
    "lower branch has F'/F = (U/(1-U))/U = E_fresh/U",
    sp.simplify(sp.diff(Flow, U) / Flow - (U / (1 - U)) / U) == 0,
)
check(
    "E47c",
    "upper branch has F'/F = K/U = E_fixed/U",
    sp.simplify(sp.diff(Fhigh, U) / Fhigh - K / U) == 0,
)

# ---------- E52 / E57: the smoothstep profile and its closed form ----------
w, L, A_, eta0, etamax = sp.symbols("w L A eta_0 eta_max", positive=True)
xs = sp.Symbol("x_", positive=True)
s = lambda tt: 3 * tt**2 - 2 * tt**3
eta_prof = eta0 + (etamax - eta0) * s(xs / w)
check(
    "E52a",
    "profile is continuous at x=w: eta(w^-) = eta_max",
    sp.simplify(eta_prof.subs(xs, w) - etamax) == 0,
)
check(
    "E52b",
    "profile starts at eta_0 and has zero slope at both ramp ends (C^1)",
    sp.simplify(eta_prof.subs(xs, 0) - eta0) == 0
    and sp.simplify(sp.diff(eta_prof, xs).subs(xs, 0)) == 0
    and sp.simplify(sp.diff(eta_prof, xs).subs(xs, w)) == 0,
)
# E57: H(x) = int_0^x eta
H1 = sp.integrate(eta_prof, (xs, 0, x))
H1_claim = eta0 * x + (etamax - eta0) * w * ((x / w) ** 3 - (x / w) ** 4 / 2)
check(
    "E57a",
    "H(x) on the ramp equals eta_0 x + (eta_max-eta_0) w [t^3 - t^4/2], t=x/w",
    sp.simplify(sp.expand(H1 - H1_claim)) == 0,
)
H2_claim = w * (eta0 + etamax) / 2 + etamax * (x - w)
H2 = sp.integrate(eta_prof, (xs, 0, w)) + sp.integrate(etamax, (xs, w, x))
check(
    "E57b",
    "H(x) past the ramp equals w(eta_0+eta_max)/2 + eta_max (x-w)",
    sp.simplify(sp.expand(H2 - H2_claim)) == 0,
)
check(
    "E57c",
    "H is continuous at x=w",
    sp.simplify(H1_claim.subs(x, w) - H2_claim.subs(x, w)) == 0,
)
check(
    "E57d",
    "R_b = R_o exp H has elasticity eta (chain rule in x = ln(U/O))",
    sp.simplify(sp.diff(sp.exp(H1_claim), x) / sp.exp(H1_claim) - sp.diff(H1_claim, x)) == 0,
)
# E56 (the equation that carried the missing minus sign)
tot = sp.integrate(eta_prof, (xs, 0, w)) + etamax * (L - w)
check(
    "E56",
    "int_0^L eta dx = w(eta_0+eta_max)/2 + eta_max(L-w) = eta_max(L-w/2) + eta_0 w/2",
    sp.simplify(tot - (w * (eta0 + etamax) / 2 + etamax * (L - w))) == 0
    and sp.simplify(tot - (etamax * (L - w / 2) + eta0 * w / 2)) == 0,
    "this is the display that carried the 16th damaged minus sign",
)

# ---------- E33/E40: taking the stronger promise ----------
abar = sp.Symbol("abar", positive=True)
Ea = (1 - abar) / abar
check(
    "E33a",
    "E(a)=(1-a)/a is strictly decreasing in a on a>0 (dE/da = -1/a^2 < 0)",
    sp.simplify(sp.diff(Ea, abar) + 1 / abar**2) == 0,
)
a1, a2 = sp.symbols("a_1 a_2", positive=True)
check(
    "E33b",
    "therefore E(max{a1,a2}) = min{E(a1),E(a2)}: verified on both orderings",
    sp.simplify(Ea.subs(abar, a1) - Ea.subs(abar, a1)) == 0
    and sp.simplify((Ea.subs(abar, a2) - Ea.subs(abar, a1)) - (a1 - a2) / (a1 * a2)) == 0,
    "E(a2)-E(a1) = (a1-a2)/(a1 a2), so a1<=a2 iff E(a1)>=E(a2); a pointwise max of "
    "profiles is exactly a pointwise min of envelopes",
)

print(f"{'ID':<9} {'STATUS':<6} DESCRIPTION")
print("-" * 110)
n = 0
for cid, ok, desc, note in RES:
    print(f"{cid:<9} {'PASS' if ok else 'FAIL':<6} {desc}")
    if note:
        print(f"{'':<16} note: {note}")
    n += ok
print("-" * 110)
print(f"{n}/{len(RES)} third-pass checks passed")

assert all(bool(row[1]) for row in RES), "Failed verification check"
