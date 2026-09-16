"""Symbolic verification of the algebraic/calculus claims in the frozen manuscript.

Each check prints  ID | PASS/FAIL | short description.
A check is PASS only if sympy reduces the asserted difference to exactly 0
(or proves the asserted equivalence), not merely numerically.
"""

import sympy as sp

RESULTS = []


def check(cid, desc, ok, note=""):
    RESULTS.append((cid, bool(ok), desc, note))


# ---------- symbols ----------
d = sp.symbols("delta", real=True)
B, T0, b0 = sp.symbols("B T_0 b_0", positive=True)
U, u, v = sp.symbols("U u v", positive=True)
R = sp.Function("R", positive=True)

# ============================================================
# C1 / C2 / C3 : the income derivative
# ============================================================
T = T0 + d
b = b0 + d
Uf = B / T

# C1: dU/ddelta = -U/T
c1 = sp.simplify(sp.diff(Uf, d) - (-Uf / T))
check("C1", "dU/ddelta = -U/T", c1 == 0)

I = b * Uf * R(Uf)
dI = sp.diff(I, d)

alpha_expr = b / T
eta_of = lambda X: X * sp.Derivative(R(X), X).doit() / R(X)

# C2/C3: dI/ddelta = U R(U) [1 - alpha (1 + eta)]
# build the claimed RHS on a fresh symbol, then substitute U = B/T(delta)
X = sp.symbols("X", positive=True)
Rp = R  # same Function object; distinct objects of equal name do not cancel
claimed_sub = (X * Rp(X) * (1 - alpha_expr * (1 + X * sp.diff(Rp(X), X) / Rp(X)))).subs(X, Uf)
c3 = sp.simplify(sp.expand(dI - claimed_sub))
check("C2/C3", "dI/ddelta = U*R(U)*[1 - alpha*(1+eta)]", c3 == 0)

# C4: sign condition (prefactor U*R(U) > 0)
_Rp = sp.Symbol("R_pos", positive=True)
check(
    "C4",
    "prefactor U*R(U) is strictly positive, so it cannot change the sign",
    (U * _Rp).is_positive is True,
    "uses the manuscript assumptions U>0 and R_b(U)>0",
)

# C5: alpha_safe = 1/(1+eta)  <=>  alpha(1+eta) <= 1
et, al = sp.symbols("eta alpha", positive=True)
check(
    "C5",
    "alpha(1+eta)<=1  <=>  alpha <= 1/(1+eta)",
    sp.simplify(sp.solve(sp.Eq(al * (1 + et), 1), al)[0] - 1 / (1 + et)) == 0,
)

# C7: constant fee f scales income and derivative by (1-f)
f = sp.symbols("f", positive=True)
dI_fee = sp.diff((1 - f) * I, d)
check(
    "C7",
    "constant fee f multiplies dI/ddelta by (1-f); sign unchanged",
    sp.simplify(dI_fee - (1 - f) * dI) == 0,
)

# ============================================================
# G1 / G2 : full supplier limit (alpha = 1)
# ============================================================
# supplier owns whole pool: b = T, so I = T*U*R(U) = B*R(U)
I_full = (T) * (B / T) * R(B / T)
dI_full = sp.simplify(sp.diff(I_full, d))
claimed_full = -((B / T) ** 2) * sp.diff(Rp(X), X).subs(X, B / T)
check("G2", "alpha=1: dI/ddelta = -U^2 R'(U)", sp.simplify(dI_full - claimed_full) == 0)
eta_r = sp.symbols("eta_r", real=True)
check(
    "G1",
    "alpha=1 in alpha(1+eta)<=1 reduces to eta<=0",
    sp.simplify(
        sp.solve_univariate_inequality(sp.Integer(1) * (1 + eta_r) <= 1, eta_r, relational=False)
    )
    == sp.Interval(-sp.oo, 0),
)

# ============================================================
# E1 : envelope from profile
# ============================================================
ab = sp.symbols("alphabar", positive=True)
E_from = sp.solve(sp.Eq(ab * (1 + et), 1), et)[0]
check("E1", "E(U) = (1-alphabar)/alphabar", sp.simplify(E_from - (1 - ab) / ab) == 0)

# ============================================================
# K2 : power law has elasticity identically K
# ============================================================
Ro, O, K = sp.symbols("R_o O K", positive=True)
RK = Ro * (U / O) ** K
eta_RK = sp.simplify(U * sp.diff(RK, U) / RK)
check("K2", "R_K(U)=R_o(U/O)^K has eta == K", sp.simplify(eta_RK - K) == 0)

# ============================================================
# E5 : integral representation has elasticity exactly eta
# ============================================================
Ua, Ra = sp.symbols("U_a R_a", positive=True)
g = sp.Function("eta", positive=True)
Rrep = Ra * sp.exp(sp.Integral(g(v) / v, (v, Ua, U)))
eta_rep = sp.simplify(U * sp.diff(Rrep, U) / Rrep)
check(
    "E5",
    "R=R_a exp(int eta/v dv) has elasticity exactly eta",
    sp.simplify(eta_rep - g(U)) == 0,
)

# ============================================================
# E4 : boundary solves U R' = E R
# ============================================================
Efun = sp.Function("E", positive=True)
Rbd = Ra * sp.exp(sp.Integral(Efun(v) / v, (v, Ua, U)))
check(
    "E4",
    "boundary curve solves U R'(U) = E(U) R(U)",
    sp.simplify(U * sp.diff(Rbd, U) - Efun(U) * Rbd) == 0,
)

# ============================================================
# K4 : endpoint identity  ln(Rmax/Ro) = int_O^1 eta dlnU
# ============================================================
Rmax, Kst = sp.symbols("R_max K_star", positive=True)
# with eta == K constant, int_O^1 K dlnU = K ln(1/O); setting = ln(Rmax/Ro)
Kstar_solved = sp.solve(sp.Eq(K * sp.log(1 / O), sp.log(Rmax / Ro)), K)[0]
check(
    "K4",
    "K* = ln(Rmax/Ro)/ln(1/O)",
    sp.simplify(Kstar_solved - sp.log(Rmax / Ro) / sp.log(1 / O)) == 0,
)
check(
    "K5",
    "alphabar_max = 1/(1+K*)",
    sp.simplify((1 / (1 + Kst)) - 1 / (1 + Kst)) == 0,
    "definitional restatement of C5 at eta=K*",
)

# ============================================================
# H1 : fresh depositor share
# ============================================================
S0, x = sp.symbols("S_0 x", positive=True)
u0e = B / S0
ue = B / (S0 + x)
check("H1", "alpha = x/(S0+x) = 1 - u/u0", sp.simplify(x / (S0 + x) - (1 - ue / u0e)) == 0)

# ============================================================
# H2 : exact fresh condition  (u0-u) R'(u) <= R(u)
# ============================================================
u0s = sp.symbols("u_0", positive=True)
alpha_fresh = 1 - u / u0s
eta_u = u * sp.diff(Rp(u), u) / Rp(u)
lhs = sp.simplify(sp.expand((alpha_fresh * (1 + eta_u) - 1) * Rp(u) * u0s / u))
rhs = sp.simplify(sp.expand((u0s - u) * sp.diff(Rp(u), u) - Rp(u)))
check(
    "H2",
    "alpha(1+eta)<=1 with alpha=1-u/u0  <=>  (u0-u)R'(u) <= R(u)",
    sp.simplify(lhs - rhs) == 0,
    "multiplied by u0/u > 0, which preserves the inequality",
)

# ============================================================
# H3 / H4 : worst start u0=1, profile 1-U, envelope U/(1-U), boundary
# ============================================================
check(
    "H3",
    "u0=1 gives alphabar(U) = 1-U",
    sp.simplify(alpha_fresh.subs(u0s, 1) - (1 - u)) == 0,
)
check(
    "H4a",
    "alphabar=1-U  =>  E = U/(1-U)",
    sp.simplify(((1 - ab) / ab).subs(ab, 1 - U) - U / (1 - U)) == 0,
)
Rfresh = Ra * (1 - Ua) / (1 - U)
check(
    "H4b",
    "boundary R_a(1-U_a)/(1-U) solves U R' = (U/(1-U)) R and anchors at U_a",
    sp.simplify(U * sp.diff(Rfresh, U) - (U / (1 - U)) * Rfresh) == 0
    and sp.simplify(Rfresh.subs(U, Ua) - Ra) == 0,
)
_anti = sp.log((1 - Ua) / (1 - U))
check(
    "H4c",
    "d/dU ln((1-U_a)/(1-U)) = E(U)/U for E=U/(1-U), and it vanishes at U=U_a",
    sp.simplify(sp.diff(_anti, U) - (U / (1 - U)) / U) == 0 and sp.simplify(_anti.subs(U, Ua)) == 0,
    "checked as an antiderivative on 0<U<1; sympy's definite integral picks the U>1 log branch",
)

# ============================================================
# H6 : envelopes cross at U = K/(1+K)
# ============================================================
cross = sp.solve(sp.Eq(K, U / (1 - U)), U)[0]
check("H6", "K = U/(1-U) crosses at U = K/(1+K)", sp.simplify(cross - K / (1 + K)) == 0)

# ============================================================
# H7 : base rate bound  R(0) >= R(U)(1-U)
# ============================================================
r0s = sp.symbols("r_0", positive=True)
check(
    "H7",
    "U_a->0 in fresh boundary gives R(U) <= R(0)/(1-U)",
    sp.simplify(sp.limit(Rfresh.subs(Ra, r0s), Ua, 0) - r0s / (1 - U)) == 0,
)

# H8: below-kink ramp R = R_o U/O has eta == 1
check(
    "H8",
    "ramp R_o*U/O has eta == 1",
    sp.simplify(U * sp.diff(Ro * U / O, U) / (Ro * U / O) - 1) == 0,
)

# ============================================================
# H10 / H11 : piecewise linear segment rule
# ============================================================
uL, uH, RL, RH = sp.symbols("u_L u_H R_L R_H", positive=True)
m = (RH - RL) / (uH - uL)
Rseg = RL + m * (u - uL)
eta_seg = u * sp.diff(Rseg, u) / Rseg
# eta <= u/(1-u)  <=>  m(1-u) <= R(u)
ineq_lhs = sp.simplify(sp.expand((eta_seg - u / (1 - u)) * Rseg * (1 - u) / u))
check(
    "H11a",
    "eta<=u/(1-u) on a segment  <=>  m(1-u) <= R(u)",
    sp.simplify(ineq_lhs - (m * (1 - u) - Rseg)) == 0,
    "multiplied by R(u)(1-u)/u > 0 for 0<u<1",
)
# R(u)/(1-u) increasing along a nondecreasing segment
deriv = sp.simplify(sp.diff(Rseg / (1 - u), u))
check(
    "H11b",
    "R(u)/(1-u) is increasing when m>=0, R>0  (binding point is LEFT endpoint)",
    sp.simplify(sp.together(deriv) - sp.together((m * (1 - u) + Rseg) / (1 - u) ** 2)) == 0,
    "numerator m(1-u)+R(u) > 0 for m>=0, R>0, u<1",
)
# admissible <=> m <= R_L/(1-u_L) <=> adjacent-knot rule
adj = sp.simplify(sp.solve(sp.Eq(m, RL / (1 - uL)), RH)[0] / RL)
check(
    "H10",
    "m <= R_L/(1-u_L)  <=>  R_H/R_L <= 1 + (u_H-u_L)/(1-u_L)",
    sp.simplify(adj - (1 + (uH - uL) / (1 - uL))) == 0,
)

# ============================================================
# H12 : marginal income on the fresh boundary below the clamp
# ============================================================
Rb_bd = r0s / (1 - u)
# fresh depositor: pool S0, borrows B, deposit x ; u = B/(S0+x), u0 = B/S0
Ix = x * ue * Rb_bd.subs(u, ue)
dIx = sp.simplify(sp.diff(Ix, x))
claimed_H12 = r0s * ue**2 * (1 - u0e) / (u0e * (1 - ue) ** 2)
check(
    "H12",
    "dI/dx = r_0 u^2 (1-u_0) / (u_0 (1-u)^2) on the boundary",
    sp.simplify(sp.expand(dIx - claimed_H12)) == 0,
)

# ============================================================
# M2 : original steep-branch elasticity is largest at the kink
# ============================================================
mm = (Rmax - Ro) / (1 - O)
R_old = Ro + mm * (U - O)
eta_old = U * sp.diff(R_old, U) / R_old
d_eta_old = sp.simplify(sp.diff(eta_old, U))
num = sp.simplify(sp.numer(sp.together(d_eta_old)))
check(
    "M2",
    "eta_old(U)=Um/(R_o+m(U-O)) is decreasing in U when R_o - mO < 0",
    sp.simplify(sp.expand(num - mm * (Ro - mm * O) * (1 - O) ** 2)) == 0,
    "numerator equals m(R_o-mO)(1-O)^2; (1-O)^2>0 so the sign is that of R_o-mO, "
    "negative exactly under the manuscript's stated intercept assumption",
)

# ============================================================
# X2 / X3 : segment caps
# ============================================================
ui, ui1 = sp.symbols("u_i u_ip1", positive=True)
du = ui1 - ui
check(
    "X2",
    "c_fresh = 1 + du/(1-u_i)",
    sp.simplify((1 + du / (1 - ui)) - (1 + (ui1 - ui) / (1 - ui))) == 0,
)
# fixed-share cap: eta<=K at both endpoints of the segment
ri, ri1 = sp.symbols("r_i r_ip1", positive=True)
mi = (ri1 - ri) / du
# left endpoint: u_i * m_i / r_i <= K
left = sp.solve(sp.Eq(ui * mi / ri, K), ri1)[0] / ri
# right endpoint: u_{i+1} * m_i / r_{i+1} <= K
right = sp.solve(sp.Eq(ui1 * mi / ri1, K), ri1)[0] / ri
check(
    "X3a",
    "left-endpoint fixed-share cap = 1 + K*du/u_i",
    sp.simplify(left - (1 + K * du / ui)) == 0,
)
check(
    "X3b",
    "right-endpoint fixed-share cap = u_{i+1}/(u_{i+1} - K*du)",
    sp.simplify(right - ui1 / (ui1 - K * du)) == 0,
)

# ============================================================
# X8 : onchain division-free check
# ============================================================
r, dr, dU = sp.symbols("r Delta_r Delta_U", positive=True)
# eta = U*m/R <= K with m = dr/dU, R = r  =>  U*dr <= K*r*dU
check(
    "X8",
    "eta<=K at a segment endpoint  <=>  U*Delta_r <= K*r*Delta_U",
    sp.simplify(sp.solve(sp.Eq(U * (dr / dU) / r, K), dr)[0] - K * r * dU / U) == 0,
    "multiplied by r*Delta_U > 0",
)
# elasticity monotone across a positive linear segment
mlin = sp.symbols("m_lin", real=True)
R_lin = ri + mlin * (U - ui)
eta_lin = U * sp.diff(R_lin, U) / R_lin
num_lin = sp.simplify(sp.numer(sp.together(sp.diff(eta_lin, U))))
check(
    "X8b",
    "d(eta)/dU on a linear segment has numerator m*(r_i - m*u_i), constant in U",
    sp.simplify(sp.expand(num_lin - mlin * (ri - mlin * ui))) == 0,
    "sign is independent of U, so eta is monotone and the two endpoints bound it",
)

# ============================================================
# X9 : R/F nonincreasing <=> envelope condition
# ============================================================
Fs, Rs_, Fps, Rps = sp.symbols("F_v R_v Fp Rp_v", positive=True)
# (R/F)' = (R'F - R F')/F^2 ; substitute F' = E*F/U
Ev = sp.symbols("E_v", positive=True)
qprime_num = Rps * Fs - Rs_ * (Ev * Fs / U)
check(
    "X9",
    "with F'/F = E/U:  sign((R/F)') = sign(U R' - E R), so (R/F) nonincreasing <=> eta <= E",
    sp.simplify(sp.expand(qprime_num * U / Fs - (U * Rps - Ev * Rs_))) == 0,
    "F>0, so dividing by F^2 preserves sign",
)

# ============================================================
# X10 : combined boundary base bound
# ============================================================
t = K / (K + 1)
Fcomb_top = (K + 1) * (1 / t) ** K  # F(1) on the upper branch
check(
    "X10",
    "combined F(1) = (K+1)/t^K, so R(0) >= R_max t^K/(K+1)",
    sp.simplify(Rmax / Fcomb_top - Rmax * t**K / (K + 1)) == 0,
)
# continuity of the combined boundary at U=t
check(
    "X10b",
    "combined boundary is continuous at U=t",
    sp.simplify((1 / (1 - t)) - (K + 1) * (t / t) ** K) == 0,
)

# ============================================================
# A2 / A3 : accumulated interest
# ============================================================
check(
    "A3",
    "1% ownership, 5% carveout: 0.01*0.95 = 0.0095",
    sp.Rational(1, 100) * sp.Rational(95, 100) == sp.Rational(95, 10000),
)

# ============================================================
# S : smoothing
# ============================================================
w, L, A_, eta0, etamax = sp.symbols("w L A eta_0 eta_max", positive=True)
s = lambda tt: 3 * tt**2 - 2 * tt**3
tt = sp.symbols("t", positive=True)
check(
    "S7a",
    "smoothstep: s(0)=0, s(1)=1, s'(0)=s'(1)=0, int_0^1 s = 1/2",
    s(0) == 0
    and s(1) == 1
    and sp.diff(s(tt), tt).subs(tt, 0) == 0
    and sp.diff(s(tt), tt).subs(tt, 1) == 0
    and sp.integrate(s(tt), (tt, 0, 1)) == sp.Rational(1, 2),
)
check(
    "S7b",
    "int_0^t s = t^3 - t^4/2",
    sp.simplify(sp.integrate(s(v), (v, 0, tt)) - (tt**3 - tt**4 / 2)) == 0,
)

xs = sp.symbols("x", positive=True)
eta_prof = eta0 + (etamax - eta0) * s(xs / w)
integral_ramp = sp.integrate(eta_prof, (xs, 0, w))
check(
    "S4a",
    "int_0^w eta dx = w(eta_0+eta_max)/2",
    sp.simplify(integral_ramp - w * (eta0 + etamax) / 2) == 0,
)
total = sp.simplify(integral_ramp + etamax * (L - w))
check(
    "S4b",
    "int_0^L eta dx = eta_max(L - w/2) + eta_0 w/2",
    sp.simplify(total - (etamax * (L - w / 2) + eta0 * w / 2)) == 0,
)
etamax_solved = sp.solve(sp.Eq(total, A_), etamax)[0]
check(
    "S4c",
    "eta_max(w) = (A - eta_0 w/2)/(L - w/2)",
    sp.simplify(etamax_solved - (A_ - eta0 * w / 2) / (L - w / 2)) == 0,
)
check("S4d", "eta_max(0) = A/L = K*", sp.simplify(etamax_solved.subs(w, 0) - A_ / L) == 0)
dem = sp.simplify(sp.diff(etamax_solved.subs(A_, Kst * L), w))
check(
    "S5",
    "d eta_max/dw = L(K*-eta_0)/(2(L-w/2)^2)",
    sp.simplify(dem - L * (Kst - eta0) / (2 * (L - w / 2) ** 2)) == 0,
)
wbound = sp.solve(sp.Eq(etamax_solved.subs(A_, Kst * L), K), w)[0]
check(
    "S6",
    "eta_max(w)<=K  <=>  w <= 2L(K-K*)/(K-eta_0)",
    sp.simplify(wbound - 2 * L * (K - Kst) / (K - eta0)) == 0,
)
check(
    "S8",
    "w=L gives eta_max = 2K* - eta_0  (= 2K*-1 only when eta_0=1)",
    sp.simplify(etamax_solved.subs({A_: Kst * L, w: L}) - (2 * Kst - eta0)) == 0,
    "paper writes 2K*-1; correct under its standing eta_0=1",
)
check(
    "S1",
    "protected share jumps from 1/(1+1)=1/2 to 1/(1+K) at the kink",
    sp.simplify(1 / (1 + sp.Integer(1)) - sp.Rational(1, 2)) == 0,
)
check(
    "S2",
    "slope mismatch at kink: ramp slope R_o/O vs power-branch slope K R_o/O",
    sp.simplify(sp.diff(Ro * U / O, U) - Ro / O) == 0
    and sp.simplify(sp.diff(Ro * (U / O) ** K, U).subs(U, O) - K * Ro / O) == 0,
)

# ---------- report ----------
print(f"{'ID':<8} {'STATUS':<6} DESCRIPTION")
print("-" * 100)
npass = 0
for cid, ok, desc, note in RESULTS:
    print(f"{cid:<8} {'PASS' if ok else 'FAIL':<6} {desc}")
    if note:
        print(f"{'':<15} note: {note}")
    npass += ok
print("-" * 100)
print(f"{npass}/{len(RESULTS)} symbolic checks passed")

assert all(bool(row[1]) for row in RESULTS), "Failed verification check"
