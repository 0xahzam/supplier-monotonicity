# Manuscript-to-Lean correspondence

The reference is `../build/main.tex`; its hash is recorded in `evidence/verification.json`.
[COVERAGE.md](COVERAGE.md) maps all displayed equations and named statements.
Each component result is stated once, and `Main.lean` restates the named results in the
paper's terms. Many declarations are supporting lemmas, and one paper claim may rest on
several of them.

## Shared notation

| Paper | Formal representation |
|---|---|
| Resulting supply T | `T + x`, with T the initial amount |
| Resulting balance b | `b + x`, with b the initial balance |
| Deposit | Real variable `x` |
| Fixed borrowings B | Parameter `B`, independent of x |
| Utilization U | `utilization B T x = B/(T+x)` |
| Supplier share alpha | `share T b x = (b+x)/(T+x)` |
| Rate R_b | Real function `R` |
| Elasticity | `elasticity u r m = u*m/r`, using r=R(u), m=R'(u) |
| Log-utilization coordinate | `x=log(u/O)` in construction proofs; this x is not a deposit |
| Worst-case elasticity | Supremum of the image of the interval, in `Smoothing.lean` |

The core derivatives are ordinary derivatives inside smooth segments. Nonzero
denominators suffice for the identities; positive borrowing, supply and rate are
required for the sign equivalence. Physical balance bounds are not needed for
those algebraic results, so their omission proves a more general identity.

## Modules and limits

Modules live in `../lean/SupplierMonotonicity/` and follow the paper's sections.
`Main.lean` restates the named results in the paper's terms; the table in
`../lean/README.md` gives the status of each.

**Model.lean.** Definitions only: `utilization`, `income`, `share`, `elasticity` and `kStar`.

**MarginalIncome.lean.** Utilization and income derivatives along the actual deposit path,
the sign and safe-share equivalences, the reversed sign condition for withdrawals and the
stationary point `α(1+η) = 1`, fee scaling, the logarithmic form of elasticity and the
full-supplier derivative. Nonnegative elasticity is derived from monotonicity of R on `(0,1)`,
not assumed in the final safe-share result.

**FiniteDeposits.lean.** The segment mean-value argument, gluing over an arbitrary finite
partition, ownership monotonicity, `finite_supplier_deposit` and `withdrawal_raises_income`. The last uses the actual income
function, continuity on each closed piece and protection on each open piece. It does not prove
a countably infinite knot-crossing extension or the one-sided derivative at a knot.

**AdmissibleFamily.lean.** Profile/envelope equivalence, protection of every smaller share,
the smooth implication from an envelope to an antitone normalized rate and its multiplicative
bound, and `reconstructedRate eta r x = r exp(integral_0^x eta)`. For a globally continuous eta
the construction is positive, C1 in log coordinates, hits its endpoint value and has
utilization elasticity exactly eta. The general construction for profiles that are only
continuous on a compact interval is not formalized, and Theorem 2 in its AC/a.e. form is open.

**FixedShare.lean.** The logarithmic rate FTC identity and log budget integral, the smooth
log-growth bound and the endpoint bound for continuous rates differentiable on the open interval
with a pointwise elasticity ceiling. This is a smooth subclass, not the paper's
AC/essential-supremum claim. Real powers are connected to `exp(K log(u/O))` under positive inputs.

**FreshDepositor.lean.** Fresh share, the fresh-path condition, the worst start `u0 = 1`, the
envelope `u/(1-u)`, hyperbolic boundary derivative and elasticity, and the piecewise linear
segment and adjacent-ratio conditions. Boundary uniqueness needs the integrated-family argument.

**Repairs.lean.** Envelope crossing and combination, knot-rate caps, and the floor, raise and
lower recursions. The backward recurrence is indexed in reverse: index 0 is the top knot.
Optimality is proved inductively against any feasible competitor. The recursions use finite
positive real caps; infinite caps are not encoded as division by infinity.
`raise_step_feasible` proves the local feasibility step, not every global implementation detail.

Analytic order bounds use `sInf`/`sSup` on the specified image sets, with explicit nonemptiness
and boundedness assumptions. They prove extremal order properties, not all continuity,
positivity or regularity facts required for full admissibility. The zero-base, E=0 scope
example explains the positive-base qualification now in the paper.

**AccumulatedInterest.lean.** Accumulated-income comparison under prescribed integrable
histories, and the supplier transfer identity.

**Onchain.lean.** The division-free endpoint form, endpoint sufficiency on a linear segment,
and elasticity monotonicity on a segment when `m(r_i - m u_i)` is nonnegative. The opposite
sign is covered by `fixed_linear_endpoint_suffices`, not by the monotonicity lemma. These are
continuous-arithmetic results, not rounded transactions.

**Smoothing.lean.** `continuous_rate_supremum_strict` proves the strict supremum result with a
continuous quotient R'/R, the starting elasticity inequality and the endpoint budget.
`continuous_quotient_of_C1_data` derives quotient continuity from a continuous rate derivative
and positive rate. `smoothEta` is the actual ramp/plateau function. Its continuity, exact
integral, plateau uniqueness, derivative and full pointwise ceiling/width equivalence are
checked for positive width `w <= L`. Separate algebra handles the printed w=0 limiting plateau,
which is not claimed to match the starting elasticity.

For a closed-interval C1 branch, R' at O denotes its branch derivative. The formal
representation uses an ambient differentiable extension when speaking of `deriv` at endpoints.
The paper's assembled curve may have a different derivative on the other side before smoothing,
and no equality with the other branch is assumed. Composed C1/C2 join assertions remain to be
formally assembled.

## Assumptions carried by the proofs

- Positivity is required before cancelling rate or utilization factors.
- A fixed borrowing parameter is not an endogenous borrowing path.
- Integrability is stated in accumulated-income comparisons and FTC lemmas.
- Positive, increasing knot coordinates and left rates are required by ratio forms.
- Nondecreasing rates give nonnegative derivatives only where the derivative
  exists. No proof uses a derivative at a kink.
- Lean totalizes division, but physical conclusions retain explicit nonzero or
  positive denominator assumptions. The fresh-share identity keeps nonzero
  initial supply even though the algebraic proof term does not need it.
- `zero_base_flat_minorant` and `no_positive_flat_minorant` are proved counterexamples.
  They show why the paper assumes a positive base rate.
