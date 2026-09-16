# Manuscript-to-Lean correspondence

The reference is `../paper.tex`; its current hash is recorded in `evidence/verification.json`.
[COVERAGE.md](COVERAGE.md) maps all displayed equations and named statements.
This mapping is a manual mathematical review, not a kernel-checked translation of LaTeX.
Each result is stated once. Declaration counts are not counts of independently
verified paper claims: many declarations are supporting lemmas, and a single paper
claim may rest on several of them.

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
| Worst-case elasticity | Supremum of the image of the interval in Endpoint.lean |

The core derivatives are ordinary derivatives inside smooth segments. Nonzero
denominators suffice for the identities; positive borrowing, supply and rate are
required for the sign equivalence. Physical balance bounds are not needed for
those algebraic results, so their omission proves a more general identity.

## Modules and limits

**Core.lean (12 declarations).** Foundational identities: actual utilization
and income derivatives, sign and threshold equivalences, fee scaling, envelope
algebra, and fresh-share/path identities. Nonnegative elasticity is derived from
monotonicity of R on `(0,1)`, not assumed silently in the final safe-share result.

**Extended.lean (31 declarations).** Segment mean-value argument, arbitrary finite
partition gluing, ownership monotonicity, every-smaller-share equivalence, worst
fresh start, linear cap algebra, local recursion steps, smoothing algebra,
full-supplier derivative, logarithmic elasticity, integral comparison and the
abstract continuous-average overshoot argument. `endpoint_budget_bound` assumes
the integral budget; it alone is not the endpoint theorem.

**Boundaries.lean (18 declarations).** The endpoint bound is proved for continuous
rates differentiable on the open interval, with a pointwise elasticity ceiling.
This is explicitly a smooth subclass, not the paper's AC/essential-supremum
claim. Real powers are connected to `exp(K log(u/O))` under positive inputs.
Hyperbolic derivatives and elasticity are exact; boundary uniqueness still needs
the integrated-family argument. Smoothstep polynomial and primitive facts are
proved, but individual branch derivatives alone do not prove C2 across all joins.

**Repairs.lean (16 declarations).** `finite_supplier_deposit` uses the actual income
function and states continuity on each closed partition piece and protection on
each open piece. The partition is arbitrary but finite. It does not prove a
countably infinite knot-crossing extension or the one-sided derivative at a knot.

The backward recurrence is indexed in reverse: index 0 is the top knot.
Optimality is proved inductively against any feasible competitor. The recurrence
theorems use finite positive real caps; infinite caps are not encoded as division
by infinity. `raise_step_feasible` proves the local feasibility step, not every
global implementation detail.

Analytic order bounds use `sInf`/`sSup` on the specified image sets. Nonemptiness
and boundedness assumptions are explicit. These prove extremal order properties,
not all continuity/positivity/regularity facts required for full admissibility.
The zero-base, E=0 scope example explains the positive-base qualification now in the paper.

**Smoothing.lean (18 declarations).** `smoothEta` is the actual ramp/plateau
function. Its continuity, exact integral, plateau uniqueness, derivative and
full pointwise ceiling/width equivalence are checked. Width w is positive for the
actual profile, with `w<=L`. Separate algebra handles the printed w=0 limiting
plateau. The w=0 profile is not claimed to match the starting elasticity.

`reconstructedRate eta r x = r exp(integral_0^x eta)` constructs the rate in log
coordinates. A globally continuous eta is used here; the explicit smoothstep
profile has that property. This does not silently certify the paper's general
construction for arbitrary profiles only continuous on a compact interval.
Positive anchor, C1 regularity in log coordinates, endpoint value, utilization
derivative and exact elasticity are checked. Some composed C1/C2 join assertions
remain to be formally assembled.

**Endpoint.lean (5 declarations).** The logarithmic rate FTC identity is proved
assuming continuity, interior differentiability and integrability of R'/R.
`continuous_rate_supremum_strict` establishes the displayed strict supremum result
with a continuous quotient R'/R, the starting elasticity inequality and endpoint
budget. `continuous_quotient_of_C1_data` derives quotient continuity from a
continuous rate derivative and positive rate.

For a closed-interval C1 branch, R' at O denotes its branch derivative. The formal
representation uses an ambient differentiable extension when speaking of `deriv`
at endpoints. The paper's assembled curve may have a different derivative on the
other side before smoothing. No equality with the other branch is silently assumed.
The full existence half of the named C1 theorem still requires assembly of the
constructed branch, regularity and endpoint/join constraints.

## Proof assumptions that must not disappear in reporting

- Positivity is required before cancelling rate or utilization factors.
- A fixed borrowing parameter is not an endogenous borrowing path.
- Integrability is stated in accumulated-income comparisons and FTC lemmas.
- Positive, increasing knot coordinates and left rates are required by ratio forms.
- Nondecreasing rates imply nonnegative derivatives only where the relevant
  derivative is defined; the proof never relies on a fake derivative at a kink.
- Lean totalizes division, but physical conclusions retain explicit nonzero or
  positive denominator assumptions. The fresh-share identity keeps nonzero
  initial supply even though the algebraic proof term does not need it.
- Verified negative scope tests are not “failed proofs.” They are proved
  counterexamples/nonexistence statements, separately identified in the report.

No theorem hypotheses were strengthened without documenting the resulting
limited coverage. The AC/a.e. theorem remains open, rather than being relabelled
as established by the smooth proof.

## Supporting results in `Envelopes.lean`

`Envelopes.lean` contributes five supporting results:

| Canonical theorem | Contribution and assumptions |
|---|---|
| `normalized_rate_antitone` | Derivative inequality implies antitone R/F on a closed interval; F is positive, both functions continuous and interior differentiable. |
| `normalized_rate_bound` | Reads the multiplicative rate bound from antitonicity. |
| `running_inf_antitone` | Actual running infimum is antitone; nonemptiness and lower boundedness are explicit. |
| `segment_fresh_ratio_monotone` | R/(1-U) is increasing on a positive, nondecreasing affine segment below U=1. |
| `segment_elasticity_monotone` | Elasticity increases when m(r_i-mu_i) is nonnegative. The opposite sign is not silently covered by this lemma; the endpoint sufficiency proof in Extended covers the constraint directly. |

Deposit identities, endpoint integrals, continuous-average arguments and pointwise
order inequalities are each stated once. Two zero-base scope lemmas record the
degenerate case in which the running-infimum construction leaves the positive rate
class. None of these supporting results discharges an AC/a.e. obligation; the open
items in COVERAGE.md remain open.
