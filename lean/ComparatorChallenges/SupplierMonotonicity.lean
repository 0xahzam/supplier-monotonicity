import Mathlib

/-!
# Comparator challenge: Depositing More Should Not Earn Less

The paper's main results as bare statements. Every proof here is `sorry`; the proofs live in
`SupplierMonotonicity.Main`. [Comparator](https://github.com/leanprover/comparator) checks that
the solution module proves exactly these statements using only the standard axioms.

The definitions below must stay identical to `SupplierMonotonicity.Model` and
`SupplierMonotonicity.Smoothing`. `verification/check.py` compares them textually.
-/

namespace SupplierMonotonicity

noncomputable section

/-- Utilization after depositing `x`: `U = B / (T + x)`. -/
def utilization (B T x : ℝ) : ℝ := B / (T + x)

/-- Supplier income rate after depositing `x`: `I = (b + x) · U · R(U)`. -/
def income (R : ℝ → ℝ) (B T b x : ℝ) : ℝ :=
  (b + x) * utilization B T x * R (utilization B T x)

/-- Supplier share of the pool after depositing `x`: `α = (b + x) / (T + x)`. -/
def share (T b x : ℝ) : ℝ := (b + x) / (T + x)

/-- Elasticity of the rate at utilization `U`, given the rate `rate = R(U)` and the slope
`slope = R'(U)`: `η = U · R'(U) / R(U)`. -/
def elasticity (U rate slope : ℝ) : ℝ := U * slope / rate

/-- The endpoint elasticity `K* = log (R_max / R_o) / log (1 / O)` of a curve from `(O, R_o)` to
`(1, R_max)` (paper, Section 6.1). -/
def kStar (O Ro Rmax : ℝ) : ℝ := Real.log (Rmax / Ro) / Real.log (1 / O)

/-- Elasticity in the log coordinate `x`: a smoothstep ramp from `e` to `M` over `[0, w]`,
then the plateau `M`. -/
noncomputable def smoothEta (e M w x : ℝ) : ℝ :=
  if x ≤ w then e + (M - e) * (3 * (x / w) ^ 2 - 2 * (x / w) ^ 3) else M

end

open Set MeasureTheory

/-- **Proposition 1 (marginal supplier income).** With borrowings fixed,
`dI/dx = U R(U) [1 - α (1 + η)]`, and income is nondecreasing in the deposit exactly when
`α (1 + η) ≤ 1`. -/
theorem marginal_supplier_income (R : ℝ → ℝ) (B T b x : ℝ) (hB : 0 < B) (hT : 0 < T + x)
    (hR : DifferentiableAt ℝ R (utilization B T x)) (hr : 0 < R (utilization B T x)) :
    deriv (income R B T b) x =
        utilization B T x * R (utilization B T x) *
          (1 - share T b x * (1 + elasticity (utilization B T x) (R (utilization B T x))
            (deriv R (utilization B T x)))) ∧
      (0 ≤ deriv (income R B T b) x ↔
        share T b x * (1 + elasticity (utilization B T x) (R (utilization B T x))
          (deriv R (utilization B T x))) ≤ 1) := by
  sorry

/-- **Theorem 3 (endpoint impossibility bound), smooth case.** A positive rate curve from
`(O, R O)` to `(1, R 1)`, continuous on `[O, 1]` and differentiable inside, with elasticity at
most `K` inside, has `K* ≤ K`.

The paper states this for absolutely continuous curves and the essential supremum; that
version is not formalized. -/
theorem endpoint_impossibility_bound (R : ℝ → ℝ) (O K : ℝ) (hO : 0 < O) (hO1 : O < 1)
    (hc : ContinuousOn R (Icc O 1)) (hr : ∀ u ∈ Icc O 1, 0 < R u)
    (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (he : ∀ u ∈ Ioo O 1, elasticity u (R u) (deriv R u) ≤ K) :
    kStar O (R O) (R 1) ≤ K := by
  sorry

/-- **Theorem 3, tightness.** The power law `R_o (u / O) ^ K*` runs from `(O, R_o)` to
`(1, R_max)` with elasticity exactly `K*` at every `u > 0`. -/
theorem endpoint_bound_tight (O Ro Rmax : ℝ) (hO : 0 < O) (hO1 : O < 1) (hRo : 0 < Ro)
    (hRmax : 0 < Rmax) :
    Ro * Real.exp (kStar O Ro Rmax * Real.log (O / O)) = Ro ∧
      Ro * Real.exp (kStar O Ro Rmax * Real.log (1 / O)) = Rmax ∧
      ∀ u, 0 < u → elasticity u (Ro * Real.exp (kStar O Ro Rmax * Real.log (u / O)))
        (deriv (fun v => Ro * Real.exp (kStar O Ro Rmax * Real.log (v / O))) u) =
          kStar O Ro Rmax := by
  sorry

/-- **Theorem 4 (global fresh depositor condition).** At utilization `0 < u < 1`, with rate
`r > 0` and slope `m ≥ 0`, protecting a fresh depositor from every start `u₀ ∈ [u, 1]` is the
envelope `η ≤ u / (1 - u)`, which is the design rule `(1 - u) R' ≤ R`.

A fresh depositor's share is `1 - u / u₀` (`fresh_share`). -/
theorem global_fresh_depositor (u r m : ℝ) (hu : 0 < u) (hu1 : u < 1) (hr : 0 < r)
    (hm : 0 ≤ m) :
    ((∀ u0 ∈ Icc u 1, (1 - u / u0) * (1 + elasticity u r m) ≤ 1) ↔
        elasticity u r m ≤ u / (1 - u)) ∧
      (elasticity u r m ≤ u / (1 - u) ↔ (1 - u) * m ≤ r) := by
  sorry

/-- **Theorem 4, boundary curve.** `R(U) = c / (1 - U)`, with `c = R(U_a) (1 - U_a)`, has
elasticity exactly `U / (1 - U)`. -/
theorem fresh_boundary_curve (c U : ℝ) (hc : c ≠ 0) (hU : U ≠ 1) :
    elasticity U (c / (1 - U)) (deriv (fun v => c / (1 - v)) U) = U / (1 - U) := by
  sorry

/-- **Theorem 5 (`C¹` makes `K*` unattainable).** A positive curve on `[O, 1]` with continuous
derivative whose elasticity starts below `K*` has `sup η > K*`.

`deriv R O` is the derivative of an ambient extension of `R` at the left endpoint. -/
theorem c1_makes_kstar_unattainable (R : ℝ → ℝ) (O : ℝ) (hO : 0 < O) (hO1 : O < 1)
    (hc : ContinuousOn R (Icc O 1)) (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (hc' : ContinuousOn (deriv R) (Icc O 1)) (hp : ∀ u ∈ Icc O 1, 0 < R u)
    (hstart : elasticity O (R O) (deriv R O) < kStar O (R O) (R 1)) :
    kStar O (R O) (R 1) < sSup ((fun u => elasticity u (R u) (deriv R u)) '' Icc O 1) := by
  sorry

/-- **Theorem 5, feasibility.** In the log coordinate `x ∈ [0, L]`, for every ceiling `K > K*`
there is a positive ramp width whose smoothstep profile meets the endpoint budget
`∫₀ᴸ η = K* L` and stays below `K`. `reconstructedRate` turns this profile into a positive
`C¹` rate curve with exactly this elasticity. -/
theorem c1_ceiling_feasible (L e Kstar K : ℝ) (hL : 0 < L) (he : e < Kstar) (hK : Kstar < K) :
    ∃ w, 0 < w ∧ w ≤ L ∧
      (∫ x in (0 : ℝ)..L, smoothEta e ((Kstar * L - e * w / 2) / (L - w / 2)) w x) =
        Kstar * L ∧
      ∀ x ∈ Icc (0 : ℝ) L, smoothEta e ((Kstar * L - e * w / 2) / (L - w / 2)) w x ≤ K := by
  sorry

/-- **Proposition 6 (the cost of smoothing).** In the log coordinate `x ∈ [0, L]` with budget
`A = K* L` and starting elasticity `e < K*`:

1. for each width `0 < w ≤ L` the budget fixes the plateau
   `η_max(w) = (A - e w / 2) / (L - w / 2)`;
2. `η_max(0) = K*`, the nonsmooth limit;
3. `η_max` has derivative `L (K* - e) / (2 (L - w / 2)²) > 0`;
4. `η_max(w) > K*` for every `w > 0`;
5. the profile respects a ceiling `K > e` exactly when `w ≤ 2 L (K - K*) / (K - e)`.

The paper allows `w = 0` in the last item; here it is stated for `w > 0`. -/
theorem cost_of_smoothing (L e Kstar : ℝ) (hL : 0 < L) (he : e < Kstar) :
    (∀ w M, 0 < w → w ≤ L →
      ((∫ x in (0 : ℝ)..L, smoothEta e M w x) = Kstar * L ↔
        M = (Kstar * L - e * w / 2) / (L - w / 2))) ∧
    (Kstar * L - e * 0 / 2) / (L - 0 / 2) = Kstar ∧
    (∀ w, w ≤ L →
      HasDerivAt (fun w : ℝ => (Kstar * L - e * w / 2) / (L - w / 2))
        (L * (Kstar - e) / (2 * (L - w / 2) ^ 2)) w ∧
      0 < L * (Kstar - e) / (2 * (L - w / 2) ^ 2)) ∧
    (∀ w, 0 < w → w ≤ L → Kstar < (Kstar * L - e * w / 2) / (L - w / 2)) ∧
    (∀ w K, 0 < w → w ≤ L → e < K →
      ((∀ x ∈ Icc (0 : ℝ) L, smoothEta e ((Kstar * L - e * w / 2) / (L - w / 2)) w x ≤ K) ↔
        w ≤ 2 * L * (K - Kstar) / (K - e))) := by
  sorry

end SupplierMonotonicity
