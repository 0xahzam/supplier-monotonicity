import SupplierMonotonicity.MarginalIncome
import SupplierMonotonicity.FixedShare
import SupplierMonotonicity.FreshDepositor
import SupplierMonotonicity.Smoothing

/-!
# Main results

The paper's named results, stated in the paper's terms and proved from the component modules.
`ComparatorChallenges/SupplierMonotonicity.lean` repeats these statements with `sorry` proofs, so
a reader can review what is claimed without reading the proofs.

`lean/README.md` maps each paper result to these theorems and records what is still open.
-/

namespace SupplierMonotonicity

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
          (deriv R (utilization B T x))) ≤ 1) :=
  ⟨income_deriv R B T b x hT.ne' hR hr.ne', income_deriv_nonneg_iff R B T b x hB hT hR hr⟩

/-- **Theorem 3 (endpoint impossibility bound), smooth case.** A positive rate curve from
`(O, R O)` to `(1, R 1)`, continuous on `[O, 1]` and differentiable inside, with elasticity at
most `K` inside, has `K* ≤ K`.

The paper states this for absolutely continuous curves and the essential supremum; that
version is not formalized. -/
theorem endpoint_impossibility_bound (R : ℝ → ℝ) (O K : ℝ) (hO : 0 < O) (hO1 : O < 1)
    (hc : ContinuousOn R (Icc O 1)) (hr : ∀ u ∈ Icc O 1, 0 < R u)
    (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (he : ∀ u ∈ Ioo O 1, elasticity u (R u) (deriv R u) ≤ K) :
    kStar O (R O) (R 1) ≤ K :=
  smooth_endpoint_bound R O K hO hO1 hc hr hd he

/-- **Theorem 3, tightness.** The power law `R_o (u / O) ^ K*` runs from `(O, R_o)` to
`(1, R_max)` with elasticity exactly `K*` at every `u > 0`. -/
theorem endpoint_bound_tight (O Ro Rmax : ℝ) (hO : 0 < O) (hO1 : O < 1) (hRo : 0 < Ro)
    (hRmax : 0 < Rmax) :
    Ro * Real.exp (kStar O Ro Rmax * Real.log (O / O)) = Ro ∧
      Ro * Real.exp (kStar O Ro Rmax * Real.log (1 / O)) = Rmax ∧
      ∀ u, 0 < u → elasticity u (Ro * Real.exp (kStar O Ro Rmax * Real.log (u / O)))
        (deriv (fun v => Ro * Real.exp (kStar O Ro Rmax * Real.log (v / O))) u) =
          kStar O Ro Rmax := by
  refine ⟨by simp [div_self hO.ne'], power_hits_top O Ro Rmax hO hO1 hRo hRmax, fun u hu => ?_⟩
  exact power_boundary_elasticity O Ro _ u hu hO hRo

/-- **Theorem 4 (global fresh depositor condition).** At utilization `0 < u < 1`, with rate
`r > 0` and slope `m ≥ 0`, protecting a fresh depositor from every start `u₀ ∈ [u, 1]` is the
envelope `η ≤ u / (1 - u)`, which is the design rule `(1 - u) R' ≤ R`.

A fresh depositor's share is `1 - u / u₀` (`fresh_share`). -/
theorem global_fresh_depositor (u r m : ℝ) (hu : 0 < u) (hu1 : u < 1) (hr : 0 < r)
    (hm : 0 ≤ m) :
    ((∀ u0 ∈ Icc u 1, (1 - u / u0) * (1 + elasticity u r m) ≤ 1) ↔
        elasticity u r m ≤ u / (1 - u)) ∧
      (elasticity u r m ≤ u / (1 - u) ↔ (1 - u) * m ≤ r) := by
  have hpath : (∀ u0 ∈ Icc u 1, (1 - u / u0) * (1 + elasticity u r m) ≤ 1) ↔
      ∀ u0 ∈ Icc u 1, (u0 - u) * m ≤ r :=
    forall₂_congr fun u0 h0 => fresh_path_iff u u0 r m hu (lt_of_lt_of_le hu h0.1) hr
  constructor
  · rw [hpath, fresh_all_starts_iff u r m hu1.le hm, fresh_envelope_iff u r m hu hu1 hr]
  · exact fresh_envelope_iff u r m hu hu1 hr

/-- **Theorem 4, boundary curve.** `R(U) = c / (1 - U)`, with `c = R(U_a) (1 - U_a)`, has
elasticity exactly `U / (1 - U)`. -/
theorem fresh_boundary_curve (c U : ℝ) (hc : c ≠ 0) (hU : U ≠ 1) :
    elasticity U (c / (1 - U)) (deriv (fun v => c / (1 - v)) U) = U / (1 - U) := by
  rw [(hyperbolic_boundary_derivative c U hU).deriv]
  exact hyperbolic_boundary_elasticity c U hc hU

/-- **Theorem 5 (`C¹` makes `K*` unattainable).** A positive curve on `[O, 1]` with continuous
derivative whose elasticity starts below `K*` has `sup η > K*`.

`deriv R O` is the derivative of an ambient extension of `R` at the left endpoint. -/
theorem c1_makes_kstar_unattainable (R : ℝ → ℝ) (O : ℝ) (hO : 0 < O) (hO1 : O < 1)
    (hc : ContinuousOn R (Icc O 1)) (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (hc' : ContinuousOn (deriv R) (Icc O 1)) (hp : ∀ u ∈ Icc O 1, 0 < R u)
    (hstart : elasticity O (R O) (deriv R O) < kStar O (R O) (R 1)) :
    kStar O (R O) (R 1) < sSup ((fun u => elasticity u (R u) (deriv R u)) '' Icc O 1) := by
  have hlog : Real.log (1 / O) ≠ 0 := (Real.log_pos ((one_lt_div hO).mpr hO1)).ne'
  exact continuous_rate_supremum_strict R O _ hO hO1 hc hp hd
    (continuous_quotient_of_C1_data R O 1 hc hc' hp) hstart (div_mul_cancel₀ _ hlog).symm

/-- **Theorem 5, feasibility.** In the log coordinate `x ∈ [0, L]`, for every ceiling `K > K*`
there is a positive ramp width whose smoothstep profile meets the endpoint budget
`∫₀ᴸ η = K* L` and stays below `K`. `reconstructedRate` turns this profile into a positive
`C¹` rate curve with exactly this elasticity. -/
theorem c1_ceiling_feasible (L e Kstar K : ℝ) (hL : 0 < L) (he : e < Kstar) (hK : Kstar < K) :
    ∃ w, 0 < w ∧ w ≤ L ∧
      (∫ x in (0 : ℝ)..L, smoothEta e ((Kstar * L - e * w / 2) / (L - w / 2)) w x) =
        Kstar * L ∧
      ∀ x ∈ Icc (0 : ℝ) L, smoothEta e ((Kstar * L - e * w / 2) / (L - w / 2)) w x ≤ K := by
  obtain ⟨w, hw, hwL, hplateau⟩ := smoothing_width_exists L e Kstar K hL he hK
  have heM := (lt_trans he (smooth_plateau_above_average w e L Kstar hL hw hwL he)).le
  exact ⟨w, hw, hwL, (smoothing_endpoint_unique e _ w L _ hw hwL).mpr rfl,
    (smoothEta_ceiling_iff e _ w L K hw hwL heM).mpr hplateau⟩

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
  refine ⟨fun w M hw hwL => smoothing_endpoint_unique e M w L _ hw hwL,
    smooth_zero_width L e Kstar hL.ne', fun w hwL => ?_,
    fun w hw hwL => smooth_plateau_above_average w e L Kstar hL hw hwL he,
    fun w K hw hwL hK => smoothing_ceiling_width_iff e w L Kstar K hL hw hwL he hK⟩
  have hd : L - w / 2 ≠ 0 := (by linarith : 0 < L - w / 2).ne'
  exact ⟨smooth_plateau_derivative L e Kstar w hd,
    div_pos (mul_pos hL (sub_pos.mpr he)) (mul_pos (by norm_num) (sq_pos_of_ne_zero hd))⟩

end SupplierMonotonicity
