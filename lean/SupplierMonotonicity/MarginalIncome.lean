import SupplierMonotonicity.Model

/-!
# Marginal supplier income

The derivative of supplier income with respect to a deposit, its sign condition and the safe
supplier share (paper, Section 4). The full-supplier limit of Appendix F is here too, because it
is the same derivative at `b = T`.

These are ordinary derivatives at smooth states. They say nothing about one-sided derivatives at
kinks, finite deposits (see `FiniteDeposits`) or rounded implementations.
-/

namespace SupplierMonotonicity

/-- `dU/dx = -U / (T + x)` along the deposit path. -/
theorem utilization_hasDerivAt (B T x : ℝ) (hT : T + x ≠ 0) :
    HasDerivAt (utilization B T) (-(B / (T + x)) / (T + x)) x := by
  have h := (hasDerivAt_const x B).div ((hasDerivAt_id x).const_add T) hT
  convert h using 1
  dsimp [utilization]
  field_simp
  ring

/-- The income derivative before factoring, from the product and chain rules. -/
theorem income_hasDerivAt_raw (R : ℝ → ℝ) (B T b x slope : ℝ)
    (hT : T + x ≠ 0) (hR : HasDerivAt R slope (utilization B T x)) :
    HasDerivAt (income R B T b)
      (utilization B T x * R (utilization B T x) -
        (b + x) * utilization B T x / (T + x) *
          (R (utilization B T x) + utilization B T x * slope)) x := by
  have hU := utilization_hasDerivAt B T x hT
  have h := (((hasDerivAt_id x).const_add b).mul hU).mul (hR.comp x hU)
  convert h using 1
  dsimp [income, utilization]
  ring

/-- The paper's factored form `dI/dx = U R(U) [1 - α (1 + η)]`. -/
theorem income_hasDerivAt (R : ℝ → ℝ) (B T b x slope : ℝ)
    (hT : T + x ≠ 0) (hR : HasDerivAt R slope (utilization B T x))
    (hr : R (utilization B T x) ≠ 0) :
    HasDerivAt (income R B T b)
      (utilization B T x * R (utilization B T x) *
        (1 - share T b x *
          (1 + elasticity (utilization B T x) (R (utilization B T x)) slope))) x := by
  convert income_hasDerivAt_raw R B T b x slope hT hR using 1
  dsimp [share, elasticity]
  field_simp

/-- `income_hasDerivAt` written with `deriv`, as in the paper. -/
theorem income_deriv (R : ℝ → ℝ) (B T b x : ℝ)
    (hT : T + x ≠ 0) (hR : DifferentiableAt ℝ R (utilization B T x))
    (hr : R (utilization B T x) ≠ 0) :
    deriv (income R B T b) x =
      utilization B T x * R (utilization B T x) *
        (1 - share T b x * (1 + elasticity (utilization B T x)
          (R (utilization B T x)) (deriv R (utilization B T x)))) :=
  (income_hasDerivAt R B T b x _ hT hR.hasDerivAt hr).deriv

/-- Income is nondecreasing in the deposit exactly when `α (1 + η) ≤ 1`. -/
theorem income_deriv_nonneg_iff (R : ℝ → ℝ) (B T b x : ℝ)
    (hB : 0 < B) (hT : 0 < T + x)
    (hR : DifferentiableAt ℝ R (utilization B T x))
    (hr : 0 < R (utilization B T x)) :
    0 ≤ deriv (income R B T b) x ↔
      share T b x * (1 + elasticity (utilization B T x)
        (R (utilization B T x)) (deriv R (utilization B T x))) ≤ 1 := by
  rw [income_deriv R B T b x hT.ne' hR hr.ne']
  have hU : 0 < utilization B T x := div_pos hB hT
  rw [mul_nonneg_iff_of_pos_left (mul_pos hU hr)]
  exact sub_nonneg

/-- The same condition read in reverse: income falls with the deposit exactly when
`α (1 + η) > 1`, so there a withdrawal (a negative deposit) raises income. -/
theorem income_deriv_neg_iff (R : ℝ → ℝ) (B T b x : ℝ)
    (hB : 0 < B) (hT : 0 < T + x)
    (hR : DifferentiableAt ℝ R (utilization B T x))
    (hr : 0 < R (utilization B T x)) :
    deriv (income R B T b) x < 0 ↔
      1 < share T b x * (1 + elasticity (utilization B T x)
        (R (utilization B T x)) (deriv R (utilization B T x))) := by
  rw [← not_le, ← not_le]
  exact not_congr (income_deriv_nonneg_iff R B T b x hB hT hR hr)

/-- Income is stationary in the deposit exactly when `α (1 + η) = 1`. An interior
income-maximizing balance, in particular the best withdrawal, satisfies this. -/
theorem income_deriv_eq_zero_iff (R : ℝ → ℝ) (B T b x : ℝ)
    (hB : 0 < B) (hT : 0 < T + x)
    (hR : DifferentiableAt ℝ R (utilization B T x))
    (hr : 0 < R (utilization B T x)) :
    deriv (income R B T b) x = 0 ↔
      share T b x * (1 + elasticity (utilization B T x)
        (R (utilization B T x)) (deriv R (utilization B T x))) = 1 := by
  have hU : 0 < utilization B T x := div_pos hB hT
  rw [income_deriv R B T b x hT.ne' hR hr.ne', mul_eq_zero,
    or_iff_right (mul_pos hU hr).ne', sub_eq_zero, eq_comm]

/-- The safe-share threshold `α ≤ 1 / (1 + η)`, including equality. -/
theorem safe_share_iff (alpha eta : ℝ) (heta : 0 ≤ eta) :
    alpha * (1 + eta) ≤ 1 ↔ alpha ≤ 1 / (1 + eta) := by
  have hd : 0 < 1 + eta := by linarith
  exact (le_div_iff₀ hd).symm

/-- A rate that is nondecreasing on `(0, 1)` has nonnegative elasticity there. -/
theorem elasticity_nonneg (R : ℝ → ℝ) (U : ℝ) (hU : U ∈ Set.Ioo (0 : ℝ) 1)
    (hmono : MonotoneOn R (Set.Ioo (0 : ℝ) 1)) (hr : 0 < R U) :
    0 ≤ elasticity U (R U) (deriv R U) := by
  have hd := hmono.derivWithin_nonneg (x := U)
  rw [derivWithin_of_mem_nhds (Ioo_mem_nhds hU.1 hU.2)] at hd
  exact div_nonneg (mul_nonneg hU.1.le hd) hr.le

/-- The sign condition as a safe share, with nonnegative elasticity derived from a
nondecreasing rate rather than assumed. -/
theorem income_deriv_safe_share_iff (R : ℝ → ℝ) (B T b x : ℝ)
    (hB : 0 < B) (hT : 0 < T + x) (hU : utilization B T x < 1)
    (hmono : MonotoneOn R (Set.Ioo (0 : ℝ) 1))
    (hR : DifferentiableAt ℝ R (utilization B T x))
    (hr : 0 < R (utilization B T x)) :
    0 ≤ deriv (income R B T b) x ↔
      share T b x ≤ 1 / (1 + elasticity (utilization B T x)
        (R (utilization B T x)) (deriv R (utilization B T x))) := by
  rw [income_deriv_nonneg_iff R B T b x hB hT hR hr]
  exact safe_share_iff _ _ (elasticity_nonneg R _ ⟨div_pos hB hT, hU⟩ hmono hr)

/-- A constant reserve carveout `f < 1` scales income and keeps the derivative's sign. -/
theorem constant_fee_sign (I : ℝ → ℝ) (d x f : ℝ) (hI : HasDerivAt I d x) (hf : f < 1) :
    HasDerivAt (fun y => (1 - f) * I y) ((1 - f) * d) x ∧ (0 ≤ (1 - f) * d ↔ 0 ≤ d) :=
  ⟨hI.const_mul (1 - f), mul_nonneg_iff_of_pos_left (sub_pos.mpr hf)⟩

/-- Elasticity is `d log R / d log U`: with `U = exp x`, the derivative of `log R(exp x)` is `η`. -/
theorem logarithmic_elasticity (R : ℝ → ℝ) (x slope : ℝ)
    (hR : HasDerivAt R slope (Real.exp x)) (hr : R (Real.exp x) ≠ 0) :
    HasDerivAt (fun x => Real.log (R (Real.exp x)))
      (elasticity (Real.exp x) (R (Real.exp x)) slope) x := by
  convert (hR.comp x (Real.hasDerivAt_exp x)).log hr using 1
  dsimp [elasticity]
  ring

/-- Scaling the whole rate curve by `c ≠ 0` leaves elasticity unchanged. -/
theorem scaled_elasticity (u r m c : ℝ) (hc : c ≠ 0) :
    elasticity u (c * r) (c * m) = elasticity u r m := by
  dsimp [elasticity]
  field_simp

/-- Full supplier limit (Appendix F): with `b = T`, `dI/dx = -U² R'(U)`. -/
theorem full_supplier_deriv (R : ℝ → ℝ) (B T x slope : ℝ)
    (hT : T + x ≠ 0) (hR : HasDerivAt R slope (utilization B T x)) :
    HasDerivAt (income R B T T) (-(utilization B T x) ^ 2 * slope) x := by
  convert income_hasDerivAt_raw R B T T x slope hT hR using 1
  dsimp [utilization]
  field_simp
  ring

end SupplierMonotonicity
