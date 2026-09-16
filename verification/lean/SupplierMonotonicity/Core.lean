import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Smooth-state supplier-income identities and protection conditions.

`T` and `b` are initial supply and supplier balance; `x` is the deposit.
The paper's resulting-state `T` and `b` are therefore `T + x` and `b + x`.
`B` is constant as `x` varies. Rates and amounts are real numbers.

These are ordinary derivatives at smooth states, not one-sided derivatives
at knots, finite-deposit results, or assertions about rounded implementations.
-/

namespace SupplierMonotonicity

noncomputable section

def utilization (B T x : ℝ) : ℝ := B / (T + x)

def income (R : ℝ → ℝ) (B T b x : ℝ) : ℝ :=
  (b + x) * utilization B T x * R (utilization B T x)

def share (T b x : ℝ) : ℝ := (b + x) / (T + x)

def elasticity (U rate slope : ℝ) : ℝ := U * slope / rate

-- C01: The utilization derivative, derived from the actual deposit path.
theorem utilization_hasDerivAt (B T x : ℝ) (hT : T + x ≠ 0) :
    HasDerivAt (utilization B T) (-(B / (T + x)) / (T + x)) x := by
  have h := (hasDerivAt_const x B).div
    ((hasDerivAt_id x).const_add T) hT
  convert h using 1
  dsimp [utilization]
  field_simp
  ring

-- C02: Product and chain rules give the unfactored income derivative.
theorem income_hasDerivAt_raw (R : ℝ → ℝ) (B T b x slope : ℝ)
    (hT : T + x ≠ 0)
    (hR : HasDerivAt R slope (utilization B T x)) :
    HasDerivAt (income R B T b)
      (utilization B T x * R (utilization B T x) -
        (b + x) * utilization B T x / (T + x) *
          (R (utilization B T x) + utilization B T x * slope)) x := by
  have hU := utilization_hasDerivAt B T x hT
  have h := (((hasDerivAt_id x).const_add b).mul hU).mul (hR.comp x hU)
  convert h using 1
  dsimp [income, utilization]
  ring

-- C03: The manuscript's factored derivative, with explicit nonzero rate.
theorem income_hasDerivAt (R : ℝ → ℝ) (B T b x slope : ℝ)
    (hT : T + x ≠ 0)
    (hR : HasDerivAt R slope (utilization B T x))
    (hr : R (utilization B T x) ≠ 0) :
    HasDerivAt (income R B T b)
      (utilization B T x * R (utilization B T x) *
        (1 - share T b x *
          (1 + elasticity (utilization B T x) (R (utilization B T x)) slope))) x := by
  convert income_hasDerivAt_raw R B T b x slope hT hR using 1
  dsimp [share, elasticity]
  field_simp

-- C04: Ordinary derivative notation, exactly as used in the paper.
theorem income_deriv (R : ℝ → ℝ) (B T b x : ℝ)
    (hT : T + x ≠ 0)
    (hR : DifferentiableAt ℝ R (utilization B T x))
    (hr : R (utilization B T x) ≠ 0) :
    deriv (income R B T b) x =
      utilization B T x * R (utilization B T x) *
        (1 - share T b x * (1 + elasticity (utilization B T x)
          (R (utilization B T x)) (deriv R (utilization B T x)))) :=
  (income_hasDerivAt R B T b x _ hT hR.hasDerivAt hr).deriv

-- C05: Both directions of the central sign equivalence.
theorem income_deriv_nonneg_iff (R : ℝ → ℝ) (B T b x : ℝ)
    (hB : 0 < B) (hT : 0 < T + x)
    (hR : DifferentiableAt ℝ R (utilization B T x))
    (hr : 0 < R (utilization B T x)) :
    0 ≤ deriv (income R B T b) x ↔
      share T b x * (1 + elasticity (utilization B T x)
        (R (utilization B T x)) (deriv R (utilization B T x))) ≤ 1 := by
  rw [income_deriv R B T b x (ne_of_gt hT) hR (ne_of_gt hr)]
  have hU : 0 < utilization B T x := div_pos hB hT
  rw [mul_nonneg_iff_of_pos_left (mul_pos hU hr)]
  exact sub_nonneg

-- C06: The exact safe-share threshold, including equality at the boundary.
theorem safe_share_iff (alpha eta : ℝ) (heta : 0 ≤ eta) :
    alpha * (1 + eta) ≤ 1 ↔ alpha ≤ 1 / (1 + eta) := by
  have hd : 0 < 1 + eta := by linarith
  exact (le_div_iff₀ hd).symm

-- C07: The protection-profile constraint and elasticity envelope are equivalent.
theorem envelope_iff (alpha eta : ℝ) (ha : 0 < alpha) :
    alpha * (1 + eta) ≤ 1 ↔ eta ≤ (1 - alpha) / alpha := by
  rw [le_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith

-- C08: A constant carveout f < 1 preserves the derivative's sign.
theorem constant_fee_sign (I : ℝ → ℝ) (d x f : ℝ)
    (hI : HasDerivAt I d x) (hf : f < 1) :
    HasDerivAt (fun y => (1 - f) * I y) ((1 - f) * d) x ∧
      (0 ≤ (1 - f) * d ↔ 0 ≤ d) := by
  exact ⟨hI.const_mul (1 - f), mul_nonneg_iff_of_pos_left (sub_pos.mpr hf)⟩

-- C09: Fresh-depositor share identity (positive physical quantities imply these
-- nonzero hypotheses). u = B/(S+x), u0 = B/S.
theorem fresh_share (B S x : ℝ) (hB : B ≠ 0) (_hS : S ≠ 0)
    (hTx : S + x ≠ 0) :
    x / (S + x) = 1 - (B / (S + x)) / (B / S) := by
  field_simp [hB, hTx]
  ring

-- C10: Exact algebraic fresh-path condition; does not assert a global theorem.
theorem fresh_path_iff (u u0 rate slope : ℝ)
    (hu : 0 < u) (hu0 : 0 < u0) (hr : 0 < rate) :
    (1 - u / u0) * (1 + elasticity u rate slope) ≤ 1 ↔
      (u0 - u) * slope ≤ rate := by
  dsimp [elasticity]
  constructor
  · intro h
    have h' := (mul_le_mul_iff_of_pos_right (mul_pos hu0 hr)).mpr h
    field_simp at h'
    nlinarith
  · intro h
    apply (mul_le_mul_iff_of_pos_right (mul_pos hu0 hr)).mp
    field_simp
    nlinarith

-- C11: The model's nondecreasing rate gives nonnegative elasticity at an
-- interior utilization. Monotonicity is required only on the physical interval.
theorem elasticity_nonneg (R : ℝ → ℝ) (U : ℝ)
    (hU : U ∈ Set.Ioo (0 : ℝ) 1)
    (hmono : MonotoneOn R (Set.Ioo (0 : ℝ) 1)) (hr : 0 < R U) :
    0 ≤ elasticity U (R U) (deriv R U) := by
  have hd := hmono.derivWithin_nonneg (x := U)
  rw [derivWithin_of_mem_nhds (Ioo_mem_nhds hU.1 hU.2)] at hd
  exact div_nonneg (mul_nonneg hU.1.le hd) hr.le

-- C12: Assemble the model assumptions into the actual safe-share condition.
theorem income_deriv_safe_share_iff (R : ℝ → ℝ) (B T b x : ℝ)
    (hB : 0 < B) (hT : 0 < T + x)
    (hU : utilization B T x < 1)
    (hmono : MonotoneOn R (Set.Ioo (0 : ℝ) 1))
    (hR : DifferentiableAt ℝ R (utilization B T x))
    (hr : 0 < R (utilization B T x)) :
    0 ≤ deriv (income R B T b) x ↔
      share T b x ≤ 1 / (1 + elasticity (utilization B T x)
        (R (utilization B T x)) (deriv R (utilization B T x))) := by
  rw [income_deriv_nonneg_iff R B T b x hB hT hR hr]
  exact safe_share_iff _ _ (elasticity_nonneg R _ ⟨div_pos hB hT, hU⟩ hmono hr)

end
end SupplierMonotonicity
