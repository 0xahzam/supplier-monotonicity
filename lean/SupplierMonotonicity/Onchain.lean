import SupplierMonotonicity.Model

/-!
# Checking the constraint onchain

For a piecewise linear rate curve, the elasticity ceiling only needs checking at the two
endpoints of each segment, and the check can be written without division (paper, Section 11).

These are statements about continuous real arithmetic. They do not prove anything about rounded
integer arithmetic or about a deployed contract.
-/

namespace SupplierMonotonicity

open Set

/-- Division-free form of `η ≤ K` from finite differences `dr / du`. -/
theorem integer_endpoint_iff (u dr du r K : ℝ) (hd : 0 < du) (hr : 0 < r) :
    u * (dr / du) / r ≤ K ↔ u * dr ≤ K * r * du := by
  rw [div_le_iff₀ hr, ← mul_div_assoc, div_le_iff₀ hd]

/-- On a linear segment, the cross-multiplied ceiling is affine in `u`, so checking both
endpoints suffices. -/
theorem fixed_linear_endpoint_suffices (l h u r m K : ℝ) (hlh : l < h) (hu : u ∈ Icc l h)
    (hl : l * m ≤ K * r) (hh : h * m ≤ K * (r + m * (h - l))) :
    u * m ≤ K * (r + m * (u - l)) := by
  have h1 := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hl)
  have h2 := mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hh)
  have hid : (h - u) * (K * r - l * m) + (u - l) * (K * (r + m * (h - l)) - h * m) =
      (h - l) * (K * (r + m * (u - l)) - u * m) := by ring
  have hz : 0 ≤ (h - l) * (K * (r + m * (u - l)) - u * m) := by
    rw [← hid]
    linarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (sub_pos.mpr hlh)).mp hz)

/-- On a linear segment, elasticity is increasing when `m (rᵢ - m uᵢ) ≥ 0`. The opposite sign
is covered by `fixed_linear_endpoint_suffices`, not by this lemma. -/
theorem segment_elasticity_monotone {m ri ui a b : ℝ}
    (hpos : ∀ U ∈ Icc a b, 0 < ri + m * (U - ui)) (hsign : 0 ≤ m * (ri - m * ui)) :
    MonotoneOn (fun U => U * m / (ri + m * (U - ui))) (Icc a b) := by
  have hne : ∀ U ∈ Icc a b, ri + m * (U - ui) ≠ 0 := fun U hU => (hpos U hU).ne'
  have hnum : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z * m) m y := by
    intro y
    simpa using (hasDerivAt_id y).mul_const m
  have hden : ∀ y : ℝ, HasDerivAt (fun z : ℝ => ri + m * (z - ui)) m y := by
    intro y
    simpa using (((hasDerivAt_id y).sub_const ui).const_mul m).const_add ri
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
  · exact (continuousOn_id.mul continuousOn_const).div
      (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))) hne
  · intro U hU
    exact ((hnum U).fun_div (hden U) (hne U (interior_subset hU))).differentiableAt
      |>.differentiableWithinAt
  · intro U hU
    have hU' := interior_subset hU
    have h2 : 0 < ri + m * (U - ui) := hpos U hU'
    rw [((hnum U).fun_div (hden U) (hne U hU')).deriv]
    have hkey : m * (ri + m * (U - ui)) - U * m * m = m * (ri - m * ui) := by ring
    rw [hkey]
    exact div_nonneg hsign (by positivity)

end SupplierMonotonicity
