import SupplierMonotonicity.Model

/-!
# The fresh depositor guarantee

A fresh depositor enters an empty position from initial utilization `u₀` and ends at `u`.
Protecting every such depositor from every start is the profile `α = 1 - U`, with envelope
`E(U) = U / (1 - U)` and hyperbolic boundary curve `R(U) = c / (1 - U)` (paper, Section 7,
and the piecewise linear form in Section 7.1).

Not covered here: boundary-curve uniqueness through the integrated family (it depends on the
unformalized general Theorem 2).
-/

namespace SupplierMonotonicity

open Set

/-! ### Fresh-depositor share and path condition -/

/-- With `u = B / (S + x)` and `u₀ = B / S`, the fresh depositor's share is `1 - u / u₀`.
The hypothesis `S ≠ 0` is unused by the proof; it is kept so that `u₀` is a real utilization. -/
theorem fresh_share (B S x : ℝ) (hB : B ≠ 0) (_hS : S ≠ 0) (hTx : S + x ≠ 0) :
    x / (S + x) = 1 - (B / (S + x)) / (B / S) := by
  field_simp [hB, hTx]
  ring

/-- The sign condition along a fresh path, in cross-multiplied form `(u₀ - u) R' ≤ R`. -/
theorem fresh_path_iff (u u0 rate slope : ℝ) (hu : 0 < u) (hu0 : 0 < u0) (hr : 0 < rate) :
    (1 - u / u0) * (1 + elasticity u rate slope) ≤ 1 ↔ (u0 - u) * slope ≤ rate := by
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

/-- For a nondecreasing rate the worst start is `u₀ = 1`. -/
theorem fresh_all_starts_iff (u r m : ℝ) (hu : u ≤ 1) (hm : 0 ≤ m) :
    (∀ u0 ∈ Icc u 1, (u0 - u) * m ≤ r) ↔ (1 - u) * m ≤ r := by
  constructor
  · intro h
    exact h 1 ⟨hu, le_rfl⟩
  · intro h u0 h0
    exact le_trans (mul_le_mul_of_nonneg_right (sub_le_sub_right h0.2 u) hm) h

/-! ### Envelope and boundary curve -/

/-- The profile `α = 1 - u` has envelope `(1 - α) / α = u / (1 - u)`. -/
theorem fresh_envelope (u : ℝ) : (1 - (1 - u)) / (1 - u) = u / (1 - u) := by ring

/-- The design rule `η ≤ u / (1 - u)` is `(1 - u) R' ≤ R`. -/
theorem fresh_envelope_iff (u r m : ℝ) (hu : 0 < u) (hu1 : u < 1) (hr : 0 < r) :
    elasticity u r m ≤ u / (1 - u) ↔ (1 - u) * m ≤ r := by
  dsimp [elasticity]
  rw [div_le_div_iff₀ hr (sub_pos.mpr hu1)]
  constructor <;> intro h <;> nlinarith

theorem hyperbolic_boundary_derivative (c u : ℝ) (hu : u ≠ 1) :
    HasDerivAt (fun v => c / (1 - v)) (c / (1 - u) ^ 2) u := by
  have hn : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  convert (hasDerivAt_const u c).div ((hasDerivAt_const u 1).sub (hasDerivAt_id u)) hn using 1
  dsimp
  ring

/-- The hyperbolic curve `c / (1 - u)` sits exactly on the envelope. -/
theorem hyperbolic_boundary_elasticity (c u : ℝ) (hc : c ≠ 0) (hu : u ≠ 1) :
    elasticity u (c / (1 - u)) (c / (1 - u) ^ 2) = u / (1 - u) := by
  have hn : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  dsimp [elasticity]
  field_simp

/-- Fresh-depositor marginal income on the hyperbolic boundary (Appendix A). -/
theorem fresh_boundary_income_algebra (c u u0 : ℝ) (hc : c ≠ 0) (hu : u ≠ 1) (hu0 : u0 ≠ 0) :
    u * (c / (1 - u)) * (1 - (1 - u / u0) * (1 + elasticity u (c / (1 - u)) (c / (1 - u) ^ 2))) =
      c * u ^ 2 * (1 - u0) / (u0 * (1 - u) ^ 2) := by
  have hn : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  rw [hyperbolic_boundary_elasticity c u hc hu]
  field_simp
  ring

/-- A positive rate meeting `r (1 - u) ≤ r₀` forces a positive base rate `r₀`. -/
theorem fresh_base_positive (r0 r u : ℝ) (hr : 0 < r) (hu : u < 1) (hb : r * (1 - u) ≤ r0) :
    0 < r0 :=
  lt_of_lt_of_le (mul_pos hr (sub_pos.mpr hu)) hb

/-! ### Piecewise linear curves (Section 7.1) -/

/-- On a linear segment from `l` to `h` the left endpoint is the binding constraint. -/
theorem fresh_linear_segment_iff (l h r m : ℝ) (hlh : l ≤ h) (hm : 0 ≤ m) :
    (∀ u ∈ Icc l h, m * (1 - u) ≤ r + m * (u - l)) ↔ m * (1 - l) ≤ r := by
  constructor
  · intro hall
    simpa using hall l ⟨le_rfl, hlh⟩
  · intro hb u hu
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hu.1)]

/-- The segment condition as a cap on the ratio of adjacent kink rates `s / r`. -/
theorem adjacent_fresh_ratio_iff (l h r s : ℝ) (hlh : l < h) (hl : l < 1) (hr : 0 < r) :
    ((s - r) / (h - l)) * (1 - l) ≤ r ↔ s / r ≤ 1 + (h - l) / (1 - l) := by
  have hd : 0 < h - l := sub_pos.mpr hlh
  have he : 0 < 1 - l := sub_pos.mpr hl
  rw [div_le_iff₀ hr]
  constructor
  · intro H
    have H' := (mul_le_mul_iff_of_pos_right hd).mpr H
    field_simp at H'
    apply (mul_le_mul_iff_of_pos_right he).mp
    field_simp
    nlinarith
  · intro H
    have H' := (mul_le_mul_iff_of_pos_right he).mpr H
    field_simp at H'
    apply (mul_le_mul_iff_of_pos_right hd).mp
    field_simp
    nlinarith

/-- On a positive nondecreasing linear segment below `U = 1`, `R / (1 - U)` is increasing. -/
theorem segment_fresh_ratio_monotone {m RL uL a b : ℝ} (hm : 0 ≤ m) (hb : b < 1)
    (hpos : ∀ u ∈ Icc a b, 0 < RL + m * (u - uL)) :
    MonotoneOn (fun u => (RL + m * (u - uL)) / (1 - u)) (Icc a b) := by
  have hne : ∀ u ∈ Icc a b, (1 : ℝ) - u ≠ 0 := by
    intro u hu
    linarith [hu.2]
  have hnum : ∀ y : ℝ, HasDerivAt (fun z : ℝ => RL + m * (z - uL)) m y := by
    intro y
    simpa using (((hasDerivAt_id y).sub_const uL).const_mul m).const_add RL
  have hden : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (1 : ℝ) - z) (-1) y := by
    intro y
    simpa using (hasDerivAt_id y).const_sub (1 : ℝ)
  refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
  · exact (continuousOn_const.add (continuousOn_const.mul
      (continuousOn_id.sub continuousOn_const))).div (continuousOn_const.sub continuousOn_id) hne
  · intro u hu
    exact ((hnum u).fun_div (hden u) (hne u (interior_subset hu))).differentiableAt
      |>.differentiableWithinAt
  · intro u hu
    have hu' := interior_subset hu
    have h1 : (0 : ℝ) < 1 - u := by linarith [hu'.2]
    have h2 : 0 < RL + m * (u - uL) := hpos u hu'
    rw [((hnum u).fun_div (hden u) (hne u hu')).deriv]
    apply div_nonneg _ (by positivity)
    nlinarith

end SupplierMonotonicity
