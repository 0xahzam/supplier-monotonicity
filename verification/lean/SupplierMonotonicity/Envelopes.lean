import Mathlib

/-! Smooth envelope implications and order monotonicity.
These results do not assert the locally absolutely continuous converse.
The last theorem treats the nonnegative elasticity-derivative case explicitly.
-/
namespace SupplierMonotonicity
open Set intervalIntegral

theorem normalized_rate_antitone
    {F R : ℝ → ℝ} {a b : ℝ}
    (hFpos : ∀ x ∈ Icc a b, 0 < F x)
    (hRc : ContinuousOn R (Icc a b)) (hFc : ContinuousOn F (Icc a b))
    (hRd : ∀ x ∈ interior (Icc a b), DifferentiableAt ℝ R x)
    (hFd : ∀ x ∈ interior (Icc a b), DifferentiableAt ℝ F x)
    (henv : ∀ x ∈ interior (Icc a b), deriv R x * F x ≤ R x * deriv F x) :
    AntitoneOn (fun x => R x / F x) (Icc a b) := by
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have hFne : ∀ x ∈ interior (Icc a b), F x ≠ 0 := by
    intro x hx
    exact ne_of_gt (hFpos x (interior_subset hx))
  refine antitoneOn_of_deriv_nonpos hconv (hRc.div hFc ?_) ?_ ?_
  · intro x hx; exact ne_of_gt (hFpos x hx)
  · intro x hx
    exact ((hRd x hx).div (hFd x hx) (hFne x hx)).differentiableWithinAt
  · intro x hx
    have hd : deriv (fun y => R y / F y) x
        = (deriv R x * F x - R x * deriv F x) / F x ^ 2 := by
      simpa using deriv_div (hRd x hx) (hFd x hx) (hFne x hx)
    rw [hd]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [henv x hx]
    · positivity

theorem normalized_rate_bound
    {F R : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hFpos : ∀ x ∈ Icc a b, 0 < F x)
    (hanti : AntitoneOn (fun x => R x / F x) (Icc a b))
    {U : ℝ} (hU : U ∈ Icc a b) :
    R U ≤ R a * F U / F a := by
  have ha : a ∈ Icc a b := ⟨le_refl a, hab⟩
  have h := hanti ha hU hU.1
  have hFa : 0 < F a := hFpos a ha
  have hFU : 0 < F U := hFpos U hU
  rw [div_le_div_iff₀ hFU hFa] at h
  rw [le_div_iff₀ hFa]
  nlinarith

theorem running_inf_antitone {q₀ : ℝ → ℝ} {s : Set ℝ}
    (hbdd : ∀ U, BddBelow (q₀ '' {v | v ∈ s ∧ v ≤ U}))
    (hne : ∀ U ∈ s, (q₀ '' {v | v ∈ s ∧ v ≤ U}).Nonempty) :
    AntitoneOn (fun U => sInf (q₀ '' {v | v ∈ s ∧ v ≤ U})) s := by
  intro x hx y hy hxy
  refine csInf_le_csInf (hbdd y) (hne x hx) ?_
  rintro z ⟨v, ⟨hvs, hvx⟩, rfl⟩
  exact ⟨v, ⟨hvs, le_trans hvx hxy⟩, rfl⟩

theorem segment_fresh_ratio_monotone {m RL uL a b : ℝ}
    (hm : 0 ≤ m) (hb : b < 1)
    (hpos : ∀ u ∈ Icc a b, 0 < RL + m * (u - uL)) :
    MonotoneOn (fun u => (RL + m * (u - uL)) / (1 - u)) (Icc a b) := by
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have hne : ∀ u ∈ Icc a b, (1 : ℝ) - u ≠ 0 := by
    intro u hu; have : u ≤ b := hu.2; linarith
  have hnum : ∀ y : ℝ, HasDerivAt (fun z : ℝ => RL + m * (z - uL)) m y := by
    intro y; simpa using (((hasDerivAt_id y).sub_const uL).const_mul m).const_add RL
  have hden : ∀ y : ℝ, HasDerivAt (fun z : ℝ => (1:ℝ) - z) (-1) y := by
    intro y; simpa using (hasDerivAt_id y).const_sub (1:ℝ)
  refine monotoneOn_of_deriv_nonneg hconv ?_ ?_ ?_
  · exact ((continuousOn_const.add (continuousOn_const.mul
      (continuousOn_id.sub continuousOn_const))).div
      (continuousOn_const.sub continuousOn_id) hne)
  · intro u hu
    exact (((hnum u).fun_div (hden u) (hne u (interior_subset hu))).differentiableAt).differentiableWithinAt
  · intro u hu
    have hu' := interior_subset hu
    have h1 : (0:ℝ) < 1 - u := by have : u ≤ b := hu'.2; linarith
    have h2 : 0 < RL + m * (u - uL) := hpos u hu'
    rw [((hnum u).fun_div (hden u) (hne u hu')).deriv]
    apply div_nonneg _ (by positivity)
    nlinarith

theorem segment_elasticity_monotone {m ri ui a b : ℝ}
    (hpos : ∀ U ∈ Icc a b, 0 < ri + m * (U - ui))
    (hsign : 0 ≤ m * (ri - m * ui)) :
    MonotoneOn (fun U => U * m / (ri + m * (U - ui))) (Icc a b) := by
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have hne : ∀ U ∈ Icc a b, ri + m * (U - ui) ≠ 0 := fun U hU => ne_of_gt (hpos U hU)
  have hnum : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z * m) m y := by
    intro y; simpa using (hasDerivAt_id y).mul_const m
  have hden : ∀ y : ℝ, HasDerivAt (fun z : ℝ => ri + m * (z - ui)) m y := by
    intro y; simpa using (((hasDerivAt_id y).sub_const ui).const_mul m).const_add ri
  refine monotoneOn_of_deriv_nonneg hconv ?_ ?_ ?_
  · exact ((continuousOn_id.mul continuousOn_const).div
      (continuousOn_const.add (continuousOn_const.mul
        (continuousOn_id.sub continuousOn_const))) hne)
  · intro U hU
    exact (((hnum U).fun_div (hden U) (hne U (interior_subset hU))).differentiableAt).differentiableWithinAt
  · intro U hU
    have hU' := interior_subset hU
    have h2 : 0 < ri + m * (U - ui) := hpos U hU'
    rw [((hnum U).fun_div (hden U) (hne U hU')).deriv]
    have hkey : m * (ri + m * (U - ui)) - U * m * m = m * (ri - m * ui) := by ring
    rw [hkey]
    exact div_nonneg hsign (by positivity)

end SupplierMonotonicity
