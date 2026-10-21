import SupplierMonotonicity.Model

/-!
# The admissible family

Protection profiles, elasticity envelopes and the integral representation of rate curves
(paper, Section 5).

The paper's Theorem 2 is stated for locally absolutely continuous rates and almost-everywhere
conditions. That version is **not** formalized. This file proves the smooth pieces:

* the pointwise equivalence between a protection profile and its elasticity envelope;
* the smooth implication "envelope ⇒ normalized rate is antitone ⇒ multiplicative bound";
* the construction `R(x) = r · exp (∫₀ˣ η)` in the log coordinate `x = log (U / O)`, which is
  positive, `C¹` and has elasticity exactly `η` for continuous `η`.
-/

namespace SupplierMonotonicity

open Set MeasureTheory

/-! ### Profiles and envelopes -/

/-- The protection constraint `α (1 + η) ≤ 1` is the envelope `η ≤ (1 - α) / α`. -/
theorem envelope_iff (alpha eta : ℝ) (ha : 0 < alpha) :
    alpha * (1 + eta) ≤ 1 ↔ eta ≤ (1 - alpha) / alpha := by
  rw [le_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith

/-- An envelope for share `a` protects every smaller share, and is necessary. -/
theorem profile_all_shares_iff (a eta : ℝ) (ha : 0 < a) (he : 0 ≤ eta) :
    (∀ alpha ∈ Icc (0 : ℝ) a, alpha * (1 + eta) ≤ 1) ↔ eta ≤ (1 - a) / a := by
  rw [← envelope_iff a eta ha]
  constructor
  · intro h
    exact h a ⟨ha.le, le_rfl⟩
  · intro h alpha hα
    exact le_trans (mul_le_mul_of_nonneg_right hα.2 (by linarith)) h

/-! ### Smooth bound from an envelope -/

/-- If `R' F ≤ R F'` inside `[a, b]` and `F > 0`, then `R / F` is antitone on `[a, b]`.
With `F' = E F / U` this is the envelope `η ≤ E` integrated. -/
theorem normalized_rate_antitone {F R : ℝ → ℝ} {a b : ℝ}
    (hFpos : ∀ x ∈ Icc a b, 0 < F x)
    (hRc : ContinuousOn R (Icc a b)) (hFc : ContinuousOn F (Icc a b))
    (hRd : ∀ x ∈ interior (Icc a b), DifferentiableAt ℝ R x)
    (hFd : ∀ x ∈ interior (Icc a b), DifferentiableAt ℝ F x)
    (henv : ∀ x ∈ interior (Icc a b), deriv R x * F x ≤ R x * deriv F x) :
    AntitoneOn (fun x => R x / F x) (Icc a b) := by
  have hFne : ∀ x ∈ interior (Icc a b), F x ≠ 0 :=
    fun x hx => (hFpos x (interior_subset hx)).ne'
  refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (hRc.div hFc fun x hx => (hFpos x hx).ne') ?_ ?_
  · intro x hx
    exact ((hRd x hx).div (hFd x hx) (hFne x hx)).differentiableWithinAt
  · intro x hx
    have hd : deriv (fun y => R y / F y) x =
        (deriv R x * F x - R x * deriv F x) / F x ^ 2 := by
      simpa using deriv_div (hRd x hx) (hFd x hx) (hFne x hx)
    rw [hd]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith [henv x hx]
    · positivity

/-- Reading the multiplicative bound `R U ≤ R a · F U / F a` off an antitone `R / F`. -/
theorem normalized_rate_bound {F R : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hFpos : ∀ x ∈ Icc a b, 0 < F x)
    (hanti : AntitoneOn (fun x => R x / F x) (Icc a b))
    {U : ℝ} (hU : U ∈ Icc a b) :
    R U ≤ R a * F U / F a := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have h := hanti ha hU hU.1
  have hFa : 0 < F a := hFpos a ha
  have hFU : 0 < F U := hFpos U hU
  rw [div_le_div_iff₀ hFU hFa] at h
  rw [le_div_iff₀ hFa]
  nlinarith

/-- The sign of the derivative of `R / F` is the envelope condition `u R' ≤ E R`. -/
theorem normalized_derivative_iff (u r m f E : ℝ) (hu : 0 < u) (hf : 0 < f) :
    (m * f - r * (E * f / u)) / f ^ 2 ≤ 0 ↔ u * m ≤ E * r := by
  rw [div_le_iff₀ (sq_pos_of_pos hf)]
  simp only [zero_mul]
  constructor
  · intro h
    have h' := (mul_le_mul_iff_of_pos_right hu).mpr h
    field_simp at h'
    nlinarith
  · intro h
    apply (mul_le_mul_iff_of_pos_right hu).mp
    field_simp
    nlinarith

/-! ### Building a rate curve from its elasticity -/

/-- The rate curve with elasticity `η` in the log coordinate `x = log (U / O)`, anchored at
rate `r` when `x = 0`. -/
noncomputable def reconstructedRate (eta : ℝ → ℝ) (r x : ℝ) : ℝ :=
  r * Real.exp (∫ t in (0 : ℝ)..x, eta t)

theorem reconstructedRate_derivative (eta : ℝ → ℝ) (r x : ℝ) (hc : Continuous eta) :
    HasDerivAt (reconstructedRate eta r) (reconstructedRate eta r x * eta x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert h.exp.const_mul r using 1
  dsimp [reconstructedRate]
  ring

theorem reconstructedRate_positive (eta : ℝ → ℝ) (r x : ℝ) (hr : 0 < r) :
    0 < reconstructedRate eta r x :=
  mul_pos hr (Real.exp_pos _)

theorem reconstructedRate_anchor (eta : ℝ → ℝ) (r : ℝ) : reconstructedRate eta r 0 = r := by
  simp [reconstructedRate]

theorem reconstructedRate_C1 (eta : ℝ → ℝ) (r : ℝ) (hc : Continuous eta) :
    ContDiff ℝ 1 (reconstructedRate eta r) := by
  have hdiff : Differentiable ℝ (reconstructedRate eta r) :=
    fun x => (reconstructedRate_derivative eta r x hc).differentiableAt
  have hd : deriv (reconstructedRate eta r) = fun x => reconstructedRate eta r x * eta x := by
    funext x
    exact (reconstructedRate_derivative eta r x hc).deriv
  apply contDiff_one_iff_deriv.mpr
  rw [hd]
  exact ⟨hdiff, hdiff.continuous.mul hc⟩

/-- The curve reaches `top` at `x = L` exactly when `∫₀ᴸ η = log (top / r)`. -/
theorem reconstructedRate_endpoint (eta : ℝ → ℝ) (r top L : ℝ) (hr : 0 < r) (ht : 0 < top)
    (hi : (∫ t in (0 : ℝ)..L, eta t) = Real.log (top / r)) :
    reconstructedRate eta r L = top := by
  dsimp [reconstructedRate]
  rw [hi, Real.exp_log (div_pos ht hr)]
  field_simp

/-- Changing back to utilization with `x = log (u / O)`. -/
theorem reconstructed_utilization_derivative (eta : ℝ → ℝ) (r O u : ℝ)
    (hc : Continuous eta) (hO : 0 < O) (hu : 0 < u) :
    HasDerivAt (fun u => reconstructedRate eta r (Real.log (u / O)))
      (reconstructedRate eta r (Real.log (u / O)) * eta (Real.log (u / O)) / u) u := by
  have hlog := ((hasDerivAt_id u).div_const O).log (div_pos hu hO).ne'
  convert (reconstructedRate_derivative eta r (Real.log (u / O)) hc).comp u hlog using 1
  dsimp
  field_simp

/-- The reconstructed curve has utilization elasticity exactly `η (log (u / O))`. -/
theorem reconstructed_utilization_elasticity (eta : ℝ → ℝ) (r O u : ℝ)
    (hc : Continuous eta) (hr : 0 < r) (hO : 0 < O) (hu : 0 < u) :
    elasticity u (reconstructedRate eta r (Real.log (u / O)))
      (deriv (fun u => reconstructedRate eta r (Real.log (u / O))) u) =
      eta (Real.log (u / O)) := by
  rw [(reconstructed_utilization_derivative eta r O u hc hO hu).deriv]
  have hp := reconstructedRate_positive eta r (Real.log (u / O)) hr
  dsimp [elasticity]
  field_simp

end SupplierMonotonicity
