import SupplierMonotonicity.Repairs

noncomputable section
open Set MeasureTheory
namespace SupplierMonotonicity

def smoothEta (e M w x : ℝ) : ℝ :=
  if x ≤ w then e+(M-e)*(3*(x/w)^2-2*(x/w)^3) else M

theorem smoothEta_continuous (e M w : ℝ) (hw : w ≠ 0) :
    Continuous (smoothEta e M w) := by
  apply Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
  intro x hx
  dsimp at hx
  subst x
  simp [div_self hw]
  ring

theorem smoothEta_integral (e M w L : ℝ) (hw : 0 < w) (hL : w ≤ L) :
    (∫ x in (0:ℝ)..L, smoothEta e M w x) = M*(L-w/2)+e*w/2 := by
  have hc := smoothEta_continuous e M w hw.ne'
  have ramp : (∫ x in (0:ℝ)..w, e+(M-e)*(3*(x/w)^2-2*(x/w)^3)) = w*(e+M)/2 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x (_ : x ∈ Set.uIcc (0:ℝ) w) => smooth_ramp_primitive_derivative e M w x hw.ne')
      ((by fun_prop : Continuous (fun x : ℝ => e+(M-e)*(3*(x/w)^2-2*(x/w)^3))).intervalIntegrable 0 w)
    rw [h]
    simp [div_self hw.ne']
    ring
  have hleft : (∫ x in (0:ℝ)..w, smoothEta e M w x) = w*(e+M)/2 := by
    rw [← ramp]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hw.le] at hx
    simp [smoothEta, hx.2]
  have hright : (∫ x in w..L, smoothEta e M w x) = (L-w)*M := by
    have heq : (∫ x in w..L, smoothEta e M w x) = ∫ _ in w..L, M := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hL] at hx
      rcases eq_or_lt_of_le hx.1 with he | he
      · subst x
        simp [smoothEta, div_self hw.ne']
        ring
      · simp [smoothEta, not_le.mpr he]
    rw [heq, intervalIntegral.integral_const]
    rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 w)
    (hc.intervalIntegrable w L), hleft, hright]
  ring

theorem smoothing_endpoint_unique (e M w L A : ℝ) (hw : 0 < w) (hL : w ≤ L) :
    (∫ x in (0:ℝ)..L, smoothEta e M w x) = A ↔ M=(A-e*w/2)/(L-w/2) := by
  rw [smoothEta_integral e M w L hw hL]
  exact smooth_plateau_unique w e M L A (ne_of_gt (by linarith))

theorem smooth_plateau_derivative_positive (L e Kstar w : ℝ)
    (hL : 0 < L) (hw : w ≤ L) (he : e < Kstar) :
    0 < deriv (fun w : ℝ => (Kstar*L-e*w/2)/(L-w/2)) w := by
  have hd : L-w/2 ≠ 0 := ne_of_gt (by linarith)
  rw [(smooth_plateau_derivative L e Kstar w hd).deriv]
  exact div_pos (mul_pos hL (sub_pos.mpr he)) (mul_pos (by norm_num) (sq_pos_of_ne_zero hd))

theorem smooth_zero_width (L e Kstar : ℝ) (hL : L ≠ 0) :
    (Kstar*L-e*0/2)/(L-0/2) = Kstar := by field_simp; ring

theorem smooth_full_width (L e Kstar : ℝ) (hL : L ≠ 0) :
    (Kstar*L-e*L/2)/(L-L/2) = 2*Kstar-e := by field_simp; ring

-- Existence of nonzero admissible transition width for every K>Kstar (eta0<Kstar).
theorem smoothing_width_exists (L e Kstar K : ℝ)
    (hL : 0 < L) (he : e < Kstar) (hK : Kstar < K) :
    ∃ w : ℝ, 0 < w ∧ w ≤ L ∧ (Kstar*L-e*w/2)/(L-w/2) ≤ K := by
  let bound := 2*L*(K-Kstar)/(K-e)
  have hb : 0 < bound := div_pos (mul_pos (mul_pos (by norm_num) hL) (sub_pos.mpr hK))
    (sub_pos.mpr (lt_trans he hK))
  refine ⟨min L bound, lt_min hL hb, min_le_left _ _, ?_⟩
  exact (smooth_width_iff _ e L Kstar K hL (min_le_left _ _) (lt_trans he hK)).mpr
    (min_le_right _ _)

theorem smoothEta_ceiling_iff (e M w L K : ℝ) (hw : 0 < w) (hL : w ≤ L)
    (heM : e ≤ M) : (∀ x ∈ Icc (0:ℝ) L, smoothEta e M w x ≤ K) ↔ M ≤ K := by
  constructor
  · intro hall
    have h := hall w ⟨hw.le,hL⟩
    simp [smoothEta,div_self hw.ne'] at h
    linarith
  · intro hM x hx
    by_cases hxw : x ≤ w
    · have ht : x/w ∈ Icc (0:ℝ) 1 := ⟨div_nonneg hx.1 hw.le, (div_le_one hw).mpr hxw⟩
      have hs := (smoothstep_range _ ht).2
      have hmul := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr heM)
      simp only [smoothEta, if_pos hxw]
      linarith
    · simp only [smoothEta, if_neg hxw]
      exact hM

-- Full pointwise ceiling equivalence for the nondegenerate prescribed ramp.
theorem smoothing_ceiling_width_iff (e w L Kstar K : ℝ)
    (hL : 0 < L) (hw : 0 < w) (hwL : w ≤ L)
    (he : e < Kstar) (hK : e < K) :
    (∀ x ∈ Icc (0:ℝ) L,
      smoothEta e ((Kstar*L-e*w/2)/(L-w/2)) w x ≤ K) ↔
      w ≤ 2*L*(K-Kstar)/(K-e) := by
  rw [smoothEta_ceiling_iff e _ w L K hw hwL
    (le_of_lt (lt_trans he (smooth_plateau_above_average w e L Kstar hL hw hwL he)))]
  exact smooth_width_iff w e L Kstar K hL hwL hK

-- Construct the rate in log-utilization coordinate x, with a positive anchor.
-- smoothEta is globally continuous, so no extension assumption is needed here.
def reconstructedRate (eta : ℝ → ℝ) (r x : ℝ) : ℝ :=
  r * Real.exp (∫ t in (0:ℝ)..x, eta t)

theorem reconstructedRate_derivative (eta : ℝ → ℝ) (r x : ℝ)
    (hc : Continuous eta) :
    HasDerivAt (reconstructedRate eta r) (reconstructedRate eta r x * eta x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert h.exp.const_mul r using 1
  dsimp [reconstructedRate]
  ring

theorem reconstructedRate_positive (eta : ℝ → ℝ) (r x : ℝ) (hr : 0 < r) :
    0 < reconstructedRate eta r x := mul_pos hr (Real.exp_pos _)

theorem reconstructedRate_anchor (eta : ℝ → ℝ) (r : ℝ) :
    reconstructedRate eta r 0 = r := by simp [reconstructedRate]

theorem reconstructedRate_C1 (eta : ℝ → ℝ) (r : ℝ) (hc : Continuous eta) :
    ContDiff ℝ 1 (reconstructedRate eta r) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (reconstructedRate_derivative eta r x hc).differentiableAt, ?_⟩
  have hd : deriv (reconstructedRate eta r) = fun x => reconstructedRate eta r x * eta x := by
    funext x
    exact (reconstructedRate_derivative eta r x hc).deriv
  rw [hd]
  have hdiff : Differentiable ℝ (reconstructedRate eta r) :=
    fun x => (reconstructedRate_derivative eta r x hc).differentiableAt
  exact hdiff.continuous.mul hc

theorem reconstructedRate_endpoint (eta : ℝ → ℝ) (r top L : ℝ)
    (hr : 0 < r) (ht : 0 < top)
    (hi : (∫ t in (0:ℝ)..L, eta t) = Real.log (top/r)) :
    reconstructedRate eta r L = top := by
  dsimp [reconstructedRate]
  rw [hi, Real.exp_log (div_pos ht hr)]
  field_simp

-- Reparameterization x=log(U/O) recovers the intended utilization elasticity.
theorem reconstructed_utilization_derivative (eta : ℝ → ℝ) (r O u : ℝ)
    (hc : Continuous eta) (hO : 0 < O) (hu : 0 < u) :
    HasDerivAt (fun u => reconstructedRate eta r (Real.log (u/O)))
      (reconstructedRate eta r (Real.log (u/O))*eta (Real.log (u/O))/u) u := by
  have hlog := ((hasDerivAt_id u).div_const O).log (ne_of_gt (div_pos hu hO))
  convert (reconstructedRate_derivative eta r (Real.log (u/O)) hc).comp u hlog using 1
  dsimp
  field_simp

theorem reconstructed_utilization_elasticity (eta : ℝ → ℝ) (r O u : ℝ)
    (hc : Continuous eta) (hr : 0 < r) (hO : 0 < O) (hu : 0 < u) :
    elasticity u (reconstructedRate eta r (Real.log (u/O)))
      (deriv (fun u => reconstructedRate eta r (Real.log (u/O))) u) =
      eta (Real.log (u/O)) := by
  rw [(reconstructed_utilization_derivative eta r O u hc hO hu).deriv]
  have hp := reconstructedRate_positive eta r (Real.log (u/O)) hr
  dsimp [elasticity]
  field_simp

-- The converse FTC bridge for a positive C1 log-coordinate rate trajectory.
theorem log_rate_integral (G : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hc : ContinuousOn G (Icc 0 L)) (hp : ∀ x ∈ Icc 0 L, 0 < G x)
    (hd : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ G x)
    (hi : IntervalIntegrable (fun x => deriv G x/G x) volume 0 L) :
    (∫ x in (0:ℝ)..L, deriv G x/G x) = Real.log (G L/G 0) := by
  rw [Real.log_div (hp L ⟨hL,le_rfl⟩).ne' (hp 0 ⟨le_rfl,hL⟩).ne']
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL
    (hc.log (fun x hx => (hp x hx).ne'))
    (fun x hx => (hd x hx).hasDerivAt.log (hp x ⟨hx.1.le,hx.2.le⟩).ne') hi

theorem C1_log_rate_overshoot (G : ℝ → ℝ) (L Kstar : ℝ) (hL : 0 < L)
    (hc : ContinuousOn G (Icc 0 L)) (hp : ∀ x ∈ Icc 0 L, 0 < G x)
    (hd : ∀ x ∈ Ioo 0 L, DifferentiableAt ℝ G x)
    (he : ContinuousOn (fun x => deriv G x/G x) (Icc 0 L))
    (hstart : deriv G 0/G 0 < Kstar)
    (hbudget : Real.log (G L/G 0) = Kstar*L) :
    ∃ x ∈ Icc (0:ℝ) L, Kstar < deriv G x/G x := by
  apply continuous_elasticity_overshoot _ L Kstar hL he hstart
  rw [log_rate_integral G L hL.le hc hp hd (he.intervalIntegrable_of_Icc hL.le),hbudget]

end SupplierMonotonicity
