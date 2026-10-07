import SupplierMonotonicity.FixedShare

/-!
# Smooth constructions

Why a `C¹` curve cannot attain the endpoint bound `K*`, and what smoothing costs
(paper, Appendix E).

* `continuous_rate_supremum_strict`: if `R'/R` is continuous on `[O, 1]` and the curve starts
  below `K*`, its elasticity must exceed `K*` somewhere.
* `smoothEta` is the explicit smoothstep ramp followed by a plateau. Its continuity, exact
  integral, plateau value, plateau derivative and ceiling/width equivalence are proved.

At the left endpoint `O`, `deriv R O` is the derivative of an ambient differentiable extension.
No equality with the other branch of an assembled curve is assumed.

Not covered here: assembling the `C¹`/`C²` joins of a full constructed curve.
-/

namespace SupplierMonotonicity

open Set MeasureTheory

/-! ### `C¹` makes `K*` unattainable -/

/-- If `R'/R` is continuous, `η(O) < K*` and the endpoint budget is exactly `K*`, then
`η > K*` somewhere on `[O, 1]`. -/
theorem continuous_rate_overshoot (R : ℝ → ℝ) (O Kstar : ℝ) (hO : 0 < O) (hO1 : O < 1)
    (hc : ContinuousOn R (Icc O 1)) (hp : ∀ u ∈ Icc O 1, 0 < R u)
    (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (hq : ContinuousOn (fun u => deriv R u / R u) (Icc O 1))
    (hstart : elasticity O (R O) (deriv R O) < Kstar)
    (hbudget : Real.log (R 1 / R O) = Kstar * Real.log (1 / O)) :
    ∃ u ∈ Icc O 1, Kstar < elasticity u (R u) (deriv R u) := by
  by_contra hall
  push_neg at hall
  have hbcont : ContinuousOn (fun u : ℝ => Kstar / u) (Icc O 1) :=
    continuousOn_const.div continuousOn_id fun u hu => (lt_of_lt_of_le hO hu.1).ne'
  have hle : ∀ u ∈ Ioc O 1, deriv R u / R u ≤ Kstar / u := by
    intro u hu
    have hr := hp u ⟨hu.1.le, hu.2⟩
    have hu0 := lt_trans hO hu.1
    have hh := hall u ⟨hu.1.le, hu.2⟩
    dsimp [elasticity] at hh
    rw [div_le_iff₀ hr] at hh
    rw [div_le_div_iff₀ hr hu0]
    nlinarith
  have hlt : deriv R O / R O < Kstar / O := by
    have hr := hp O ⟨le_rfl, hO1.le⟩
    dsimp [elasticity] at hstart
    rw [div_lt_iff₀ hr] at hstart
    rw [div_lt_div_iff₀ hr hO]
    nlinarith
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hO1 hq hbcont hle ⟨O, ⟨le_rfl, hO1.le⟩, hlt⟩
  rw [log_rate_integral_on R O 1 hO1.le hc hp hd (hq.intervalIntegrable_of_Icc hO1.le),
    log_budget_integral O 1 Kstar hO hO1.le, hbudget] at hi
  exact lt_irrefl _ hi

/-- The strict form of the paper: `K* < sup_{[O,1]} η`. -/
theorem continuous_rate_supremum_strict (R : ℝ → ℝ) (O Kstar : ℝ) (hO : 0 < O) (hO1 : O < 1)
    (hc : ContinuousOn R (Icc O 1)) (hp : ∀ u ∈ Icc O 1, 0 < R u)
    (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (hq : ContinuousOn (fun u => deriv R u / R u) (Icc O 1))
    (hstart : elasticity O (R O) (deriv R O) < Kstar)
    (hbudget : Real.log (R 1 / R O) = Kstar * Real.log (1 / O)) :
    Kstar < sSup ((fun u => elasticity u (R u) (deriv R u)) '' Icc O 1) := by
  obtain ⟨u, hu, hgt⟩ := continuous_rate_overshoot R O Kstar hO hO1 hc hp hd hq hstart hbudget
  have he : ContinuousOn (fun u => elasticity u (R u) (deriv R u)) (Icc O 1) := by
    simpa [elasticity, mul_div_assoc] using continuousOn_id.mul hq
  have hb := (isCompact_Icc.image_of_continuousOn he).bddAbove
  exact lt_of_lt_of_le hgt (le_csSup hb ⟨u, hu, rfl⟩)

/-- A continuous derivative and a positive rate give a continuous `R'/R`. -/
theorem continuous_quotient_of_C1_data (R : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn R (Icc a b)) (hd : ContinuousOn (deriv R) (Icc a b))
    (hp : ∀ u ∈ Icc a b, 0 < R u) :
    ContinuousOn (fun u => deriv R u / R u) (Icc a b) :=
  hd.div hc fun u hu => (hp u hu).ne'

/-! ### The smoothstep `s(t) = 3t² - 2t³` -/

theorem smoothstep_primitive_derivative (t : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 3 - t ^ 4 / 2) (3 * t ^ 2 - 2 * t ^ 3) t := by
  convert (hasDerivAt_pow 3 t).sub ((hasDerivAt_pow 4 t).div_const 2) using 1
  ring

theorem smoothstep_derivative (t : ℝ) :
    HasDerivAt (fun t : ℝ => 3 * t ^ 2 - 2 * t ^ 3) (6 * t - 6 * t ^ 2) t := by
  convert ((hasDerivAt_pow 2 t).const_mul 3).sub ((hasDerivAt_pow 3 t).const_mul 2) using 1
  ring

/-- `s(0) = 0`, `s(1) = 1`, `s'(0) = s'(1) = 0`. -/
theorem smoothstep_endpoint_values :
    (3 * (0 : ℝ) ^ 2 - 2 * 0 ^ 3 = 0) ∧ (3 * (1 : ℝ) ^ 2 - 2 * 1 ^ 3 = 1) ∧
      (6 * (0 : ℝ) - 6 * 0 ^ 2 = 0) ∧ (6 * (1 : ℝ) - 6 * 1 ^ 2 = 0) := by
  norm_num

theorem smoothstep_range (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ 3 * t ^ 2 - 2 * t ^ 3 ∧ 3 * t ^ 2 - 2 * t ^ 3 ≤ 1 := by
  constructor
  · nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 3 - 2 * t by linarith [ht.2])]
  · nlinarith [mul_nonneg (sq_nonneg (1 - t)) (show 0 ≤ 1 + 2 * t by linarith [ht.1])]

/-- `∫₀¹ s = 1/2`. -/
theorem smoothstep_integral : (∫ t in (0 : ℝ)..1, 3 * t ^ 2 - 2 * t ^ 3) = 1 / 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => smoothstep_primitive_derivative t)
    ((by fun_prop : Continuous fun t : ℝ => 3 * t ^ 2 - 2 * t ^ 3).intervalIntegrable 0 1)
  norm_num at h ⊢

/-- The ramp's antiderivative meets the plateau's at `x = w`. -/
theorem smooth_primitive_join (e M w : ℝ) (hw : w ≠ 0) :
    e * w + (M - e) * w * ((w / w) ^ 3 - (w / w) ^ 4 / 2) = w * (e + M) / 2 + M * (w - w) := by
  field_simp
  ring

theorem smooth_ramp_primitive_derivative (e M w x : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun x : ℝ => e * x + (M - e) * w * ((x / w) ^ 3 - (x / w) ^ 4 / 2))
      (e + (M - e) * (3 * (x / w) ^ 2 - 2 * (x / w) ^ 3)) x := by
  have h := ((hasDerivAt_id x).const_mul e).add
    (((smoothstep_primitive_derivative (x / w)).comp x
      ((hasDerivAt_id x).div_const w)).const_mul ((M - e) * w))
  convert h using 1
  dsimp
  field_simp

/-! ### Plateau algebra for the cost of smoothing -/

/-- Ramp area plus plateau area. -/
theorem smooth_area_identity (w e M L : ℝ) :
    w * (e + M) / 2 + M * (L - w) = M * (L - w / 2) + e * w / 2 := by
  ring

theorem smooth_plateau_unique (w e M L A : ℝ) (hd : L - w / 2 ≠ 0) :
    M * (L - w / 2) + e * w / 2 = A ↔ M = (A - e * w / 2) / (L - w / 2) := by
  rw [eq_div_iff hd]
  constructor <;> intro h <;> linarith

theorem smooth_width_iff (w e L Kstar K : ℝ) (hL : 0 < L) (hw : w ≤ L) (hK : e < K) :
    (Kstar * L - e * w / 2) / (L - w / 2) ≤ K ↔ w ≤ 2 * L * (K - Kstar) / (K - e) := by
  rw [div_le_iff₀ (by linarith : 0 < L - w / 2), le_div_iff₀ (sub_pos.mpr hK)]
  constructor <;> intro h <;> nlinarith

theorem smooth_plateau_above_average (w e L Kstar : ℝ) (hL : 0 < L) (hw : 0 < w) (hwL : w ≤ L)
    (he : e < Kstar) : Kstar < (Kstar * L - e * w / 2) / (L - w / 2) := by
  rw [lt_div_iff₀ (by linarith : 0 < L - w / 2)]
  nlinarith [mul_pos hw (sub_pos.mpr he)]

theorem smooth_plateau_derivative (L e Kstar w : ℝ) (hd : L - w / 2 ≠ 0) :
    HasDerivAt (fun w : ℝ => (Kstar * L - e * w / 2) / (L - w / 2))
      (L * (Kstar - e) / (2 * (L - w / 2) ^ 2)) w := by
  have hn := (hasDerivAt_const w (Kstar * L)).sub (((hasDerivAt_id w).const_mul e).div_const 2)
  have hh := (hasDerivAt_const w L).sub ((hasDerivAt_id w).div_const 2)
  convert hn.div hh hd using 1
  dsimp
  field_simp
  ring

theorem smooth_plateau_derivative_positive (L e Kstar w : ℝ) (hL : 0 < L) (hw : w ≤ L)
    (he : e < Kstar) : 0 < deriv (fun w : ℝ => (Kstar * L - e * w / 2) / (L - w / 2)) w := by
  have hd : L - w / 2 ≠ 0 := (by linarith : 0 < L - w / 2).ne'
  rw [(smooth_plateau_derivative L e Kstar w hd).deriv]
  exact div_pos (mul_pos hL (sub_pos.mpr he)) (mul_pos (by norm_num) (sq_pos_of_ne_zero hd))

/-- `w = 0` gives the nonsmooth limit `η_max = K*`. -/
theorem smooth_zero_width (L e Kstar : ℝ) (hL : L ≠ 0) :
    (Kstar * L - e * 0 / 2) / (L - 0 / 2) = Kstar := by
  field_simp
  ring

theorem smooth_full_width (L e Kstar : ℝ) (hL : L ≠ 0) :
    (Kstar * L - e * L / 2) / (L - L / 2) = 2 * Kstar - e := by
  field_simp
  ring

/-- Every ceiling `K > K*` admits a positive transition width. -/
theorem smoothing_width_exists (L e Kstar K : ℝ) (hL : 0 < L) (he : e < Kstar) (hK : Kstar < K) :
    ∃ w : ℝ, 0 < w ∧ w ≤ L ∧ (Kstar * L - e * w / 2) / (L - w / 2) ≤ K := by
  have hb : 0 < 2 * L * (K - Kstar) / (K - e) :=
    div_pos (mul_pos (mul_pos two_pos hL) (sub_pos.mpr hK)) (sub_pos.mpr (lt_trans he hK))
  refine ⟨min L (2 * L * (K - Kstar) / (K - e)), lt_min hL hb, min_le_left _ _, ?_⟩
  exact (smooth_width_iff _ e L Kstar K hL (min_le_left _ _) (lt_trans he hK)).mpr
    (min_le_right _ _)

/-! ### The explicit ramp-and-plateau profile -/

/-- Elasticity in the log coordinate `x`: a smoothstep ramp from `e` to `M` over `[0, w]`,
then the plateau `M`. -/
noncomputable def smoothEta (e M w x : ℝ) : ℝ :=
  if x ≤ w then e + (M - e) * (3 * (x / w) ^ 2 - 2 * (x / w) ^ 3) else M

theorem smoothEta_continuous (e M w : ℝ) (hw : w ≠ 0) : Continuous (smoothEta e M w) := by
  apply Continuous.if_le (by fun_prop) continuous_const continuous_id continuous_const
  intro x hx
  dsimp at hx
  subst x
  simp [div_self hw]
  ring

theorem smoothEta_integral (e M w L : ℝ) (hw : 0 < w) (hL : w ≤ L) :
    (∫ x in (0 : ℝ)..L, smoothEta e M w x) = M * (L - w / 2) + e * w / 2 := by
  have hc := smoothEta_continuous e M w hw.ne'
  have ramp : (∫ x in (0 : ℝ)..w, e + (M - e) * (3 * (x / w) ^ 2 - 2 * (x / w) ^ 3)) =
      w * (e + M) / 2 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x (_ : x ∈ uIcc (0 : ℝ) w) => smooth_ramp_primitive_derivative e M w x hw.ne')
      ((by fun_prop : Continuous fun x : ℝ =>
        e + (M - e) * (3 * (x / w) ^ 2 - 2 * (x / w) ^ 3)).intervalIntegrable 0 w)
    rw [h]
    simp [div_self hw.ne']
    ring
  have hleft : (∫ x in (0 : ℝ)..w, smoothEta e M w x) = w * (e + M) / 2 := by
    rw [← ramp]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hw.le] at hx
    simp [smoothEta, hx.2]
  have hright : (∫ x in w..L, smoothEta e M w x) = (L - w) * M := by
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

/-- The endpoint condition `∫₀ᴸ η = A` fixes the plateau uniquely. -/
theorem smoothing_endpoint_unique (e M w L A : ℝ) (hw : 0 < w) (hL : w ≤ L) :
    (∫ x in (0 : ℝ)..L, smoothEta e M w x) = A ↔ M = (A - e * w / 2) / (L - w / 2) := by
  rw [smoothEta_integral e M w L hw hL]
  exact smooth_plateau_unique w e M L A (by linarith : 0 < L - w / 2).ne'

/-- For `e ≤ M` the profile respects a ceiling `K` exactly when the plateau does. -/
theorem smoothEta_ceiling_iff (e M w L K : ℝ) (hw : 0 < w) (hL : w ≤ L) (heM : e ≤ M) :
    (∀ x ∈ Icc (0 : ℝ) L, smoothEta e M w x ≤ K) ↔ M ≤ K := by
  constructor
  · intro hall
    have h := hall w ⟨hw.le, hL⟩
    simp [smoothEta, div_self hw.ne'] at h
    linarith
  · intro hM x hx
    by_cases hxw : x ≤ w
    · have ht : x / w ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hx.1 hw.le, (div_le_one hw).mpr hxw⟩
      have hs := (smoothstep_range _ ht).2
      have hmul := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr heM)
      simp only [smoothEta, if_pos hxw]
      linarith
    · simp only [smoothEta, if_neg hxw]
      exact hM

/-- The width bound `w ≤ 2L (K - K*) / (K - e)`, for the profile whose plateau meets the budget. -/
theorem smoothing_ceiling_width_iff (e w L Kstar K : ℝ) (hL : 0 < L) (hw : 0 < w) (hwL : w ≤ L)
    (he : e < Kstar) (hK : e < K) :
    (∀ x ∈ Icc (0 : ℝ) L, smoothEta e ((Kstar * L - e * w / 2) / (L - w / 2)) w x ≤ K) ↔
      w ≤ 2 * L * (K - Kstar) / (K - e) := by
  rw [smoothEta_ceiling_iff e _ w L K hw hwL
    (lt_trans he (smooth_plateau_above_average w e L Kstar hL hw hwL he)).le]
  exact smooth_width_iff w e L Kstar K hL hwL hK

end SupplierMonotonicity
