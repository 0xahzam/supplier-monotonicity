import SupplierMonotonicity.Core
import Mathlib

noncomputable section
open Set MeasureTheory
open scoped Interval
namespace SupplierMonotonicity

-- E01: Finite deposits on one smooth segment, including endpoints by continuity.
theorem segment_income_nondecreasing (I : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hc : ContinuousOn I (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ I x)
    (hs : ∀ x ∈ Ioo a b, 0 ≤ deriv I x) : I a ≤ I b := by
  have hm : MonotoneOn I (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
    (by simpa only [interior_Icc] using fun x hx => (hd x hx).differentiableWithinAt)
    (by simpa only [interior_Icc] using hs)
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

-- E02: Glue finitely many smooth segments; no derivative required at the knots.
theorem finite_partition_income (I : ℝ → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hp : ∀ i < n, p i ≤ p (i+1))
    (hc : ∀ i < n, ContinuousOn I (Icc (p i) (p (i+1))))
    (hd : ∀ i < n, ∀ x ∈ Ioo (p i) (p (i+1)), DifferentiableAt ℝ I x)
    (hs : ∀ i < n, ∀ x ∈ Ioo (p i) (p (i+1)), 0 ≤ deriv I x) :
    I (p 0) ≤ I (p n) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact le_trans (ih (fun i hi => hp i (Nat.lt_succ_of_lt hi))
      (fun i hi => hc i (Nat.lt_succ_of_lt hi))
      (fun i hi => hd i (Nat.lt_succ_of_lt hi))
      (fun i hi => hs i (Nat.lt_succ_of_lt hi)))
      (segment_income_nondecreasing I _ _ (hp n (Nat.lt_succ_self n))
        (hc n (Nat.lt_succ_self n)) (hd n (Nat.lt_succ_self n))
        (hs n (Nat.lt_succ_self n)))

-- E03: Final ownership bounds earlier ownership during a deposit.
theorem share_nondecreasing (T b x y : ℝ) (hb : b ≤ T)
    (hx : 0 < T+x) (hy : 0 < T+y) (hxy : x ≤ y) :
    share T b x ≤ share T b y := by
  dsimp [share]
  apply (div_le_div_iff₀ hx hy).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hxy)]

-- E04: The envelope protects every smaller nonnegative supplier share, and is necessary.
theorem profile_all_shares_iff (a eta : ℝ) (ha : 0 < a) (he : 0 ≤ eta) :
    (∀ alpha ∈ Icc (0 : ℝ) a, alpha * (1+eta) ≤ 1) ↔ eta ≤ (1-a)/a := by
  rw [← envelope_iff a eta ha]
  constructor
  · intro h; exact h a ⟨ha.le, le_rfl⟩
  · intro h alpha hα
    exact le_trans (mul_le_mul_of_nonneg_right hα.2 (by linarith)) h

-- E05: u0=1 is exactly the worst feasible fresh-depositor start.
theorem fresh_all_starts_iff (u r m : ℝ) (hu : u ≤ 1) (hm : 0 ≤ m) :
    (∀ u0 ∈ Icc u 1, (u0-u)*m ≤ r) ↔ (1-u)*m ≤ r := by
  constructor
  · intro h; exact h 1 ⟨hu, le_rfl⟩
  · intro h u0 h0
    exact le_trans (mul_le_mul_of_nonneg_right (sub_le_sub_right h0.2 u) hm) h

theorem fresh_envelope (u : ℝ) : (1-(1-u))/(1-u) = u/(1-u) := by ring

theorem fresh_envelope_iff (u r m : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hr : 0 < r) : elasticity u r m ≤ u/(1-u) ↔ (1-u)*m ≤ r := by
  dsimp [elasticity]
  rw [div_le_div_iff₀ hr (sub_pos.mpr hu1)]
  constructor <;> intro h <;> nlinarith

theorem envelope_crossing (u K : ℝ) (hu : u < 1) (hK : 0 ≤ K) :
    u/(1-u) ≤ K ↔ u ≤ K/(1+K) := by
  rw [div_le_iff₀ (sub_pos.mpr hu), le_div_iff₀ (by linarith : 0 < 1+K)]
  constructor <;> intro h <;> nlinarith

theorem combined_envelope (e a b : ℝ) : (e ≤ a ∧ e ≤ b) ↔ e ≤ min a b :=
  le_min_iff.symm

-- E09: The left endpoint is sufficient and necessary for a nondecreasing linear segment.
theorem fresh_linear_segment_iff (l h r m : ℝ) (hlh : l ≤ h) (hm : 0 ≤ m) :
    (∀ u ∈ Icc l h, m*(1-u) ≤ r+m*(u-l)) ↔ m*(1-l) ≤ r := by
  constructor
  · intro hall; simpa using hall l ⟨le_rfl, hlh⟩
  · intro hb u hu
    nlinarith [mul_nonneg hm (sub_nonneg.mpr hu.1)]

theorem adjacent_fresh_ratio_iff (l h r s : ℝ)
    (hlh : l < h) (hl : l < 1) (hr : 0 < r) :
    ((s-r)/(h-l))*(1-l) ≤ r ↔ s/r ≤ 1+(h-l)/(1-l) := by
  have hd : 0 < h-l := sub_pos.mpr hlh
  have he : 0 < 1-l := sub_pos.mpr hl
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

-- E11: Affinity of the cross-multiplied constraint gives the two-endpoint test.
theorem fixed_linear_endpoint_suffices (l h u r m K : ℝ)
    (hlh : l < h) (hu : u ∈ Icc l h)
    (hl : l*m ≤ K*r) (hh : h*m ≤ K*(r+m*(h-l))) :
    u*m ≤ K*(r+m*(u-l)) := by
  have h1 := mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hl)
  have h2 := mul_nonneg (sub_nonneg.mpr hu.1) (sub_nonneg.mpr hh)
  have hid : (h-u)*(K*r-l*m)+(u-l)*(K*(r+m*(h-l))-h*m) =
      (h-l)*(K*(r+m*(u-l))-u*m) := by ring
  have hz : 0 ≤ (h-l)*(K*(r+m*(u-l))-u*m) := by rw [← hid]; linarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (sub_pos.mpr hlh)).mp hz)

theorem integer_endpoint_iff (u dr du r K : ℝ) (hd : 0 < du) (hr : 0 < r) :
    u*(dr/du)/r ≤ K ↔ u*dr ≤ K*r*du := by
  rw [div_le_iff₀ hr]
  rw [← mul_div_assoc, div_le_iff₀ hd]

theorem fixed_left_cap_iff (l d r s K : ℝ) (hl : 0 < l) (hr : 0 < r) :
    l*(s-r) ≤ K*r*d ↔ s/r ≤ 1+K*d/l := by
  rw [div_le_iff₀ hr]
  constructor <;> intro H
  · apply (mul_le_mul_iff_of_pos_right hl).mp
    field_simp
    nlinarith
  · have H' := (mul_le_mul_iff_of_pos_right hl).mpr H
    field_simp at H'
    nlinarith

theorem fixed_right_cap_iff (h d r s K : ℝ) (hr : 0 < r)
    (hd : 0 < h-K*d) :
    h*(s-r) ≤ K*s*d ↔ s/r ≤ h/(h-K*d) := by
  rw [div_le_div_iff₀ hr hd]
  constructor <;> intro H <;> nlinarith

-- E15: The local steps underlying backwards floor/majorant and forward minorant.
theorem backward_floor_bound (c next r : ℝ) (hc : 0 < c)
    (h : next ≤ c*r) : next/c ≤ r := (div_le_iff₀ hc).mpr (by nlinarith)

theorem raise_step_minimal (base next c r : ℝ) (hc : 0 < c)
    (hb : base ≤ r) (hn : next ≤ c*r) : max base (next/c) ≤ r :=
  max_le hb (backward_floor_bound c next r hc hn)

theorem raise_step_feasible (base next c : ℝ) (hc : 1 ≤ c)
    (hn : 0 ≤ next) (hb : base ≤ next) :
    base ≤ max base (next/c) ∧ max base (next/c) ≤ next ∧
      next ≤ c * max base (next/c) := by
  have hc0 : 0 < c := by linarith
  refine ⟨le_max_left _ _, max_le hb ?_, ?_⟩
  · apply (div_le_iff₀ hc0).mpr
    nlinarith
  · have := le_max_right base (next/c)
    have := (div_le_iff₀ hc0).mp this
    nlinarith

theorem lower_step_maximal (base prev c r : ℝ)
    (hb : r ≤ base) (hc : r ≤ c*prev) : r ≤ min base (c*prev) := le_min hb hc

-- E19: The smoothing-area identity.
theorem smooth_area_identity (w e M L : ℝ) :
    w*(e+M)/2 + M*(L-w) = M*(L-w/2)+e*w/2 := by ring

theorem smooth_plateau_unique (w e M L A : ℝ) (hd : L-w/2 ≠ 0) :
    M*(L-w/2)+e*w/2 = A ↔ M = (A-e*w/2)/(L-w/2) := by
  rw [eq_div_iff hd]
  constructor <;> intro h <;> linarith

theorem smooth_width_iff (w e L Kstar K : ℝ)
    (hL : 0 < L) (hw : w ≤ L) (hK : e < K) :
    (Kstar*L-e*w/2)/(L-w/2) ≤ K ↔ w ≤ 2*L*(K-Kstar)/(K-e) := by
  rw [div_le_iff₀ (by linarith : 0 < L-w/2), le_div_iff₀ (sub_pos.mpr hK)]
  constructor <;> intro h <;> nlinarith

theorem smooth_plateau_above_average (w e L Kstar : ℝ)
    (hL : 0 < L) (hw : 0 < w) (hwL : w ≤ L) (he : e < Kstar) :
    Kstar < (Kstar*L-e*w/2)/(L-w/2) := by
  rw [lt_div_iff₀ (by linarith : 0 < L-w/2)]
  nlinarith [mul_pos hw (sub_pos.mpr he)]

theorem smooth_plateau_derivative (L e Kstar w : ℝ) (hd : L-w/2 ≠ 0) :
    HasDerivAt (fun w : ℝ => (Kstar*L-e*w/2)/(L-w/2))
      (L*(Kstar-e)/(2*(L-w/2)^2)) w := by
  have hn := (hasDerivAt_const w (Kstar*L)).sub
    (((hasDerivAt_id w).const_mul e).div_const 2)
  have hh := (hasDerivAt_const w L).sub ((hasDerivAt_id w).div_const 2)
  convert hn.div hh hd using 1
  dsimp
  field_simp
  ring


-- E25: Full supplier derivative follows from the actual income function.
theorem full_supplier_deriv (R : ℝ → ℝ) (B T x slope : ℝ)
    (hT : T+x ≠ 0) (hR : HasDerivAt R slope (utilization B T x)) :
    HasDerivAt (income R B T T) (-(utilization B T x)^2*slope) x := by
  convert income_hasDerivAt_raw R B T T x slope hT hR using 1
  dsimp [utilization]
  field_simp
  ring

-- E26: Conventional precise meaning of d log R / d log U: use x=log U.
theorem logarithmic_elasticity (R : ℝ → ℝ) (x slope : ℝ)
    (hR : HasDerivAt R slope (Real.exp x)) (hr : R (Real.exp x) ≠ 0) :
    HasDerivAt (fun x => Real.log (R (Real.exp x)))
      (elasticity (Real.exp x) (R (Real.exp x)) slope) x := by
  convert (hR.comp x (Real.hasDerivAt_exp x)).log hr using 1
  dsimp [elasticity]
  ring

-- E27: The integral budget implies the endpoint ceiling, in logarithmic coordinates.
-- The identity connecting R to this budget is a separate obligation for AC curves.
theorem endpoint_budget_bound (eta : ℝ → ℝ) (L A K : ℝ) (hL : 0 < L)
    (hi : IntervalIntegrable eta volume 0 L)
    (hb : ∀ x ∈ Icc (0 : ℝ) L, eta x ≤ K)
    (ha : (∫ x in (0 : ℝ)..L, eta x) = A) : A/L ≤ K := by
  have h := intervalIntegral.integral_mono_on hL.le hi intervalIntegrable_const hb
  rw [ha, intervalIntegral.integral_const] at h
  simp only [sub_zero, smul_eq_mul] at h
  apply (div_le_iff₀ hL).mpr
  nlinarith

-- E28: Continuous elasticity starting below its prescribed average must exceed it.
theorem continuous_elasticity_overshoot (eta : ℝ → ℝ) (L Kstar : ℝ)
    (hL : 0 < L) (hc : ContinuousOn eta (Icc 0 L))
    (h0 : eta 0 < Kstar)
    (ha : (∫ x in (0 : ℝ)..L, eta x) = Kstar*L) :
    ∃ x ∈ Icc (0 : ℝ) L, Kstar < eta x := by
  by_contra h
  push_neg at h
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hL hc continuousOn_const (fun x hx => h x ⟨hx.1.le,hx.2⟩)
    ⟨0, ⟨le_rfl,hL.le⟩, h0⟩
  rw [ha, intervalIntegral.integral_const] at hi
  simp only [sub_zero, smul_eq_mul] at hi
  nlinarith

-- E29: Income comparison under prescribed integrable histories.
theorem accumulated_interest_order (I J : ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hI : IntervalIntegrable I volume 0 H) (hJ : IntervalIntegrable J volume 0 H)
    (h : ∀ t ∈ Icc (0 : ℝ) H, I t ≤ J t) :
    (∫ t in (0 : ℝ)..H, I t) ≤ ∫ t in (0 : ℝ)..H, J t :=
  intervalIntegral.integral_mono_on hH hI hJ h

theorem accumulated_interest_difference (I J : ℝ → ℝ) (H : ℝ)
    (hI : IntervalIntegrable I volume 0 H) (hJ : IntervalIntegrable J volume 0 H) :
    (∫ t in (0 : ℝ)..H, J t) - (∫ t in (0 : ℝ)..H, I t) =
    ∫ t in (0 : ℝ)..H, J t-I t := (intervalIntegral.integral_sub hJ hI).symm

theorem rate_order_income_order (b u f r s : ℝ)
    (hb : 0 ≤ b) (hu : 0 ≤ u) (hf : f ≤ 1) (hrs : r ≤ s) :
    (1-f)*b*u*r ≤ (1-f)*b*u*s :=
  mul_le_mul_of_nonneg_left hrs (mul_nonneg (mul_nonneg (sub_nonneg.mpr hf) hb) hu)

end SupplierMonotonicity
