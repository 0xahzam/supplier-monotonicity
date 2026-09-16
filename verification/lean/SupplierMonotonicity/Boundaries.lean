import SupplierMonotonicity.Extended

noncomputable section
open Set MeasureTheory
namespace SupplierMonotonicity

-- B01: Smooth logarithmic growth bound. This is NOT the paper's more general
-- locally absolutely continuous / a.e. theorem; that obligation stays separate.
theorem smooth_log_growth (R : ℝ → ℝ) (a b K : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hc : ContinuousOn R (Icc a b))
    (hr : ∀ u ∈ Icc a b, 0 < R u)
    (hd : ∀ u ∈ Ioo a b, DifferentiableAt ℝ R u)
    (he : ∀ u ∈ Ioo a b, elasticity u (R u) (deriv R u) ≤ K) :
    Real.log (R b) - Real.log (R a) ≤ K*(Real.log b - Real.log a) := by
  let F := fun u => Real.log (R u)-K*Real.log u
  have hcont : ContinuousOn F (Icc a b) :=
    (hc.log (fun u hu => ne_of_gt (hr u hu))).sub
      (continuousOn_const.mul ((continuousOn_id : ContinuousOn (fun u : ℝ => u) (Icc a b)).log
        (fun u hu => ne_of_gt (lt_of_lt_of_le ha hu.1))))
  have hder : ∀ u ∈ Ioo a b, HasDerivAt F
      (deriv R u / R u - K/u) u := by
    intro u hu
    convert ((hd u hu).hasDerivAt.log (ne_of_gt (hr u ⟨hu.1.le,hu.2.le⟩))).sub
      ((Real.hasDerivAt_log (ne_of_gt (lt_trans ha hu.1))).const_mul K) using 1
  have hs : ∀ u ∈ Ioo a b, deriv F u ≤ 0 := by
    intro u hu
    rw [(hder u hu).deriv]
    have hu0 : 0 < u := lt_trans ha hu.1
    have hr0 := hr u ⟨hu.1.le,hu.2.le⟩
    have hh := he u hu
    dsimp [elasticity] at hh
    have hcross := (div_le_iff₀ hr0).mp hh
    have hq : deriv R u / R u ≤ K/u := by
      rw [div_le_div_iff₀ hr0 hu0]
      nlinarith
    linarith
  have hm : AntitoneOn F (Icc a b) := antitoneOn_of_deriv_nonpos (convex_Icc a b)
    hcont (by simpa only [interior_Icc] using
      fun u hu => (hder u hu).differentiableAt.differentiableWithinAt)
    (by simpa only [interior_Icc] using hs)
  have hh := hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  dsimp [F] at hh
  linarith

theorem smooth_endpoint_bound (R : ℝ → ℝ) (O K : ℝ)
    (hO : 0 < O) (hO1 : O < 1) (hc : ContinuousOn R (Icc O 1))
    (hr : ∀ u ∈ Icc O 1, 0 < R u)
    (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (he : ∀ u ∈ Ioo O 1, elasticity u (R u) (deriv R u) ≤ K) :
    Real.log (R 1 / R O) / Real.log (1/O) ≤ K := by
  have h := smooth_log_growth R O 1 K hO hO1.le hc hr hd he
  have hlog : 0 < Real.log (1/O) := Real.log_pos ((one_lt_div hO).mpr hO1)
  apply (div_le_iff₀ hlog).mpr
  rw [Real.log_div (ne_of_gt (hr 1 ⟨hO1.le,le_rfl⟩))
    (ne_of_gt (hr O ⟨le_rfl,hO1.le⟩))]
  rw [Real.log_div one_ne_zero hO.ne', Real.log_one]
  simpa only [Real.log_one] using h

-- B03: Power boundary, written exp(K log(U/O)) to avoid notation ambiguity.
theorem power_boundary_derivative (O r K u : ℝ) (hu : 0 < u) (hO : 0 < O) :
    HasDerivAt (fun v => r * Real.exp (K * Real.log (v/O)))
      (K*(r*Real.exp (K*Real.log (u/O)))/u) u := by
  have h := (((((hasDerivAt_id u).div_const O).log
    (ne_of_gt (div_pos hu hO))).const_mul K).exp).const_mul r
  convert h using 1
  dsimp
  field_simp

theorem power_boundary_elasticity (O r K u : ℝ) (hu : 0 < u)
    (hO : 0 < O) (hr : 0 < r) :
    elasticity u (r*Real.exp (K*Real.log (u/O)))
      (deriv (fun v => r*Real.exp (K*Real.log (v/O))) u) = K := by
  rw [(power_boundary_derivative O r K u hu hO).deriv]
  dsimp [elasticity]
  field_simp

theorem power_exp_matches_rpow (O r K u : ℝ) (hu : 0 < u) (hO : 0 < O) :
    r*Real.exp (K*Real.log (u/O)) = r*(u/O)^K := by
  rw [Real.rpow_def_of_pos (div_pos hu hO)]
  rw [mul_comm K]

theorem power_hits_top (O r top : ℝ) (hO : 0 < O) (hO1 : O < 1)
    (hr : 0 < r) (ht : 0 < top) :
    r*Real.exp ((Real.log (top/r)/Real.log (1/O))*Real.log (1/O)) = top := by
  have hlog : Real.log (1/O) ≠ 0 := ne_of_gt (Real.log_pos ((one_lt_div hO).mpr hO1))
  rw [div_mul_cancel₀ _ hlog, Real.exp_log (div_pos ht hr)]
  field_simp

theorem hyperbolic_boundary_derivative (c u : ℝ) (hu : u ≠ 1) :
    HasDerivAt (fun v => c/(1-v)) (c/(1-u)^2) u := by
  have hn : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  convert (hasDerivAt_const u c).div ((hasDerivAt_const u 1).sub (hasDerivAt_id u)) hn using 1
  dsimp
  ring

theorem hyperbolic_boundary_elasticity (c u : ℝ) (hc : c ≠ 0) (hu : u ≠ 1) :
    elasticity u (c/(1-u)) (c/(1-u)^2) = u/(1-u) := by
  have hn : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  dsimp [elasticity]
  field_simp

theorem fresh_boundary_income_algebra (c u u0 : ℝ)
    (hc : c ≠ 0) (hu : u ≠ 1) (hu0 : u0 ≠ 0) :
    u*(c/(1-u))*(1-(1-u/u0)*(1+elasticity u (c/(1-u)) (c/(1-u)^2))) =
      c*u^2*(1-u0)/(u0*(1-u)^2) := by
  have hn : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  rw [hyperbolic_boundary_elasticity c u hc hu]
  field_simp
  ring

theorem fresh_base_positive (r0 r u : ℝ) (hr : 0 < r) (hu : u < 1)
    (hb : r*(1-u) ≤ r0) : 0 < r0 := lt_of_lt_of_le (mul_pos hr (sub_pos.mpr hu)) hb

-- B11: Uniform repricing affects levels, not percentage elasticity.
theorem scaled_elasticity (u r m c : ℝ) (hc : c ≠ 0) :
    elasticity u (c*r) (c*m) = elasticity u r m := by
  dsimp [elasticity]
  field_simp

-- B12: Smoothstep polynomial and its primitive, including endpoint data.
theorem smoothstep_primitive_derivative (t : ℝ) :
    HasDerivAt (fun t : ℝ => t^3-t^4/2) (3*t^2-2*t^3) t := by
  convert ((hasDerivAt_pow 3 t).sub ((hasDerivAt_pow 4 t).div_const 2)) using 1
  ring

theorem smoothstep_derivative (t : ℝ) :
    HasDerivAt (fun t : ℝ => 3*t^2-2*t^3) (6*t-6*t^2) t := by
  convert ((hasDerivAt_pow 2 t).const_mul 3).sub ((hasDerivAt_pow 3 t).const_mul 2) using 1
  ring

theorem smoothstep_endpoint_values :
    (3*(0:ℝ)^2-2*0^3=0) ∧ (3*(1:ℝ)^2-2*1^3=1) ∧
    (6*(0:ℝ)-6*0^2=0) ∧ (6*(1:ℝ)-6*1^2=0) := by norm_num

theorem smoothstep_range (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    0 ≤ 3*t^2-2*t^3 ∧ 3*t^2-2*t^3 ≤ 1 := by
  constructor
  · nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 3-2*t by linarith [ht.2])]
  · nlinarith [mul_nonneg (sq_nonneg (1-t)) (show 0 ≤ 1+2*t by linarith [ht.1])]

theorem smoothstep_integral : (∫ t in (0:ℝ)..1, 3*t^2-2*t^3) = 1/2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ Set.uIcc (0:ℝ) 1) => smoothstep_primitive_derivative t)
    (show IntervalIntegrable (fun t : ℝ => 3*t^2-2*t^3) volume 0 1 from
      (by fun_prop : Continuous (fun t : ℝ => 3*t^2-2*t^3)).intervalIntegrable 0 1)
  norm_num at h ⊢

-- B17: The explicit antiderivative branches meet at w with the right slope.
theorem smooth_primitive_join (e M w : ℝ) (hw : w ≠ 0) :
    e*w+(M-e)*w*((w/w)^3-(w/w)^4/2) = w*(e+M)/2+M*(w-w) := by
  field_simp
  ring

theorem smooth_ramp_primitive_derivative (e M w x : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun x : ℝ => e*x+(M-e)*w*((x/w)^3-(x/w)^4/2))
      (e+(M-e)*(3*(x/w)^2-2*(x/w)^3)) x := by
  have h := ((hasDerivAt_id x).const_mul e).add
    (((smoothstep_primitive_derivative (x/w)).comp x ((hasDerivAt_id x).div_const w)).const_mul ((M-e)*w))
  convert h using 1
  dsimp
  field_simp

end SupplierMonotonicity
