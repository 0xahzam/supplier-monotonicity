import SupplierMonotonicity.Model

/-!
# Fixed supplier share protection and the endpoint bound

The power-law boundary curve for a constant elasticity ceiling `K`, and the endpoint
impossibility bound `K* = log (R_max / R_o) / log (1 / O)` (paper, Section 6).

The bound is proved for rates that are continuous on `[O, 1]` and differentiable inside, with a
pointwise elasticity ceiling. The paper's Theorem 3 is stated for absolutely continuous rates and
the essential supremum. That version is **not** formalized.

The power law is written `r · exp (K · log (u / O))` to avoid ambiguity in real powers;
`power_exp_matches_rpow` connects it to `r · (u / O) ^ K`.
-/

namespace SupplierMonotonicity

open Set MeasureTheory

/-! ### Logarithmic integrals -/

/-- `∫ₐᵇ R' / R = log (R b / R a)` for a positive rate, differentiable inside `[a, b]`. -/
theorem log_rate_integral_on (R : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn R (Icc a b)) (hp : ∀ u ∈ Icc a b, 0 < R u)
    (hd : ∀ u ∈ Ioo a b, DifferentiableAt ℝ R u)
    (hi : IntervalIntegrable (fun u => deriv R u / R u) volume a b) :
    (∫ u in a..b, deriv R u / R u) = Real.log (R b / R a) := by
  rw [Real.log_div (hp b ⟨hab, le_rfl⟩).ne' (hp a ⟨le_rfl, hab⟩).ne']
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hc.log fun x hx => (hp x hx).ne')
    (fun x hx => (hd x hx).hasDerivAt.log (hp x ⟨hx.1.le, hx.2.le⟩).ne') hi

/-- `∫ₐᵇ K / u = K · log (b / a)`. -/
theorem log_budget_integral (a b K : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, K / u) = K * Real.log (b / a) := by
  have hpos : ∀ u ∈ Icc a b, u ≠ 0 := fun u hu => (lt_of_lt_of_le ha hu.1).ne'
  have hc : ContinuousOn (fun u : ℝ => K / u) (Icc a b) :=
    continuousOn_const.div continuousOn_id hpos
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_const.mul
      ((continuousOn_id : ContinuousOn (fun u : ℝ => u) (Icc a b)).log hpos))
    (fun u (hu : u ∈ Ioo a b) => by
      convert (Real.hasDerivAt_log (lt_trans ha hu.1).ne').const_mul K using 1)
    (hc.intervalIntegrable_of_Icc hab)
  rw [Real.log_div (lt_of_lt_of_le ha hab).ne' ha.ne']
  simpa [id_eq, mul_sub] using h

/-! ### Endpoint impossibility bound -/

/-- An elasticity ceiling `K` on `(a, b)` limits log-growth:
`log R(b) - log R(a) ≤ K (log b - log a)`. -/
theorem smooth_log_growth (R : ℝ → ℝ) (a b K : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hc : ContinuousOn R (Icc a b)) (hr : ∀ u ∈ Icc a b, 0 < R u)
    (hd : ∀ u ∈ Ioo a b, DifferentiableAt ℝ R u)
    (he : ∀ u ∈ Ioo a b, elasticity u (R u) (deriv R u) ≤ K) :
    Real.log (R b) - Real.log (R a) ≤ K * (Real.log b - Real.log a) := by
  let F := fun u => Real.log (R u) - K * Real.log u
  have hcont : ContinuousOn F (Icc a b) :=
    (hc.log fun u hu => (hr u hu).ne').sub
      (continuousOn_const.mul ((continuousOn_id : ContinuousOn (fun u : ℝ => u) (Icc a b)).log
        fun u hu => (lt_of_lt_of_le ha hu.1).ne'))
  have hder : ∀ u ∈ Ioo a b, HasDerivAt F (deriv R u / R u - K / u) u := by
    intro u hu
    convert ((hd u hu).hasDerivAt.log (hr u ⟨hu.1.le, hu.2.le⟩).ne').sub
      ((Real.hasDerivAt_log (lt_trans ha hu.1).ne').const_mul K) using 1
  have hs : ∀ u ∈ Ioo a b, deriv F u ≤ 0 := by
    intro u hu
    rw [(hder u hu).deriv]
    have hu0 : 0 < u := lt_trans ha hu.1
    have hr0 := hr u ⟨hu.1.le, hu.2.le⟩
    have hh := he u hu
    dsimp [elasticity] at hh
    have hcross := (div_le_iff₀ hr0).mp hh
    have hq : deriv R u / R u ≤ K / u := by
      rw [div_le_div_iff₀ hr0 hu0]
      nlinarith
    linarith
  have hm : AntitoneOn F (Icc a b) := antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont
    (by simpa only [interior_Icc] using
      fun u hu => (hder u hu).differentiableAt.differentiableWithinAt)
    (by simpa only [interior_Icc] using hs)
  have hh := hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  dsimp [F] at hh
  linarith

/-- Smooth endpoint bound: any elasticity ceiling `K` on `(O, 1)` is at least
`log (R 1 / R O) / log (1 / O)`. -/
theorem smooth_endpoint_bound (R : ℝ → ℝ) (O K : ℝ) (hO : 0 < O) (hO1 : O < 1)
    (hc : ContinuousOn R (Icc O 1)) (hr : ∀ u ∈ Icc O 1, 0 < R u)
    (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (he : ∀ u ∈ Ioo O 1, elasticity u (R u) (deriv R u) ≤ K) :
    Real.log (R 1 / R O) / Real.log (1 / O) ≤ K := by
  have h := smooth_log_growth R O 1 K hO hO1.le hc hr hd he
  have hlog : 0 < Real.log (1 / O) := Real.log_pos ((one_lt_div hO).mpr hO1)
  apply (div_le_iff₀ hlog).mpr
  rw [Real.log_div (hr 1 ⟨hO1.le, le_rfl⟩).ne' (hr O ⟨le_rfl, hO1.le⟩).ne',
    Real.log_div one_ne_zero hO.ne', Real.log_one]
  simpa only [Real.log_one] using h

/-- The same bound in the log coordinate, from an integral budget `∫₀ᴸ η = A`. -/
theorem endpoint_budget_bound (eta : ℝ → ℝ) (L A K : ℝ) (hL : 0 < L)
    (hi : IntervalIntegrable eta volume 0 L)
    (hb : ∀ x ∈ Icc (0 : ℝ) L, eta x ≤ K)
    (ha : (∫ x in (0 : ℝ)..L, eta x) = A) : A / L ≤ K := by
  have h := intervalIntegral.integral_mono_on hL.le hi intervalIntegrable_const hb
  rw [ha, intervalIntegral.integral_const] at h
  simp only [sub_zero, smul_eq_mul] at h
  apply (div_le_iff₀ hL).mpr
  nlinarith

/-! ### The power-law boundary curve -/

theorem power_boundary_derivative (O r K u : ℝ) (hu : 0 < u) (hO : 0 < O) :
    HasDerivAt (fun v => r * Real.exp (K * Real.log (v / O)))
      (K * (r * Real.exp (K * Real.log (u / O))) / u) u := by
  have h := (((((hasDerivAt_id u).div_const O).log
    (div_pos hu hO).ne').const_mul K).exp).const_mul r
  convert h using 1
  dsimp
  field_simp

/-- The power law has constant elasticity `K`. -/
theorem power_boundary_elasticity (O r K u : ℝ) (hu : 0 < u) (hO : 0 < O) (hr : 0 < r) :
    elasticity u (r * Real.exp (K * Real.log (u / O)))
      (deriv (fun v => r * Real.exp (K * Real.log (v / O))) u) = K := by
  rw [(power_boundary_derivative O r K u hu hO).deriv]
  dsimp [elasticity]
  field_simp

theorem power_exp_matches_rpow (O r K u : ℝ) (hu : 0 < u) (hO : 0 < O) :
    r * Real.exp (K * Real.log (u / O)) = r * (u / O) ^ K := by
  rw [Real.rpow_def_of_pos (div_pos hu hO), mul_comm K]

/-- Tightness: the power law with `K = K*` reaches `top` exactly at `u = 1`. -/
theorem power_hits_top (O r top : ℝ) (hO : 0 < O) (hO1 : O < 1) (hr : 0 < r) (ht : 0 < top) :
    r * Real.exp ((Real.log (top / r) / Real.log (1 / O)) * Real.log (1 / O)) = top := by
  have hlog : Real.log (1 / O) ≠ 0 := (Real.log_pos ((one_lt_div hO).mpr hO1)).ne'
  rw [div_mul_cancel₀ _ hlog, Real.exp_log (div_pos ht hr)]
  field_simp

end SupplierMonotonicity
