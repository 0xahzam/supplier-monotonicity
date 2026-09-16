import SupplierMonotonicity.Smoothing

noncomputable section
open Set MeasureTheory
namespace SupplierMonotonicity

theorem log_rate_integral_on (R : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn R (Icc a b)) (hp : ∀ u ∈ Icc a b, 0 < R u)
    (hd : ∀ u ∈ Ioo a b, DifferentiableAt ℝ R u)
    (hi : IntervalIntegrable (fun u => deriv R u/R u) volume a b) :
    (∫ u in a..b, deriv R u/R u) = Real.log (R b/R a) := by
  rw [Real.log_div (hp b ⟨hab,le_rfl⟩).ne' (hp a ⟨le_rfl,hab⟩).ne']
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (hc.log (fun x hx => (hp x hx).ne'))
    (fun x hx => (hd x hx).hasDerivAt.log (hp x ⟨hx.1.le,hx.2.le⟩).ne') hi

theorem log_budget_integral (a b K : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ u in a..b, K/u) = K*Real.log (b/a) := by
  have hc : ContinuousOn (fun u : ℝ => K/u) (Icc a b) :=
    continuousOn_const.div continuousOn_id (fun u hu => (lt_of_lt_of_le ha hu.1).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (continuousOn_const.mul ((continuousOn_id : ContinuousOn (fun u : ℝ => u) (Icc a b)).log
      (fun u hu => (lt_of_lt_of_le ha hu.1).ne')))
    (fun u (hu : u ∈ Ioo a b) => by
      convert (Real.hasDerivAt_log (lt_trans ha hu.1).ne').const_mul K using 1)
    (hc.intervalIntegrable_of_Icc hab)
  rw [Real.log_div (lt_of_lt_of_le ha hab).ne' ha.ne']
  simpa [id_eq,mul_sub] using h

-- Direct version of the strict C1 obstruction in U coordinates.
-- The quotient-continuity premise follows from a continuous rate derivative
-- and positive rate; it is explicit rather than hidden in a C1 notation convention.
theorem continuous_rate_overshoot (R : ℝ → ℝ) (O Kstar : ℝ)
    (hO : 0 < O) (hO1 : O < 1)
    (hc : ContinuousOn R (Icc O 1)) (hp : ∀ u ∈ Icc O 1, 0 < R u)
    (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (hq : ContinuousOn (fun u => deriv R u/R u) (Icc O 1))
    (hstart : elasticity O (R O) (deriv R O) < Kstar)
    (hbudget : Real.log (R 1/R O) = Kstar*Real.log (1/O)) :
    ∃ u ∈ Icc O 1, Kstar < elasticity u (R u) (deriv R u) := by
  by_contra hall
  push_neg at hall
  have hbcont : ContinuousOn (fun u : ℝ => Kstar/u) (Icc O 1) :=
    continuousOn_const.div continuousOn_id (fun u hu => (lt_of_lt_of_le hO hu.1).ne')
  have hle : ∀ u ∈ Ioc O 1, deriv R u/R u ≤ Kstar/u := by
    intro u hu
    have hr := hp u ⟨hu.1.le,hu.2⟩
    have hu0 := lt_trans hO hu.1
    have hh := hall u ⟨hu.1.le,hu.2⟩
    dsimp [elasticity] at hh
    rw [div_le_iff₀ hr] at hh
    rw [div_le_div_iff₀ hr hu0]
    nlinarith
  have hlt : deriv R O/R O < Kstar/O := by
    have hr := hp O ⟨le_rfl,hO1.le⟩
    dsimp [elasticity] at hstart
    rw [div_lt_iff₀ hr] at hstart
    rw [div_lt_div_iff₀ hr hO]
    nlinarith
  have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hO1 hq hbcont hle ⟨O,⟨le_rfl,hO1.le⟩,hlt⟩
  rw [log_rate_integral_on R O 1 hO1.le hc hp hd (hq.intervalIntegrable_of_Icc hO1.le),
    log_budget_integral O 1 Kstar hO hO1.le,hbudget] at hi
  exact (lt_irrefl _ hi)

theorem continuous_rate_supremum_strict (R : ℝ → ℝ) (O Kstar : ℝ)
    (hO : 0 < O) (hO1 : O < 1)
    (hc : ContinuousOn R (Icc O 1)) (hp : ∀ u ∈ Icc O 1, 0 < R u)
    (hd : ∀ u ∈ Ioo O 1, DifferentiableAt ℝ R u)
    (hq : ContinuousOn (fun u => deriv R u/R u) (Icc O 1))
    (hstart : elasticity O (R O) (deriv R O) < Kstar)
    (hbudget : Real.log (R 1/R O) = Kstar*Real.log (1/O)) :
    Kstar < sSup ((fun u => elasticity u (R u) (deriv R u)) '' Icc O 1) := by
  obtain ⟨u,hu,hgt⟩ := continuous_rate_overshoot R O Kstar hO hO1 hc hp hd hq hstart hbudget
  have he : ContinuousOn (fun u => elasticity u (R u) (deriv R u)) (Icc O 1) := by
    simpa [elasticity,mul_div_assoc] using (continuousOn_id.mul hq)
  have hb := (isCompact_Icc.image_of_continuousOn he).bddAbove
  exact lt_of_lt_of_le hgt (le_csSup hb ⟨u,hu,rfl⟩)

theorem continuous_quotient_of_C1_data (R : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn R (Icc a b)) (hd : ContinuousOn (deriv R) (Icc a b))
    (hp : ∀ u ∈ Icc a b, 0 < R u) :
    ContinuousOn (fun u => deriv R u/R u) (Icc a b) :=
  hd.div hc (fun u hu => (hp u hu).ne')

end SupplierMonotonicity
