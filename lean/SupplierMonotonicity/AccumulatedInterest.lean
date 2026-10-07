import SupplierMonotonicity.Model

/-!
# Income levels and accumulated interest

Comparing accumulated interest under two prescribed, integrable income histories, and how a rate
order becomes an income order (paper, Section 10 and Appendix C). Borrowing paths are taken as
given; they are not derived from the rate curve.
-/

namespace SupplierMonotonicity

open Set MeasureTheory

theorem accumulated_interest_order (I J : ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hI : IntervalIntegrable I volume 0 H) (hJ : IntervalIntegrable J volume 0 H)
    (h : ∀ t ∈ Icc (0 : ℝ) H, I t ≤ J t) :
    (∫ t in (0 : ℝ)..H, I t) ≤ ∫ t in (0 : ℝ)..H, J t :=
  intervalIntegral.integral_mono_on hH hI hJ h

theorem accumulated_interest_difference (I J : ℝ → ℝ) (H : ℝ)
    (hI : IntervalIntegrable I volume 0 H) (hJ : IntervalIntegrable J volume 0 H) :
    (∫ t in (0 : ℝ)..H, J t) - (∫ t in (0 : ℝ)..H, I t) = ∫ t in (0 : ℝ)..H, J t - I t :=
  (intervalIntegral.integral_sub hJ hI).symm

/-- With the same balance, utilization and reserve factor, a higher rate earns more. -/
theorem rate_order_income_order (b u f r s : ℝ) (hb : 0 ≤ b) (hu : 0 ≤ u) (hf : f ≤ 1)
    (hrs : r ≤ s) : (1 - f) * b * u * r ≤ (1 - f) * b * u * s :=
  mul_le_mul_of_nonneg_left hrs (mul_nonneg (mul_nonneg (sub_nonneg.mpr hf) hb) hu)

/-- The income transfer to a supplier holding `b` of `T` when the rate moves from `r` to `s`:
`(1 - f) · b · (B / T) · (s - r) = (1 - f) · (b / T) · (B s - B r)`. -/
theorem supplier_transfer (b T B r s f : ℝ) :
    (1 - f) * b * (B / T) * (s - r) = (1 - f) * (b / T) * (B * s - B * r) := by
  ring

end SupplierMonotonicity
