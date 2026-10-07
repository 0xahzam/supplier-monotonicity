import Mathlib

/-!
# The lending-pool model

Definitions shared by every other module (paper, Section 3).

A supplier holds `b` of a pool with total supply `T` and fixed borrowings `B`, then deposits
`x`. After the deposit the pool supply is `T + x` and the supplier holds `b + x`, so the paper's
resulting-state `T` and `b` are `T + x` and `b + x` here. `B` stays constant as `x` varies.
The borrow rate is an arbitrary real function `R` of utilization.

All quantities are real numbers. Lean defines division by zero as zero, so every theorem that
divides states its own positivity or nonzero hypotheses.
-/

namespace SupplierMonotonicity

noncomputable section

/-- Utilization after depositing `x`: `U = B / (T + x)`. -/
def utilization (B T x : ℝ) : ℝ := B / (T + x)

/-- Supplier income rate after depositing `x`: `I = (b + x) · U · R(U)`. -/
def income (R : ℝ → ℝ) (B T b x : ℝ) : ℝ :=
  (b + x) * utilization B T x * R (utilization B T x)

/-- Supplier share of the pool after depositing `x`: `α = (b + x) / (T + x)`. -/
def share (T b x : ℝ) : ℝ := (b + x) / (T + x)

/-- Elasticity of the rate at utilization `U`, given the rate `rate = R(U)` and the slope
`slope = R'(U)`: `η = U · R'(U) / R(U)`. -/
def elasticity (U rate slope : ℝ) : ℝ := U * slope / rate

/-- The endpoint elasticity `K* = log (R_max / R_o) / log (1 / O)` of a curve from `(O, R_o)` to
`(1, R_max)` (paper, Section 6.1). -/
def kStar (O Ro Rmax : ℝ) : ℝ := Real.log (Rmax / Ro) / Real.log (1 / O)

end

end SupplierMonotonicity
