import SupplierMonotonicity.MarginalIncome

/-!
# Finite deposits across kinks

A finite deposit can cross kinks where the rate curve has no derivative. These results glue the
smooth-segment sign condition across an arbitrary finite partition (paper, Sections 4 and 7).
Income only needs to be continuous at the kinks, and no derivative is required there.
`withdrawal_raises_income` is the reverse: where `α (1 + η) > 1` throughout, withdrawing
strictly raises income (paper, Sections 2 and 4).

Not covered here: countably many kinks, and the one-sided derivative at a kink.
-/

namespace SupplierMonotonicity

open Set

/-- On one smooth segment, a nonnegative derivative inside gives `I a ≤ I b`. -/
theorem segment_income_nondecreasing (I : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn I (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ I x)
    (hs : ∀ x ∈ Ioo a b, 0 ≤ deriv I x) : I a ≤ I b := by
  have hm : MonotoneOn I (Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
    (by simpa only [interior_Icc] using fun x hx => (hd x hx).differentiableWithinAt)
    (by simpa only [interior_Icc] using hs)
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Glue finitely many smooth segments `[p i, p (i + 1)]`. -/
theorem finite_partition_income (I : ℝ → ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hp : ∀ i < n, p i ≤ p (i + 1))
    (hc : ∀ i < n, ContinuousOn I (Icc (p i) (p (i + 1))))
    (hd : ∀ i < n, ∀ x ∈ Ioo (p i) (p (i + 1)), DifferentiableAt ℝ I x)
    (hs : ∀ i < n, ∀ x ∈ Ioo (p i) (p (i + 1)), 0 ≤ deriv I x) :
    I (p 0) ≤ I (p n) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact le_trans
      (ih (fun i hi => hp i (Nat.lt_succ_of_lt hi)) (fun i hi => hc i (Nat.lt_succ_of_lt hi))
        (fun i hi => hd i (Nat.lt_succ_of_lt hi)) (fun i hi => hs i (Nat.lt_succ_of_lt hi)))
      (segment_income_nondecreasing I _ _ (hp n n.lt_succ_self) (hc n n.lt_succ_self)
        (hd n n.lt_succ_self) (hs n n.lt_succ_self))

/-- The supplier's share only grows during a deposit, so the final share bounds every
intermediate one. -/
theorem share_nondecreasing (T b x y : ℝ) (hb : b ≤ T) (hx : 0 < T + x) (hy : 0 < T + y)
    (hxy : x ≤ y) : share T b x ≤ share T b y := by
  dsimp [share]
  apply (div_le_div_iff₀ hx hy).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hxy)]

/-- A finite deposit does not lower income if the sign condition holds on the interior of every
piece of a finite partition and income is continuous on each closed piece. -/
theorem finite_supplier_deposit (R : ℝ → ℝ) (B T b : ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hB : 0 < B) (hp : ∀ i < n, p i ≤ p (i + 1))
    (hc : ∀ i < n, ContinuousOn (income R B T b) (Icc (p i) (p (i + 1))))
    (hstate : ∀ i < n, ∀ x ∈ Ioo (p i) (p (i + 1)),
      0 < T + x ∧ DifferentiableAt ℝ R (utilization B T x) ∧
      0 < R (utilization B T x) ∧
      share T b x * (1 + elasticity (utilization B T x) (R (utilization B T x))
        (deriv R (utilization B T x))) ≤ 1) :
    income R B T b (p 0) ≤ income R B T b (p n) := by
  apply finite_partition_income _ p n hp hc
  · intro i hi x hx
    obtain ⟨hT, hR, hr, _⟩ := hstate i hi x hx
    exact (income_hasDerivAt R B T b x _ hT.ne' hR.hasDerivAt hr.ne').differentiableAt
  · intro i hi x hx
    obtain ⟨hT, hR, hr, hs⟩ := hstate i hi x hx
    exact (income_deriv_nonneg_iff R B T b x hB hT hR hr).mpr hs

/-- A finite withdrawal from balance position `c` down to `a` strictly raises income if
`α (1 + η) > 1` at every smooth state in between and income is continuous on `[a, c]`. -/
theorem withdrawal_raises_income (R : ℝ → ℝ) (B T b a c : ℝ) (hB : 0 < B) (hac : a < c)
    (hc : ContinuousOn (income R B T b) (Icc a c))
    (hstate : ∀ x ∈ Ioo a c,
      0 < T + x ∧ DifferentiableAt ℝ R (utilization B T x) ∧
      0 < R (utilization B T x) ∧
      1 < share T b x * (1 + elasticity (utilization B T x) (R (utilization B T x))
        (deriv R (utilization B T x)))) :
    income R B T b c < income R B T b a := by
  have hanti : StrictAntiOn (income R B T b) (Icc a c) :=
    strictAntiOn_of_deriv_neg (convex_Icc a c) hc fun x hx => by
      rw [interior_Icc] at hx
      obtain ⟨hT, hR, hr, hs⟩ := hstate x hx
      exact (income_deriv_neg_iff R B T b x hB hT hR hr).mpr hs
  exact hanti ⟨le_rfl, hac.le⟩ ⟨hac.le, le_rfl⟩ hac

end SupplierMonotonicity
