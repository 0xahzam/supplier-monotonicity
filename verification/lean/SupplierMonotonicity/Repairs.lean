import SupplierMonotonicity.Boundaries

noncomputable section
open Set MeasureTheory
namespace SupplierMonotonicity

-- R01: The full finite-deposit statement for an explicitly given finite partition.
theorem finite_supplier_deposit (R : ℝ → ℝ) (B T b : ℝ) (p : ℕ → ℝ) (n : ℕ)
    (hB : 0 < B) (hp : ∀ i < n, p i ≤ p (i+1))
    (hc : ∀ i < n, ContinuousOn (income R B T b) (Icc (p i) (p (i+1))))
    (hstate : ∀ i < n, ∀ x ∈ Ioo (p i) (p (i+1)),
      0 < T+x ∧ DifferentiableAt ℝ R (utilization B T x) ∧
      0 < R (utilization B T x) ∧
      share T b x*(1+elasticity (utilization B T x) (R (utilization B T x))
        (deriv R (utilization B T x))) ≤ 1) :
    income R B T b (p 0) ≤ income R B T b (p n) := by
  apply finite_partition_income _ p n hp hc
  · intro i hi x hx
    rcases hstate i hi x hx with ⟨hT,hR,hr,_⟩
    exact (income_hasDerivAt R B T b x _ hT.ne' hR.hasDerivAt hr.ne').differentiableAt
  · intro i hi x hx
    rcases hstate i hi x hx with ⟨hT,hR,hr,hs⟩
    exact (income_deriv_nonneg_iff R B T b x hB hT hR hr).mpr hs

-- R02-R04: Complete inductive optimality of the recursions, indexed in their
-- construction direction. For the backwards recursions, zero denotes the top.
theorem floor_recursion_minimal (floor q c : ℕ → ℝ) (n : ℕ)
    (h0 : floor 0 ≤ q 0) (hc : ∀ i, 0 < c i)
    (hf : ∀ i, floor (i+1)=floor i / c i)
    (hq : ∀ i, q i ≤ c i*q (i+1)) : floor n ≤ q n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hf n]
    exact le_trans (div_le_div_of_nonneg_right ih (hc n).le)
      (backward_floor_bound _ _ _ (hc n) (hq n))

theorem raise_recursion_minimal (base up q c : ℕ → ℝ) (n : ℕ)
    (h0 : up 0 ≤ q 0) (hc : ∀ i, 0 < c i)
    (hu : ∀ i, up (i+1)=max (base (i+1)) (up i / c i))
    (hb : ∀ i, base i ≤ q i) (hq : ∀ i, q i ≤ c i*q (i+1)) : up n ≤ q n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hu n]
    exact max_le (hb (n+1)) (le_trans (div_le_div_of_nonneg_right ih (hc n).le)
      (backward_floor_bound _ _ _ (hc n) (hq n)))

theorem lower_recursion_maximal (base down q c : ℕ → ℝ) (n : ℕ)
    (h0 : q 0 ≤ down 0) (hc : ∀ i, 0 ≤ c i)
    (hd : ∀ i, down (i+1)=min (base (i+1)) (c i*down i))
    (hb : ∀ i, q i ≤ base i) (hq : ∀ i, q (i+1) ≤ c i*q i) : q n ≤ down n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hd n]
    exact le_min (hb (n+1)) (le_trans (hq n) (mul_le_mul_of_nonneg_left ih (hc n)))

-- R05: Zero/nonpositive denominator branches of the fixed-share cap impose no constraint.
theorem fixed_right_unbounded (h d r s K : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hh : 0 ≤ h) (hd : h-K*d ≤ 0) : h*(s-r) ≤ K*s*d := by
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hd hs, mul_nonneg hh hr]

theorem fixed_left_zero (K r d : ℝ) (hK : 0 ≤ K) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    (0:ℝ) ≤ K*r*d := mul_nonneg (mul_nonneg hK hr) hd

-- R07: Normalized quotient derivative sign is precisely the envelope condition.
theorem normalized_derivative_iff (u r m f E : ℝ) (hu : 0 < u) (hf : 0 < f) :
    (m*f-r*(E*f/u))/f^2 ≤ 0 ↔ u*m ≤ E*r := by
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

-- R08-R11: Order-theoretic core of analytic repairs. Admissible q is antitone.
-- Continuity/regularity of the constructed rate and its zero limit are separate.
theorem analytic_minorant_bound (q q0 : ℝ → ℝ) (u : ℝ) (hu : 0 < u)
    (hm : AntitoneOn q (Ioc (0:ℝ) u)) (hb : ∀ v ∈ Ioc (0:ℝ) u, q v ≤ q0 v) :
    q u ≤ sInf (q0 '' Ioc (0:ℝ) u) := by
  refine le_csInf (s := q0 '' Ioc (0:ℝ) u) ?_ ?_
  · exact ⟨q0 u, ⟨u,⟨hu,le_rfl⟩,rfl⟩⟩
  rintro _ ⟨v,hv,rfl⟩
  exact le_trans (hm hv ⟨hu,le_rfl⟩ hv.2) (hb v hv)

theorem analytic_minorant_below (q0 : ℝ → ℝ) (u : ℝ) (hu : 0 < u)
    (hb : BddBelow (q0 '' Ioc (0:ℝ) u)) :
    sInf (q0 '' Ioc (0:ℝ) u) ≤ q0 u :=
  csInf_le hb ⟨u,⟨hu,le_rfl⟩,rfl⟩

theorem analytic_majorant_bound (q q0 : ℝ → ℝ) (u : ℝ) (hu : u ≤ 1)
    (hm : AntitoneOn q (Icc u 1)) (hb : ∀ v ∈ Icc u 1, q0 v ≤ q v) :
    sSup (q0 '' Icc u 1) ≤ q u := by
  refine csSup_le (s := q0 '' Icc u 1) ?_ ?_
  · exact ⟨q0 u, ⟨u,⟨le_rfl,hu⟩,rfl⟩⟩
  rintro _ ⟨v,hv,rfl⟩
  exact le_trans (hb v hv) (hm ⟨le_rfl,hu⟩ hv hv.1)

theorem analytic_majorant_above (q0 : ℝ → ℝ) (u : ℝ) (hu : u ≤ 1)
    (hb : BddAbove (q0 '' Icc u 1)) : q0 u ≤ sSup (q0 '' Icc u 1) :=
  le_csSup hb ⟨u,⟨le_rfl,hu⟩,rfl⟩

-- R12: Minimum of two positive protection ceilings corresponds to max profile.
theorem max_profile_envelope (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1-max a b)/(max a b) = min ((1-a)/a) ((1-b)/b) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, min_eq_right]
    apply (div_le_div_iff₀ hb ha).mpr
    nlinarith
  · rw [max_eq_left hba, min_eq_left]
    apply (div_le_div_iff₀ ha hb).mpr
    nlinarith

-- R13: A base bound from a normalized antitone curve and a boundary F(0)=1.
theorem normalized_base_bound (R F : ℝ → ℝ)
    (hF0 : F 0=1)
    (hm : AntitoneOn (fun u => R u/F u) (Icc (0:ℝ) 1)) : R 1/F 1 ≤ R 0 := by
  have h := hm (by norm_num) (by norm_num) (by norm_num : (0:ℝ) ≤ 1)
  simpa [hF0] using h

-- R14: Positive rates can have arbitrarily large scalar multiples with the same elasticity.
theorem supplier_transfer (b T B r s f : ℝ) :
    (1-f)*b*(B/T)*(s-r) = (1-f)*(b/T)*(B*s-B*r) := by ring

-- Scope test for the general analytic-minorant paragraph (not the positive-base
-- USDT example): baseline R0(u)=u, flat boundary F(u)=1, envelope E=0.
-- The running infimum is zero and therefore is outside the positive-rate class.
theorem zero_base_flat_minorant (u : ℝ) (hu : 0 < u) :
    (1:ℝ) * sInf ((fun v : ℝ => v/1) '' Ioc (0:ℝ) u) = 0 := by
  simpa using csInf_Ioc hu

theorem no_positive_flat_minorant (q : ℝ → ℝ)
    (hm : AntitoneOn q (Ioc (0:ℝ) 1))
    (hb : ∀ u ∈ Ioc (0:ℝ) 1, q u ≤ u) : ¬ 0 < q 1 := by
  intro hpos
  have hu : q 1/2 ∈ Ioc (0:ℝ) 1 := by
    have h1 := hb 1 ⟨by norm_num,le_rfl⟩
    constructor <;> linarith
  have hmon := hm hu ⟨by norm_num,le_rfl⟩ hu.2
  have hbound := hb (q 1/2) hu
  linarith

end SupplierMonotonicity
