import SupplierMonotonicity.Model

/-!
# Repairs and several kinks

Order-theoretic facts behind the repair constructions: combining protection profiles, kink-rate
caps for piecewise linear curves, the backward floor/raise and forward lower recursions, and the
analytic greatest minorant and least majorant (paper, Sections 8 and 9, Appendix B).

The recursions use finite positive real caps; an infinite cap is not encoded as division by
infinity. Backward recursions are indexed from the top kink, so index `0` is the top.

Not covered here: continuity and regularity of the constructed curves, and the full
rejoin/greatest-minorant theorem.
-/

namespace SupplierMonotonicity

open Set

/-! ### Combining guarantees -/

/-- The fresh envelope `u / (1 - u)` stays below `K` exactly up to `u = K / (1 + K)`. -/
theorem envelope_crossing (u K : ℝ) (hu : u < 1) (hK : 0 ≤ K) :
    u / (1 - u) ≤ K ↔ u ≤ K / (1 + K) := by
  rw [div_le_iff₀ (sub_pos.mpr hu), le_div_iff₀ (by linarith : 0 < 1 + K)]
  constructor <;> intro h <;> nlinarith

/-- Meeting two envelopes is meeting their minimum. -/
theorem combined_envelope (e a b : ℝ) : (e ≤ a ∧ e ≤ b) ↔ e ≤ min a b :=
  le_min_iff.symm

/-- Protecting the larger of two shares gives the smaller of the two envelopes. -/
theorem max_profile_envelope (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1 - max a b) / max a b = min ((1 - a) / a) ((1 - b) / b) := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, min_eq_right]
    apply (div_le_div_iff₀ hb ha).mpr
    nlinarith
  · rw [max_eq_left hba, min_eq_left]
    apply (div_le_div_iff₀ ha hb).mpr
    nlinarith

/-! ### Kink-rate caps for a fixed share `K` -/

theorem fixed_left_cap_iff (l d r s K : ℝ) (hl : 0 < l) (hr : 0 < r) :
    l * (s - r) ≤ K * r * d ↔ s / r ≤ 1 + K * d / l := by
  rw [div_le_iff₀ hr]
  constructor <;> intro H
  · apply (mul_le_mul_iff_of_pos_right hl).mp
    field_simp
    nlinarith
  · have H' := (mul_le_mul_iff_of_pos_right hl).mpr H
    field_simp at H'
    nlinarith

theorem fixed_right_cap_iff (h d r s K : ℝ) (hr : 0 < r) (hd : 0 < h - K * d) :
    h * (s - r) ≤ K * s * d ↔ s / r ≤ h / (h - K * d) := by
  rw [div_le_div_iff₀ hr hd]
  constructor <;> intro H <;> nlinarith

/-- When `h - K d ≤ 0` the right-endpoint cap imposes no constraint. -/
theorem fixed_right_unbounded (h d r s K : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (hd : h - K * d ≤ 0) : h * (s - r) ≤ K * s * d := by
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hd hs, mul_nonneg hh hr]

/-- At `l = 0` the left-endpoint cap imposes no constraint. -/
theorem fixed_left_zero (K r d : ℝ) (hK : 0 ≤ K) (hr : 0 ≤ r) (hd : 0 ≤ d) : (0 : ℝ) ≤ K * r * d :=
  mul_nonneg (mul_nonneg hK hr) hd

/-! ### Recursions on kink rates -/

/-- One backward step: a feasible rate `r` below `next` with ratio cap `c` satisfies
`next / c ≤ r`. -/
theorem backward_floor_bound (c next r : ℝ) (hc : 0 < c) (h : next ≤ c * r) : next / c ≤ r :=
  (div_le_iff₀ hc).mpr (by nlinarith)

theorem raise_step_minimal (base next c r : ℝ) (hc : 0 < c) (hb : base ≤ r) (hn : next ≤ c * r) :
    max base (next / c) ≤ r :=
  max_le hb (backward_floor_bound c next r hc hn)

theorem raise_step_feasible (base next c : ℝ) (hc : 1 ≤ c) (hn : 0 ≤ next) (hb : base ≤ next) :
    base ≤ max base (next / c) ∧ max base (next / c) ≤ next ∧
      next ≤ c * max base (next / c) := by
  have hc0 : 0 < c := by linarith
  refine ⟨le_max_left _ _, max_le hb ?_, ?_⟩
  · apply (div_le_iff₀ hc0).mpr
    nlinarith
  · have := le_max_right base (next / c)
    have := (div_le_iff₀ hc0).mp this
    nlinarith

theorem lower_step_maximal (base prev c r : ℝ) (hb : r ≤ base) (hc : r ≤ c * prev) :
    r ≤ min base (c * prev) :=
  le_min hb hc

/-- The backward floor recursion is below every feasible competitor `q`. -/
theorem floor_recursion_minimal (floor q c : ℕ → ℝ) (n : ℕ) (h0 : floor 0 ≤ q 0)
    (hc : ∀ i, 0 < c i) (hf : ∀ i, floor (i + 1) = floor i / c i)
    (hq : ∀ i, q i ≤ c i * q (i + 1)) : floor n ≤ q n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hf n]
    exact le_trans (div_le_div_of_nonneg_right ih (hc n).le)
      (backward_floor_bound _ _ _ (hc n) (hq n))

/-- The backward raise recursion is below every feasible competitor above the baseline. -/
theorem raise_recursion_minimal (base up q c : ℕ → ℝ) (n : ℕ) (h0 : up 0 ≤ q 0)
    (hc : ∀ i, 0 < c i) (hu : ∀ i, up (i + 1) = max (base (i + 1)) (up i / c i))
    (hb : ∀ i, base i ≤ q i) (hq : ∀ i, q i ≤ c i * q (i + 1)) : up n ≤ q n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hu n]
    exact max_le (hb (n + 1)) (le_trans (div_le_div_of_nonneg_right ih (hc n).le)
      (backward_floor_bound _ _ _ (hc n) (hq n)))

/-- The forward lower recursion is above every feasible competitor below the baseline. -/
theorem lower_recursion_maximal (base down q c : ℕ → ℝ) (n : ℕ) (h0 : q 0 ≤ down 0)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, down (i + 1) = min (base (i + 1)) (c i * down i))
    (hb : ∀ i, q i ≤ base i) (hq : ∀ i, q (i + 1) ≤ c i * q i) : q n ≤ down n := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [hd n]
    exact le_min (hb (n + 1)) (le_trans (hq n) (mul_le_mul_of_nonneg_left ih (hc n)))

/-! ### Analytic minorant and majorant

Here `q = R / F` is a normalized rate; an admissible `q` is antitone. -/

theorem analytic_minorant_bound (q q0 : ℝ → ℝ) (u : ℝ) (hu : 0 < u)
    (hm : AntitoneOn q (Ioc (0 : ℝ) u)) (hb : ∀ v ∈ Ioc (0 : ℝ) u, q v ≤ q0 v) :
    q u ≤ sInf (q0 '' Ioc (0 : ℝ) u) := by
  refine le_csInf ⟨q0 u, u, ⟨hu, le_rfl⟩, rfl⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact le_trans (hm hv ⟨hu, le_rfl⟩ hv.2) (hb v hv)

theorem analytic_minorant_below (q0 : ℝ → ℝ) (u : ℝ) (hu : 0 < u)
    (hb : BddBelow (q0 '' Ioc (0 : ℝ) u)) : sInf (q0 '' Ioc (0 : ℝ) u) ≤ q0 u :=
  csInf_le hb ⟨u, ⟨hu, le_rfl⟩, rfl⟩

theorem analytic_majorant_bound (q q0 : ℝ → ℝ) (u : ℝ) (hu : u ≤ 1)
    (hm : AntitoneOn q (Icc u 1)) (hb : ∀ v ∈ Icc u 1, q0 v ≤ q v) :
    sSup (q0 '' Icc u 1) ≤ q u := by
  refine csSup_le ⟨q0 u, u, ⟨le_rfl, hu⟩, rfl⟩ ?_
  rintro _ ⟨v, hv, rfl⟩
  exact le_trans (hb v hv) (hm ⟨le_rfl, hu⟩ hv hv.1)

theorem analytic_majorant_above (q0 : ℝ → ℝ) (u : ℝ) (hu : u ≤ 1)
    (hb : BddAbove (q0 '' Icc u 1)) : q0 u ≤ sSup (q0 '' Icc u 1) :=
  le_csSup hb ⟨u, ⟨le_rfl, hu⟩, rfl⟩

/-- The running infimum of a baseline is antitone. -/
theorem running_inf_antitone {q₀ : ℝ → ℝ} {s : Set ℝ}
    (hbdd : ∀ U, BddBelow (q₀ '' {v | v ∈ s ∧ v ≤ U}))
    (hne : ∀ U ∈ s, (q₀ '' {v | v ∈ s ∧ v ≤ U}).Nonempty) :
    AntitoneOn (fun U => sInf (q₀ '' {v | v ∈ s ∧ v ≤ U})) s := by
  intro x hx y _ hxy
  refine csInf_le_csInf (hbdd y) (hne x hx) ?_
  rintro z ⟨v, ⟨hvs, hvx⟩, rfl⟩
  exact ⟨v, ⟨hvs, le_trans hvx hxy⟩, rfl⟩

/-- An antitone normalized curve with `F 0 = 1` bounds the base rate: `R 1 / F 1 ≤ R 0`. -/
theorem normalized_base_bound (R F : ℝ → ℝ) (hF0 : F 0 = 1)
    (hm : AntitoneOn (fun u => R u / F u) (Icc (0 : ℝ) 1)) : R 1 / F 1 ≤ R 0 := by
  have h := hm (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  simpa [hF0] using h

/-! ### Scope examples for the positive-base assumption

With baseline `R₀(u) = u`, flat boundary `F = 1` and envelope `E = 0`, the running infimum is
zero, so the construction leaves the positive-rate class. This is why the paper assumes a
positive base rate. -/

theorem zero_base_flat_minorant (u : ℝ) (hu : 0 < u) :
    (1 : ℝ) * sInf ((fun v : ℝ => v / 1) '' Ioc (0 : ℝ) u) = 0 := by
  simpa using csInf_Ioc hu

theorem no_positive_flat_minorant (q : ℝ → ℝ) (hm : AntitoneOn q (Ioc (0 : ℝ) 1))
    (hb : ∀ u ∈ Ioc (0 : ℝ) 1, q u ≤ u) : ¬ 0 < q 1 := by
  intro hpos
  have hu : q 1 / 2 ∈ Ioc (0 : ℝ) 1 := by
    have h1 := hb 1 ⟨by norm_num, le_rfl⟩
    constructor <;> linarith
  have hmon := hm hu ⟨by norm_num, le_rfl⟩ hu.2
  have hbound := hb (q 1 / 2) hu
  linarith

end SupplierMonotonicity
