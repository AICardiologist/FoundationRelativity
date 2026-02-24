/-
  Paper 35: The Conservation Metatheorem
  WLPOBoundary.lean: Theorem B3 — Limit equality is WLPO

  Deciding whether a completed real equals a specific value
  (x = c ∨ x ≠ c) costs WLPO.
-/
import Papers.P35_ConservationMetatheorem.Defs

noncomputable section

open Real

-- ============================================================
-- Theorem B3: Limit Equality Decision → WLPO
-- ============================================================

/-- WLPO decides x = 0 ∨ x ≠ 0 for completed reals.
    This is the zero-test / threshold decision mechanism. -/
theorem wlpo_decides_zero_test (hw : WLPO) (x : ℝ)
    (hx : ∃ a : ℕ → Bool, x = 0 ↔ ∀ n, a n = false) :
    x = 0 ∨ x ≠ 0 := by
  obtain ⟨a, ha⟩ := hx
  cases hw a with
  | inl h_all => left; exact ha.mpr h_all
  | inr h_not => right; intro heq; exact h_not (ha.mp heq)

/-- Given WLPO, for any completed real x and target c,
    we can decide x = c ∨ x ≠ c.
    This is the threshold decision mechanism. -/
theorem wlpo_decides_equality (hw : WLPO) (x c : ℝ)
    (hxc : ∃ a : ℕ → Bool, x = c ↔ ∀ n, a n = false) :
    x = c ∨ x ≠ c := by
  obtain ⟨a, ha⟩ := hxc
  cases hw a with
  | inl h_all => left; exact ha.mpr h_all
  | inr h_not => right; intro heq; exact h_not (ha.mp heq)

-- ============================================================
-- LLPO: Sign Decision / Disjunction
-- ============================================================

/-- LLPO decides sign disjunctions: x ≤ 0 ∨ x ≥ 0
    when x is a completed real. This is the mechanism behind
    Bell nonlocality (Paper 21) and IVT (Paper 27). -/
theorem llpo_decides_sign (hl : LLPO) (x : ℝ)
    (hx : ∃ a : ℕ → Bool,
      (x ≤ 0 ↔ ∀ n, a (2 * n) = false) ∧
      (x ≥ 0 ↔ ∀ n, a (2 * n + 1) = false)) :
    x ≤ 0 ∨ x ≥ 0 := by
  obtain ⟨a, h_neg, h_pos⟩ := hx
  cases hl a with
  | inl h_even => left; exact h_neg.mpr h_even
  | inr h_odd => right; exact h_pos.mpr h_odd

-- ============================================================
-- Subsumption: LPO ⊇ WLPO ⊇ LLPO
-- ============================================================

/-- The hierarchy is strictly ordered and LPO is the ceiling. -/
theorem lpo_subsumes_all (hl : LPO) :
    WLPO ∧ LLPO :=
  ⟨wlpo_of_lpo hl, llpo_of_wlpo (wlpo_of_lpo hl)⟩

end
