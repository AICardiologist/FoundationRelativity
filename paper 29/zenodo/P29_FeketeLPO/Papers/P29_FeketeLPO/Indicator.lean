/-
  Paper 29: Fekete's Subadditive Lemma ↔ LPO
  Indicator.lean — Properties of the hasTrue / indicator sequences

  Key results:
    - hasTrue is monotone (once true, stays true)
    - indicator ∈ {0, 1}
    - indicator is monotone (non-decreasing)
    - If α ≡ false: indicator ≡ 0
    - If ∃ k, α(k) = true: indicator is eventually 1
    - hasTrue at 0 is false
    - Witness extraction: hasTrue α n = true → ∃ k < n, α k = true

  All proofs are BISH-valid. The indicator is computed by decidable
  bounded search — no Classical.choice in the proof content.
-/
import Papers.P29_FeketeLPO.Defs

namespace Papers.P29

-- ========================================================================
-- hasTrue: basic properties
-- ========================================================================

/-- hasTrue α 0 = false (no k < 0 exists). -/
@[simp]
lemma hasTrue_zero (α : ℕ → Bool) : hasTrue α 0 = false := by
  simp [hasTrue]

/-- hasTrue is monotone: if true at n, true at n+1. -/
lemma hasTrue_mono_succ (α : ℕ → Bool) (n : ℕ) :
    hasTrue α n ≤ hasTrue α (n + 1) := by
  unfold hasTrue
  simp only [List.range_succ, List.any_append, List.any_cons,
    List.any_nil, Bool.or_false]
  intro h
  simp [h]

/-- hasTrue is monotone in ℕ. -/
lemma hasTrue_mono (α : ℕ → Bool) : Monotone (hasTrue α) :=
  monotone_nat_of_le_succ (hasTrue_mono_succ α)

/-- Witness extraction: hasTrue α n = true → ∃ k < n, α k = true. -/
lemma hasTrue_witness {α : ℕ → Bool} {n : ℕ} (h : hasTrue α n = true) :
    ∃ k, k < n ∧ α k = true := by
  simp only [hasTrue, List.any_eq_true, List.mem_range] at h
  obtain ⟨k, hk, hak⟩ := h
  exact ⟨k, hk, by simpa using hak⟩

/-- If α k = true and k < n, then hasTrue α n = true. -/
lemma hasTrue_of_true {α : ℕ → Bool} {k n : ℕ} (hk : k < n) (hak : α k = true) :
    hasTrue α n = true := by
  simp only [hasTrue, List.any_eq_true, List.mem_range]
  exact ⟨k, hk, by simpa using hak⟩

/-- If all terms are false, hasTrue stays false. -/
lemma hasTrue_of_all_false (α : ℕ → Bool) (h : ∀ n, α n = false) (n : ℕ) :
    hasTrue α n = false := by
  simp only [hasTrue, List.any_eq_false, List.mem_range]
  intro k _
  simpa using h k

/-- If ∃ k, α k = true, then hasTrue is eventually true. -/
lemma hasTrue_of_exists_true (α : ℕ → Bool) {k : ℕ} (hk : α k = true) {n : ℕ}
    (hn : k < n) : hasTrue α n = true :=
  hasTrue_of_true hn hk

-- ========================================================================
-- indicator: real-valued properties
-- ========================================================================

/-- indicator α n ∈ {0, 1}. -/
lemma indicator_mem (α : ℕ → Bool) (n : ℕ) :
    indicator α n = 0 ∨ indicator α n = 1 := by
  unfold indicator
  split <;> simp

/-- indicator is non-negative. -/
lemma indicator_nonneg (α : ℕ → Bool) (n : ℕ) : 0 ≤ indicator α n := by
  unfold indicator; split <;> linarith

/-- indicator is at most 1. -/
lemma indicator_le_one (α : ℕ → Bool) (n : ℕ) : indicator α n ≤ 1 := by
  unfold indicator; split <;> linarith

/-- indicator α 0 = 0. -/
@[simp]
lemma indicator_zero (α : ℕ → Bool) : indicator α 0 = 0 := by
  simp [indicator]

/-- indicator is monotone (non-decreasing). -/
lemma indicator_mono (α : ℕ → Bool) : Monotone (indicator α) := by
  intro a b hab
  simp only [indicator]
  by_cases ha : hasTrue α a = true
  · -- hasTrue a = true → hasTrue b = true (by monotonicity)
    have hb : hasTrue α b = true := by
      have := hasTrue_mono α hab
      rw [Bool.le_iff_imp] at this
      exact this ha
    simp [ha, hb]
  · -- hasTrue a ≠ true, so indicator a = 0 ≤ indicator b
    rw [if_neg ha]
    by_cases hb : hasTrue α b = true
    · rw [if_pos hb]; linarith
    · rw [if_neg hb]

/-- If all terms are false, indicator is constantly 0. -/
lemma indicator_of_all_false (α : ℕ → Bool) (h : ∀ n, α n = false) (n : ℕ) :
    indicator α n = 0 := by
  simp [indicator, hasTrue_of_all_false α h n]

/-- If ∃ k, α k = true, then indicator is 1 for n > k. -/
lemma indicator_of_exists_true (α : ℕ → Bool) {k : ℕ} (hk : α k = true) {n : ℕ}
    (hn : k < n) : indicator α n = 1 := by
  simp [indicator, hasTrue_of_exists_true α hk hn]

end Papers.P29
