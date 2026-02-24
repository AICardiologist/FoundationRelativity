/-
Papers/P17_BHEntropy/PartB_AreaSeq.lean
Properties of the area sequence derived from a binary sequence.

Key results:
  - Area values are in {A_lo, A_hi}
  - Area is non-decreasing when A_lo ≤ A_hi
  - If α ≡ false: area ≡ A_lo
  - If ∃ n₀ with α(n₀) = true: area ≡ A_hi for n ≥ n₀

Adapted from Paper 8's PartB_CouplingSeq.lean.
-/
import Papers.P17_BHEntropy.PartB_RunMax

namespace Papers.P17

-- ========================================================================
-- Values
-- ========================================================================

/-- Area values are in {A_lo, A_hi}. -/
lemma areaSeq_mem (α : ℕ → Bool) (A_lo A_hi : ℝ) (n : ℕ) :
    areaSeq α A_lo A_hi n = A_lo ∨ areaSeq α A_lo A_hi n = A_hi := by
  unfold areaSeq
  cases runMax α n <;> simp

-- ========================================================================
-- Monotonicity
-- ========================================================================

/-- Area is non-decreasing when A_lo ≤ A_hi. -/
lemma areaSeq_mono (α : ℕ → Bool) {A_lo A_hi : ℝ} (hA : A_lo ≤ A_hi) :
    Monotone (areaSeq α A_lo A_hi) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold areaSeq
  cases h1 : runMax α n <;> cases h2 : runMax α (n + 1) <;> simp
  · exact hA
  · exfalso
    have := runMax_le_succ α n
    rw [h1, h2] at this
    exact absurd this (by decide)

-- ========================================================================
-- Bounds
-- ========================================================================

/-- Area is bounded above by A_hi. -/
lemma areaSeq_le_hi (α : ℕ → Bool) {A_lo A_hi : ℝ} (hA : A_lo ≤ A_hi) (n : ℕ) :
    areaSeq α A_lo A_hi n ≤ A_hi := by
  rcases areaSeq_mem α A_lo A_hi n with h | h <;> simp [h]
  exact hA

/-- Area is bounded below by A_lo. -/
lemma lo_le_areaSeq (α : ℕ → Bool) {A_lo A_hi : ℝ} (hA : A_lo ≤ A_hi) (n : ℕ) :
    A_lo ≤ areaSeq α A_lo A_hi n := by
  rcases areaSeq_mem α A_lo A_hi n with h | h <;> simp [h]
  exact hA

-- ========================================================================
-- Eventual constancy
-- ========================================================================

/-- If α ≡ false, area is constantly A_lo. -/
lemma areaSeq_of_all_false (α : ℕ → Bool) (A_lo A_hi : ℝ)
    (h : ∀ n, α n = false) (n : ℕ) :
    areaSeq α A_lo A_hi n = A_lo := by
  simp [areaSeq, runMax_of_all_false α h n]

/-- If ∃ n₀ with α(n₀) = true, area is A_hi for n ≥ n₀. -/
lemma areaSeq_of_exists_true (α : ℕ → Bool) (A_lo A_hi : ℝ)
    {n₀ : ℕ} (h : α n₀ = true) {n : ℕ} (hn : n₀ ≤ n) :
    areaSeq α A_lo A_hi n = A_hi := by
  simp [areaSeq, runMax_of_exists_true α h hn]

end Papers.P17
