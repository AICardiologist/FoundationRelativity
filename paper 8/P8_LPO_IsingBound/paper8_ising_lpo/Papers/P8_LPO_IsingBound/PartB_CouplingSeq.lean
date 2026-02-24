/-
Papers/P8_LPO_IsingBound/PartB_CouplingSeq.lean
Properties of the coupling sequence derived from a binary sequence.

Key results:
  - Coupling values are in {J₀, J₁}
  - Coupling is non-decreasing when J₀ ≤ J₁
  - Coupling is bounded: J₀ ≤ couplingSeq ≤ J₁
  - If α ≡ false: coupling ≡ J₀
  - If ∃ n₀ with α(n₀) = true: coupling ≡ J₁ for n ≥ n₀
-/
import Papers.P8_LPO_IsingBound.PartB_RunMax

namespace Papers.P8

-- ========================================================================
-- Values
-- ========================================================================

/-- Coupling values are in {J₀, J₁}. -/
lemma couplingSeq_mem (α : ℕ → Bool) (J₀ J₁ : ℝ) (n : ℕ) :
    couplingSeq α J₀ J₁ n = J₀ ∨ couplingSeq α J₀ J₁ n = J₁ := by
  unfold couplingSeq
  cases runMax α n <;> simp

-- ========================================================================
-- Monotonicity
-- ========================================================================

/-- Coupling is non-decreasing when J₀ ≤ J₁. -/
lemma couplingSeq_mono (α : ℕ → Bool) {J₀ J₁ : ℝ} (hJ : J₀ ≤ J₁) :
    Monotone (couplingSeq α J₀ J₁) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold couplingSeq
  cases h1 : runMax α n <;> cases h2 : runMax α (n + 1) <;> simp
  · exact hJ
  · -- runMax α n = true but runMax α (n+1) = false: impossible
    exfalso
    have := runMax_le_succ α n
    rw [h1, h2] at this
    exact absurd this (by decide)

-- ========================================================================
-- Bounds
-- ========================================================================

/-- Coupling is bounded above by J₁. -/
lemma couplingSeq_le_J1 (α : ℕ → Bool) {J₀ J₁ : ℝ} (hJ : J₀ ≤ J₁) (n : ℕ) :
    couplingSeq α J₀ J₁ n ≤ J₁ := by
  rcases couplingSeq_mem α J₀ J₁ n with h | h <;> simp [h]
  exact hJ

/-- Coupling is bounded below by J₀. -/
lemma J0_le_couplingSeq (α : ℕ → Bool) {J₀ J₁ : ℝ} (hJ : J₀ ≤ J₁) (n : ℕ) :
    J₀ ≤ couplingSeq α J₀ J₁ n := by
  rcases couplingSeq_mem α J₀ J₁ n with h | h <;> simp [h]
  exact hJ

-- ========================================================================
-- Eventual constancy
-- ========================================================================

/-- If α ≡ false, coupling is constantly J₀. -/
lemma couplingSeq_of_all_false (α : ℕ → Bool) (J₀ J₁ : ℝ)
    (h : ∀ n, α n = false) (n : ℕ) :
    couplingSeq α J₀ J₁ n = J₀ := by
  simp [couplingSeq, runMax_of_all_false α h n]

/-- If ∃ n₀ with α(n₀) = true, coupling is J₁ for n ≥ n₀. -/
lemma couplingSeq_of_exists_true (α : ℕ → Bool) (J₀ J₁ : ℝ)
    {n₀ : ℕ} (h : α n₀ = true) {n : ℕ} (hn : n₀ ≤ n) :
    couplingSeq α J₀ J₁ n = J₁ := by
  simp [couplingSeq, runMax_of_exists_true α h hn]

end Papers.P8
