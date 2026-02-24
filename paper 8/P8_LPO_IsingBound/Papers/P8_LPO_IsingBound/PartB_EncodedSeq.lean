/-
Papers/P8_LPO_IsingBound/PartB_EncodedSeq.lean
Properties of the encoded free energy sequence F(n) = g(J(n)).

Key results:
  - encodedSeq takes values in {g(J₀), g(J₁)}
  - If α ≡ false: F ≡ g(J₀)
  - If ∃ n₀ with α(n₀) = true: F ≡ g(J₁) for n ≥ n₀
  - -F is non-decreasing (Monotone) and bounded above
-/
import Papers.P8_LPO_IsingBound.PartB_CouplingSeq
import Papers.P8_LPO_IsingBound.PartB_FreeEnergyAnti

namespace Papers.P8

open Real

-- ========================================================================
-- Values
-- ========================================================================

/-- encodedSeq takes values in {g(J₀), g(J₁)}. -/
lemma encodedSeq_mem (α : ℕ → Bool) (β J₀ J₁ : ℝ) (n : ℕ) :
    encodedSeq α β J₀ J₁ n = freeEnergyAtCoupling β J₀ ∨
    encodedSeq α β J₀ J₁ n = freeEnergyAtCoupling β J₁ := by
  unfold encodedSeq
  rcases couplingSeq_mem α J₀ J₁ n with h | h <;> [left; right] <;> rw [h]

-- ========================================================================
-- Eventual constancy
-- ========================================================================

/-- If α ≡ false, encodedSeq is constantly g(J₀). -/
lemma encodedSeq_of_all_false (α : ℕ → Bool) (β J₀ J₁ : ℝ)
    (h : ∀ n, α n = false) (n : ℕ) :
    encodedSeq α β J₀ J₁ n = freeEnergyAtCoupling β J₀ := by
  simp [encodedSeq, couplingSeq_of_all_false α J₀ J₁ h n]

/-- If ∃ n₀ with α(n₀) = true, encodedSeq is g(J₁) for n ≥ n₀. -/
lemma encodedSeq_of_exists_true (α : ℕ → Bool) (β J₀ J₁ : ℝ)
    {n₀ : ℕ} (h : α n₀ = true) {n : ℕ} (hn : n₀ ≤ n) :
    encodedSeq α β J₀ J₁ n = freeEnergyAtCoupling β J₁ := by
  simp [encodedSeq, couplingSeq_of_exists_true α J₀ J₁ h hn]

-- ========================================================================
-- Negated sequence is non-decreasing
-- ========================================================================

/-- The negated encodedSeq is non-decreasing.
    Since g is anti-monotone and J is non-decreasing, g(J(n)) is
    non-increasing, so -g(J(n)) is non-decreasing. -/
lemma neg_encodedSeq_mono (α : ℕ → Bool) {β J₀ J₁ : ℝ}
    (hβ : 0 < β) (hJ₀ : 0 < J₀) (hJ : J₀ ≤ J₁) :
    Monotone (fun n => -encodedSeq α β J₀ J₁ n) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [neg_le_neg_iff]
  -- Goal: g(coupling(n+1)) ≤ g(coupling(n))
  -- Since coupling(n) ≤ coupling(n+1) and g is anti-monotone
  unfold encodedSeq
  apply freeEnergyAtCoupling_le hβ
    (lt_of_lt_of_le hJ₀ (J0_le_couplingSeq α hJ n))
    (lt_of_lt_of_le hJ₀ (J0_le_couplingSeq α hJ (n + 1)))
    (couplingSeq_mono α hJ (Nat.le_succ n))

-- ========================================================================
-- Negated sequence is bounded
-- ========================================================================

/-- The negated encodedSeq is bounded above by -g(J₁). -/
lemma neg_encodedSeq_bounded (α : ℕ → Bool) {β J₀ J₁ : ℝ}
    (hβ : 0 < β) (hJ₀ : 0 < J₀) (hJ : J₀ ≤ J₁) (n : ℕ) :
    -encodedSeq α β J₀ J₁ n ≤ -freeEnergyAtCoupling β J₁ := by
  simp only [neg_le_neg_iff]
  -- Goal: g(J₁) ≤ g(coupling(n))
  -- Since coupling(n) ≤ J₁ and g is anti-monotone
  unfold encodedSeq
  apply freeEnergyAtCoupling_le hβ
    (lt_of_lt_of_le hJ₀ (J0_le_couplingSeq α hJ n))
    (lt_of_lt_of_le hJ₀ hJ)
    (couplingSeq_le_J1 α hJ n)

end Papers.P8
