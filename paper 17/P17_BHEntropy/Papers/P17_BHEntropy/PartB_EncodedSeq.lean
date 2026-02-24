/-
Papers/P17_BHEntropy/PartB_EncodedSeq.lean
Properties of the encoded entropy density sequence S_alpha.

Key results:
  - S_alpha takes values in {entropy_density A_lo, entropy_density A_hi}
  - If α ≡ false: S_alpha ≡ entropy_density A_lo
  - If ∃ n₀ with α(n₀) = true: S_alpha ≡ entropy_density A_hi for n ≥ n₀

Adapted from Paper 8's PartB_EncodedSeq.lean.
-/
import Papers.P17_BHEntropy.PartB_AreaSeq
import Papers.P17_BHEntropy.PartB_GapLemma

noncomputable section
namespace Papers.P17

open Real

-- ========================================================================
-- Values
-- ========================================================================

/-- S_alpha takes values in {entropy_density A_lo, entropy_density A_hi}. -/
lemma S_alpha_mem (α : ℕ → Bool) (A_lo A_hi gamma delta : ℝ)
    (hA_lo : A_lo > 0) (hA_hi : A_hi > 0)
    (hg : gamma > 0) (hd : delta > 0) (n : ℕ) :
    S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd n =
      entropy_density A_lo gamma delta hA_lo hg hd ∨
    S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd n =
      entropy_density A_hi gamma delta hA_hi hg hd := by
  unfold S_alpha
  cases runMax α n <;> simp

-- ========================================================================
-- Eventual constancy
-- ========================================================================

/-- If α ≡ false, S_alpha is constantly entropy_density A_lo. -/
lemma S_alpha_of_all_false (α : ℕ → Bool) (A_lo A_hi gamma delta : ℝ)
    (hA_lo : A_lo > 0) (hA_hi : A_hi > 0)
    (hg : gamma > 0) (hd : delta > 0)
    (h : ∀ n, α n = false) (n : ℕ) :
    S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd n =
      entropy_density A_lo gamma delta hA_lo hg hd := by
  unfold S_alpha
  rw [runMax_of_all_false α h n]

/-- If ∃ n₀ with α(n₀) = true, S_alpha is entropy_density A_hi for n ≥ n₀. -/
lemma S_alpha_of_exists_true (α : ℕ → Bool) (A_lo A_hi gamma delta : ℝ)
    (hA_lo : A_lo > 0) (hA_hi : A_hi > 0)
    (hg : gamma > 0) (hd : delta > 0)
    {n₀ : ℕ} (h : α n₀ = true) {n : ℕ} (hn : n₀ ≤ n) :
    S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd n =
      entropy_density A_hi gamma delta hA_hi hg hd := by
  unfold S_alpha
  rw [runMax_of_exists_true α h hn]

end Papers.P17
end
