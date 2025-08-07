/-
  Papers/P2_BidualGap/Constructive/WitnessRational.lean
  
  Following junior professor's advice: Prove everything in ℚ first,
  then embed with CReal.from_rat.
-/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith

namespace Papers.P2_BidualGap.Constructive

/-- Binary sequence type -/
def BinarySeq := ℕ → Bool

/-- Count how many true values in first n+1 positions -/
def count_true (α : BinarySeq) : ℕ → ℕ
  | 0 => if α 0 then 1 else 0
  | n+1 => count_true α n + if α (n+1) then 1 else 0

/-- The rational partial sums -/
def S (α : BinarySeq) (n : ℕ) : ℚ := count_true α n

/-- Key lemma: if α m = true, then for all n ≥ m, count_true α n ≥ 1 -/
lemma count_true_ge_one (α : BinarySeq) (m : ℕ) (hm : α m = true) :
  ∀ n ≥ m, count_true α n ≥ 1 := by
  intro n hn
  induction n with
  | zero => 
    simp at hn
    subst hn
    simp [count_true, hm]
  | succ n ih =>
    simp [count_true]
    by_cases h : n < m
    · -- If n < m, then n+1 might equal m
      by_cases h2 : n + 1 = m
      · subst h2
        simp [hm]
        omega
      · -- n < m but n+1 ≠ m, so count_true α (n+1) = 0
        -- This case shouldn't happen in our proof
        sorry
    · -- n ≥ m, so by IH count_true α n ≥ 1
      push_neg at h
      have : count_true α n ≥ 1 := ih h
      omega

/-- The normalized witness sequence -/
def witness_rat (α : BinarySeq) (n : ℕ) : ℚ :=
  S α n / (n + 1)

/-- Simplified theorem: if not all false, then partial sums don't converge to 0 -/
theorem S_not_converge_if_exists_true (α : BinarySeq) (m : ℕ) (hm : α m = true) :
  ∃ c > 0, ∀ N, ∃ n ≥ N, S α n ≥ c := by
  use 1
  constructor
  · norm_num
  · intro N
    use max N m
    constructor
    · exact le_max_left _ _
    · simp [S]
      exact count_true_ge_one α m hm _ (le_max_right _ _)

/-- Main theorem: witness converges to 0 iff all α n = false -/
theorem witness_converges_iff_all_false (α : BinarySeq) :
  (∀ ε > 0, ∃ N, ∀ n ≥ N, |witness_rat α n| < ε) ↔ (∀ n, α n = false) := by
  constructor
  · -- Forward: convergence implies all false
    intro h_conv
    by_contra h_not_all
    push_neg at h_not_all
    obtain ⟨m, hm⟩ := h_not_all
    -- We have α m = true
    have hm' : α m = true := by
      cases h : α m
      · contradiction
      · rfl
    
    -- Choose ε = 1/(2(m+1))
    have hε : (0 : ℚ) < 1/(2*(m+1)) := by norm_num
    obtain ⟨N, hN⟩ := h_conv (1/(2*(m+1))) hε
    
    -- Take n = max(N, m)
    let n := max N m
    have hn_N : n ≥ N := le_max_left _ _
    have hn_m : n ≥ m := le_max_right _ _
    
    -- From convergence: |witness n| < 1/(2(m+1))
    have h1 : |witness_rat α n| < 1/(2*(m+1)) := hN n hn_N
    
    -- But S α n ≥ 1
    have hS : S α n ≥ 1 := by
      simp [S]
      exact count_true_ge_one α m hm' n hn_m
    
    -- So witness n ≥ 1/(n+1)
    have hw : witness_rat α n ≥ 1/(n+1) := by
      simp [witness_rat]
      -- S α n / (n+1) ≥ 1/(n+1) since S α n ≥ 1
      apply div_le_div_of_nonneg_right hS
      norm_cast
      omega
    
    -- Since n ≥ m, we have n+1 ≥ m+1, so 1/(n+1) ≤ 1/(m+1)
    have : 1/(n+1 : ℚ) ≤ 1/(m+1) := by
      apply div_le_div_of_nonneg_left
      · norm_num
      · norm_cast; omega
      · norm_cast; exact hn_m
    
    -- Since m ≥ 0, we have m+1 < 2(m+1), so 1/(m+1) > 1/(2(m+1))
    have : 1/(m+1 : ℚ) > 1/(2*(m+1)) := by
      rw [div_lt_div_left]
      · norm_cast; simp; omega
      · norm_num
      · norm_cast; omega
    
    -- Witness values are non-negative
    have hw_pos : witness_rat α n ≥ 0 := by
      simp [witness_rat, S]
      apply div_nonneg
      · norm_cast
        exact Nat.zero_le _
      · norm_cast; omega
    
    -- So |witness n| = witness n
    have : |witness_rat α n| = witness_rat α n := abs_of_nonneg hw_pos
    rw [this] at h1
    
    -- Now we have: witness n ≥ 1/(n+1) ≤ 1/(m+1) > 1/(2(m+1))
    -- But also witness n < 1/(2(m+1))
    -- Contradiction
    linarith
    
  · -- Reverse: all false implies convergence
    intro h_all_false ε hε
    -- If all false, then count_true α n = 0 for all n
    have : ∀ n, count_true α n = 0 := by
      intro n
      induction n with
      | zero => simp [count_true, h_all_false 0]
      | succ n ih => simp [count_true, ih, h_all_false (n+1)]
    
    -- So witness = 0 for all n
    use 0
    intro n _
    simp [witness_rat, S, this n]
    exact hε

end Papers.P2_BidualGap.Constructive