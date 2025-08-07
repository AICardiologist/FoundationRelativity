/-
  Papers/P2_BidualGap/Constructive/WitnessSimple.lean
  
  Simplified witness sequence following senior professor's advice:
  Use unnormalized v^α_n = ∑_{k=1}^n α_k (not divided by n+1).
  This makes the proof much cleaner.
-/

import Papers.P2_BidualGap.Constructive.RegularReal
import Papers.P2_BidualGap.Logic.WLPOBasic

namespace Papers.P2_BidualGap.Constructive

open RegularReal

/-- The unnormalized witness sequence: v^α_n = ∑_{k=0}^n α_k -/
def witness_simple (α : BinarySeq) (n : ℕ) : ℕ :=
  (List.range (n + 1)).foldl (fun acc k => acc + if α k then 1 else 0) 0

/-- Witness sequence as regular reals -/
def witness_regular (α : BinarySeq) : ℕ → RegularReal :=
  fun n => from_rat (witness_simple α n)

/-- Key property: witness values are 0 or ≥ 1 -/
lemma witness_discrete (α : BinarySeq) (n : ℕ) :
  witness_simple α n = 0 ∨ witness_simple α n ≥ 1 := by
  induction n with
  | zero => 
    simp [witness_simple, List.range]
    cases h : α 0
    · left; rfl
    · right; norm_num
  | succ n ih =>
    simp [witness_simple, List.range]
    cases ih with
    | inl h => 
      -- Previous sum was 0
      cases h' : α (n + 1)
      · left
        sorry -- TODO: Show sum stays 0
      · right
        sorry -- TODO: Show sum becomes 1
    | inr h =>
      -- Previous sum was ≥ 1
      right
      sorry -- TODO: Show sum stays ≥ 1

/-- Main theorem: witness in c₀ iff all α n = false -/
theorem witness_in_c_zero_iff_simple (α : BinarySeq) :
  (∀ ε > 0, ∃ N, ∀ n ≥ N, witness_simple α n < ε) ↔ (∀ n, α n = false) := by
  constructor
  · -- Forward: convergence to 0 implies all false
    intro hconv
    by_contra h_not_all
    push_neg at h_not_all
    obtain ⟨m, hm⟩ := h_not_all
    
    -- Key: if α m = true, then witness_simple α n ≥ 1 for all n ≥ m
    have h_ge_one : ∀ n ≥ m, witness_simple α n ≥ 1 := by
      intro n hn
      sorry -- TODO: Once α m = true, sum includes it
    
    -- But convergence with ε = 1/2 gives contradiction
    specialize hconv (1/2) (by norm_num : (0 : ℚ) < 1/2)
    obtain ⟨N, hN⟩ := hconv
    
    let n := max N m
    have : witness_simple α n < 1/2 := hN n (le_max_left _ _)
    have : witness_simple α n ≥ 1 := h_ge_one n (le_max_right _ _)
    -- Contradiction: 1 ≤ witness < 1/2
    linarith
    
  · -- Reverse: all false implies convergence
    intro h_all_false ε hε
    -- If all false, witness is always 0
    use 0
    intro n _
    -- witness_simple α n = 0 < ε
    have : witness_simple α n = 0 := by
      induction n with
      | zero => simp [witness_simple, h_all_false 0]
      | succ n ih => 
        simp [witness_simple, List.range]
        sorry -- TODO: Show sum stays 0
    rw [this]
    exact hε

/-- For c₀ in ℓ∞, we embed witness values -/
def witness_in_ell_infty (α : BinarySeq) : ℕ → RegularReal :=
  fun n => from_rat (witness_simple α n : ℚ)

/-- The witness sequence is bounded by n+1 -/
lemma witness_bounded (α : BinarySeq) :
  ∀ n, witness_simple α n ≤ n + 1 := by
  intro n
  induction n with
  | zero => simp [witness_simple]; split_ifs <;> norm_num
  | succ n ih =>
    simp [witness_simple, List.range]
    sorry -- TODO: Complete induction

end Papers.P2_BidualGap.Constructive