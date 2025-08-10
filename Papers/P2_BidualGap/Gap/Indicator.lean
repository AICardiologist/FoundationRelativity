/-
Papers/P2_BidualGap/Gap/Indicator.lean

§3.1 Indicator function helpers (landing pad for equivalence proof)
Lightweight χ definition + preparatory lemmas (proof-free) for 
connecting finite symmetric difference to c₀ convergence.
-/
import Mathlib.Data.Real.Basic
import Papers.P2_BidualGap.Gap.IndicatorSpec

namespace Papers.P2.Gap.BooleanSubLattice

open Classical
variable (A B : Set ℕ)

/-- Indicator function: χ A n = 1 if n ∈ A, 0 otherwise. -/
noncomputable def χ (A : Set ℕ) : ℕ → ℝ := fun n => if n ∈ A then 1 else 0

/-- Indicator difference is bounded by 1. -/
lemma abs_indicator_diff_le_one (n : ℕ) : 
    |χ A n - χ B n| ≤ 1 := by
  simp only [χ]
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp [hA, hB]

/-- If n ∉ symmDiff A B then indicators agree. -/
lemma indicator_eq_of_not_mem_symmDiff {n : ℕ} 
    (hn : n ∉ symmDiff A B) : χ A n = χ B n := by
  simp only [symmDiff, Set.mem_union, Set.mem_diff, not_or] at hn
  obtain ⟨hnot_AB, hnot_BA⟩ := hn
  simp only [χ]
  -- If n ∉ (A \ B) ∪ (B \ A), then (n ∈ A ↔ n ∈ B)
  by_cases h : n ∈ A
  · -- n ∈ A, so n ∉ A \ B means n ∈ B
    have hB : n ∈ B := by
      by_contra hnB
      have : n ∈ A ∧ n ∉ B := ⟨h, hnB⟩
      have : n ∈ A \ B := this
      exact hnot_AB this
    simp [h, hB]
  · -- n ∉ A, so n ∉ B \ A means n ∉ B
    have hB : n ∉ B := by
      by_contra hnB  
      have : n ∈ B ∧ n ∉ A := ⟨hnB, h⟩
      have : n ∈ B \ A := this
      exact hnot_BA this
    simp [h, hB]

end Papers.P2.Gap.BooleanSubLattice