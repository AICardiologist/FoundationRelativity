/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  Defs/EncodedField.lean — Binary encoding of external field

  Given α : ℕ → Bool, define:
    h_α = Σₙ (if α(n) then (1/2)^(n+1) else 0)

  Key property: h_α = 0  ⟺  ∀ n, α(n) = false
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

namespace Papers.P20

noncomputable section

/-- The term of the encoded field series. -/
def encodedFieldTerm (α : ℕ → Bool) (n : ℕ) : ℝ :=
  if α n then ((1 : ℝ) / 2) ^ (n + 1) else 0

/-- Each term of the encoded field is non-negative. -/
theorem encodedFieldTerm_nonneg (α : ℕ → Bool) (n : ℕ) :
    0 ≤ encodedFieldTerm α n := by
  unfold encodedFieldTerm
  split
  · apply pow_nonneg; norm_num
  · exact le_refl 0

/-- Each term is bounded by the geometric series (1/2)^(n+1). -/
theorem encodedFieldTerm_le (α : ℕ → Bool) (n : ℕ) :
    encodedFieldTerm α n ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
  unfold encodedFieldTerm
  split
  · exact le_refl _
  · apply pow_nonneg; norm_num

/-- The geometric series (1/2)^(n+1) is summable. -/
theorem summable_half_pow_succ :
    Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1)) := by
  have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
  simp_rw [pow_succ]
  exact h.mul_right _

/-- The encoded field series is summable (comparison with geometric series). -/
theorem encodedField_summable (α : ℕ → Bool) :
    Summable (encodedFieldTerm α) :=
  Summable.of_nonneg_of_le (encodedFieldTerm_nonneg α) (encodedFieldTerm_le α) summable_half_pow_succ

/-- The encoded external field: h_α = Σₙ (if α(n) then (1/2)^(n+1) else 0). -/
def encodedField (α : ℕ → Bool) : ℝ :=
  ∑' n, encodedFieldTerm α n

/-- The encoded field is non-negative. -/
theorem encodedField_nonneg (α : ℕ → Bool) : 0 ≤ encodedField α :=
  tsum_nonneg (encodedFieldTerm_nonneg α)

/-- If all terms are false, the encoded field is zero. -/
theorem encodedField_eq_zero_of_all_false (α : ℕ → Bool)
    (hall : ∀ n, α n = false) : encodedField α = 0 := by
  unfold encodedField
  have : encodedFieldTerm α = fun _ => 0 := by
    ext n; unfold encodedFieldTerm; simp [hall n]
  rw [this, tsum_zero]

/-- If the encoded field is zero, then all terms are false.
    Key argument: for non-negative summable functions, tsum = 0
    implies each term is 0 (via tsum_pos). -/
theorem all_false_of_encodedField_eq_zero (α : ℕ → Bool)
    (hzero : encodedField α = 0) : ∀ n, α n = false := by
  intro n
  by_contra hne
  -- α n ≠ false means α n = true
  push_neg at hne
  have htrue : α n = true := by
    cases h : α n
    · exact absurd h hne
    · rfl
  -- The n-th term is positive
  have hterm_pos : 0 < encodedFieldTerm α n := by
    unfold encodedFieldTerm; rw [if_pos htrue]
    apply pow_pos; norm_num
  -- But the sum of nonneg terms with a positive term is positive
  have hsum_pos : 0 < encodedField α := by
    unfold encodedField
    exact (encodedField_summable α).tsum_pos (encodedFieldTerm_nonneg α) n hterm_pos
  linarith

/-- The encoded field is zero if and only if all terms are false. -/
theorem encodedField_eq_zero_iff (α : ℕ → Bool) :
    encodedField α = 0 ↔ ∀ n, α n = false :=
  ⟨all_false_of_encodedField_eq_zero α, encodedField_eq_zero_of_all_false α⟩

end

end Papers.P20
