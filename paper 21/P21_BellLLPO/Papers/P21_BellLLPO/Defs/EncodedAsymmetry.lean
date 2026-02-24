/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  Defs/EncodedAsymmetry.lean — Encoded Bell asymmetry construction

  Given α : ℕ → Bool, we split it into even-indexed and odd-indexed
  subsequences, encode each as a real number via geometric series,
  and define the "Bell asymmetry" as their difference.

  The sign of the asymmetry (≤ 0 vs ≥ 0) determines which parity
  class contains the unique true value (if any).
-/
import Papers.P21_BellLLPO.Defs.LLPO
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

namespace Papers.P21

noncomputable section

-- ========================================================================
-- Even-indexed encoded field
-- ========================================================================

/-- The n-th term of the even-indexed encoded field:
    (1/2)^(n+1) if α(2n) = true, else 0. -/
def evenFieldTerm (α : ℕ → Bool) (n : ℕ) : ℝ :=
  if α (2 * n) = true then ((1 : ℝ) / 2) ^ (n + 1) else 0

/-- Each even field term is non-negative. -/
theorem evenFieldTerm_nonneg (α : ℕ → Bool) (n : ℕ) :
    0 ≤ evenFieldTerm α n := by
  unfold evenFieldTerm
  split
  · apply pow_nonneg; norm_num
  · exact le_refl _

/-- Each even field term is bounded by the geometric series. -/
theorem evenFieldTerm_le (α : ℕ → Bool) (n : ℕ) :
    evenFieldTerm α n ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
  unfold evenFieldTerm
  split
  · exact le_refl _
  · apply pow_nonneg; norm_num

-- ========================================================================
-- Odd-indexed encoded field
-- ========================================================================

/-- The n-th term of the odd-indexed encoded field:
    (1/2)^(n+1) if α(2n+1) = true, else 0. -/
def oddFieldTerm (α : ℕ → Bool) (n : ℕ) : ℝ :=
  if α (2 * n + 1) = true then ((1 : ℝ) / 2) ^ (n + 1) else 0

/-- Each odd field term is non-negative. -/
theorem oddFieldTerm_nonneg (α : ℕ → Bool) (n : ℕ) :
    0 ≤ oddFieldTerm α n := by
  unfold oddFieldTerm
  split
  · apply pow_nonneg; norm_num
  · exact le_refl _

/-- Each odd field term is bounded by the geometric series. -/
theorem oddFieldTerm_le (α : ℕ → Bool) (n : ℕ) :
    oddFieldTerm α n ≤ ((1 : ℝ) / 2) ^ (n + 1) := by
  unfold oddFieldTerm
  split
  · exact le_refl _
  · apply pow_nonneg; norm_num

-- ========================================================================
-- Summability (geometric comparison)
-- ========================================================================

/-- The geometric series (1/2)^(n+1) is summable. -/
theorem summable_half_pow_succ :
    Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ (n + 1)) := by
  have h := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 < 1)
  simp_rw [pow_succ]
  exact h.mul_right _

/-- The even field series is summable. -/
theorem evenField_summable (α : ℕ → Bool) :
    Summable (evenFieldTerm α) :=
  Summable.of_nonneg_of_le (evenFieldTerm_nonneg α) (evenFieldTerm_le α)
    summable_half_pow_succ

/-- The odd field series is summable. -/
theorem oddField_summable (α : ℕ → Bool) :
    Summable (oddFieldTerm α) :=
  Summable.of_nonneg_of_le (oddFieldTerm_nonneg α) (oddFieldTerm_le α)
    summable_half_pow_succ

-- ========================================================================
-- The encoded fields (tsum)
-- ========================================================================

/-- The even-indexed encoded field: Σₙ (if α(2n) then (1/2)^(n+1) else 0). -/
def evenField (α : ℕ → Bool) : ℝ :=
  ∑' n, evenFieldTerm α n

/-- The odd-indexed encoded field: Σₙ (if α(2n+1) then (1/2)^(n+1) else 0). -/
def oddField (α : ℕ → Bool) : ℝ :=
  ∑' n, oddFieldTerm α n

/-- The even field is non-negative. -/
theorem evenField_nonneg (α : ℕ → Bool) : 0 ≤ evenField α :=
  tsum_nonneg (evenFieldTerm_nonneg α)

/-- The odd field is non-negative. -/
theorem oddField_nonneg (α : ℕ → Bool) : 0 ≤ oddField α :=
  tsum_nonneg (oddFieldTerm_nonneg α)

-- ========================================================================
-- Zero-iff characterizations
-- ========================================================================

/-- The even field is zero iff all even-indexed entries are false. -/
theorem evenField_eq_zero_iff (α : ℕ → Bool) :
    evenField α = 0 ↔ ∀ n, α (2 * n) = false := by
  constructor
  · -- evenField = 0 → all even entries false
    intro hzero n
    by_contra hne
    push_neg at hne
    have htrue : α (2 * n) = true := by
      cases h : α (2 * n)
      · exact absurd h hne
      · rfl
    have hterm_pos : 0 < evenFieldTerm α n := by
      unfold evenFieldTerm; rw [if_pos htrue]
      apply pow_pos; norm_num
    have hpos : 0 < evenField α :=
      (evenField_summable α).tsum_pos (evenFieldTerm_nonneg α) n hterm_pos
    linarith
  · -- all even entries false → evenField = 0
    intro h_all
    have : evenFieldTerm α = fun _ => 0 := by
      ext n; unfold evenFieldTerm; rw [if_neg]; simp [h_all n]
    unfold evenField; rw [this, tsum_zero]

/-- The odd field is zero iff all odd-indexed entries are false. -/
theorem oddField_eq_zero_iff (α : ℕ → Bool) :
    oddField α = 0 ↔ ∀ n, α (2 * n + 1) = false := by
  constructor
  · intro hzero n
    by_contra hne
    push_neg at hne
    have htrue : α (2 * n + 1) = true := by
      cases h : α (2 * n + 1)
      · exact absurd h hne
      · rfl
    have hterm_pos : 0 < oddFieldTerm α n := by
      unfold oddFieldTerm; rw [if_pos htrue]
      apply pow_pos; norm_num
    have hpos : 0 < oddField α :=
      (oddField_summable α).tsum_pos (oddFieldTerm_nonneg α) n hterm_pos
    linarith
  · intro h_all
    have : oddFieldTerm α = fun _ => 0 := by
      ext n; unfold oddFieldTerm; rw [if_neg]; simp [h_all n]
    unfold oddField; rw [this, tsum_zero]

-- ========================================================================
-- The Bell asymmetry
-- ========================================================================

/-- The Bell asymmetry: difference between even-field and odd-field signals.
    Physically, this represents the imbalance between "Alice-side" and
    "Bob-side" contributions to the Bell violation, parameterized by α. -/
def bellAsymmetry (α : ℕ → Bool) : ℝ :=
  evenField α - oddField α

/-- The Bell sign decision: for every α with AtMostOne, the asymmetry
    has a decidable sign. This is the physical formulation of LLPO
    in the Bell nonlocality context. -/
def BellSignDecision : Prop :=
  ∀ (α : ℕ → Bool), AtMostOne α →
    bellAsymmetry α ≤ 0 ∨ 0 ≤ bellAsymmetry α

end
end Papers.P21
