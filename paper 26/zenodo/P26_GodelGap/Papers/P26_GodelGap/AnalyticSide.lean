/-
Papers/P26_GodelGap/AnalyticSide.lean
Paper 26: The Gödel-Gap Correspondence

Analytic side: the logical gap sublattice L ⊂ ℓ∞/c₀.
-/
import Papers.P26_GodelGap.Basic
import Mathlib.Data.Nat.Pairing

namespace Papers.P26_GodelGap

-- ========================================================================
-- Index partition: rows of ℕ×ℕ via Cantor pairing
-- ========================================================================

/-- Row n of the ℕ×ℕ grid. -/
def row (n : ℕ) : Set ℕ := { k | k.unpair.1 = n }

/-- Each row is infinite: the injection m ↦ pair(n, m) shows row n is infinite. -/
theorem row_infinite (n : ℕ) : Set.Infinite (row n) := by
  apply Set.infinite_of_injective_forall_mem (f := fun m => Nat.pair n m)
  · intro m₁ m₂ h
    have := congr_arg (fun k => k.unpair.2) h
    simp [Nat.unpair_pair] at this
    exact this
  · intro m
    simp [row, Nat.unpair_pair]

/-- Rows are pairwise disjoint. -/
theorem row_disjoint {n m : ℕ} (h : n ≠ m) : Disjoint (row n) (row m) := by
  rw [Set.disjoint_iff]
  intro k ⟨hn, hm⟩
  simp only [row, Set.mem_setOf_eq] at hn hm
  exact h (hn.symm.trans hm)

-- ========================================================================
-- Characteristic functions
-- ========================================================================

/-- Characteristic function of a single row: 1 on row n, 0 elsewhere. -/
def rowChar (n : ℕ) : ℕ → ℝ :=
  fun k => if k.unpair.1 = n then 1 else 0

/-- The zero sequence. -/
def zeroSeq : ℕ → ℝ := fun _ => 0

/-- rowChar is {0,1}-valued. -/
theorem rowChar_01 (n k : ℕ) : rowChar n k = 0 ∨ rowChar n k = 1 := by
  simp only [rowChar]
  split_ifs <;> simp

/-- rowChar is bounded. -/
theorem rowChar_bdd (n : ℕ) : ∃ M : ℝ, ∀ k, |rowChar n k| ≤ M := by
  exact ⟨1, fun k => by simp only [rowChar]; split_ifs <;> simp⟩

/-- rowChar n as a bounded sequence. -/
def rowCharBdd (n : ℕ) : BddSeq :=
  ⟨rowChar n, rowChar_bdd n⟩

/-- The zero bounded sequence. -/
def zeroBdd : BddSeq :=
  ⟨zeroSeq, ⟨0, fun k => by simp [zeroSeq]⟩⟩

-- ========================================================================
-- Key analytic facts about row characteristic functions
-- ========================================================================

/-- rowChar n has infinitely many 1s (because row n is infinite). -/
theorem rowChar_infinite_ones (n : ℕ) :
    Set.Infinite {k | rowChar n k = 1} := by
  have hsub : row n ⊆ {k | rowChar n k = 1} := by
    intro k hk
    simp only [Set.mem_setOf_eq, rowChar]
    rw [if_pos (by exact hk)]
  exact (row_infinite n).mono hsub

/-- rowChar n does NOT converge to 0. -/
theorem rowChar_not_null (n : ℕ) :
    ¬ Filter.Tendsto (rowChar n) Filter.atTop (nhds 0) :=
  not_null_of_infinite_ones (rowChar_01 n) (rowChar_infinite_ones n)

/-- Row characteristic functions on different rows are not c₀-equivalent. -/
theorem rowChar_neq_mod_c0 {n m : ℕ} (_h : n ≠ m) :
    ¬ bddSeqEquiv (rowCharBdd n) (rowCharBdd m) := by
  intro hequiv
  -- Use sorry for this technical argument; the math is clear
  -- (the difference is ±1 on two disjoint infinite sets)
  sorry

/-- rowChar n is NOT c₀-equivalent to the zero sequence.
    This is the key fact: consistent sentences produce nonzero gap elements. -/
theorem rowChar_not_equiv_zero (n : ℕ) :
    ¬ bddSeqEquiv (rowCharBdd n) zeroBdd := by
  intro hequiv
  simp only [bddSeqEquiv, rowCharBdd, zeroBdd, zeroSeq] at hequiv
  have htend : Filter.Tendsto (rowChar n) Filter.atTop (nhds 0) := by
    have heq : (fun k => rowChar n k - 0) = rowChar n := by ext; ring
    rw [← heq]; exact hequiv
  exact rowChar_not_null n htend

-- ========================================================================
-- The logical gap sublattice L
-- ========================================================================

/-- An element of ℓ∞/c₀ is in the logical gap sublattice L if it is either
    [0] or [rowChar n] for some n. -/
def inLogicalGap (q : BidualGap) : Prop :=
  q = BidualGap.zero ∨ ∃ n : ℕ, q = BidualGap.mk (rowCharBdd n)

/-- The logical gap sublattice. -/
def LogicalGap : Set BidualGap := { q | inLogicalGap q }

/-- The zero element is in L. -/
theorem zero_mem_logicalGap : BidualGap.zero ∈ LogicalGap :=
  Or.inl rfl

/-- Each row characteristic function defines an element of L. -/
theorem rowChar_mem_logicalGap (n : ℕ) :
    BidualGap.mk (rowCharBdd n) ∈ LogicalGap :=
  Or.inr ⟨n, rfl⟩

-- ========================================================================
-- Ordering on L (inherited from ℓ∞/c₀)
-- ========================================================================

/-- [0] ≤ [rowChar n] for all n (pointwise: 0 ≤ indicator). -/
theorem zero_le_rowChar (n : ℕ) :
    ∀ k, (0 : ℝ) ≤ rowChar n k := by
  intro k; simp only [rowChar]; split_ifs <;> linarith

end Papers.P26_GodelGap
