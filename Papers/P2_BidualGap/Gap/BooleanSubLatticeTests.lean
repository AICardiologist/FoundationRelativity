/-
Papers/P2_BidualGap/Gap/BooleanSubLatticeTests.lean
Pin-safe smoke tests for the §3 residue-class partition.
-/
import Papers.P2_BidualGap.Gap.BooleanSubLattice

open Papers.P2.Gap.BooleanSubLattice

section

-- Coverage witness: every k lands in some residue class when 0 < n.
example (n k : ℕ) (hn : 0 < n) :
    ∃ r ∈ Finset.range n, k ∈ residueClass n r := by
  refine ⟨k % n, ?_, ?_⟩
  · exact Finset.mem_range.mpr (Nat.mod_lt k hn)
  · simp [residueClass]

-- Disjointness sanity: can't be in two different residue classes at once.
example (n r₁ r₂ k : ℕ) (hne : r₁ ≠ r₂)
    (h1 : k ∈ residueClass n r₁) (h2 : k ∈ residueClass n r₂) : False := by
  have hdis := residueClass_disjoint (n := n) (r₁ := r₁) (r₂ := r₂) hne
  exact (Set.disjoint_left.mp hdis) h1 h2

-- Basic membership test: 5 ∈ residue class 2 mod 3.
example : 5 ∈ residueClass 3 2 := by simp

-- Stability under adding one period: k ∈ U_r ⇒ k + n ∈ U_r.
example (n r k : ℕ) (hn : 0 < n) (hk : k ∈ residueClass n r) :
    k + n ∈ residueClass n r :=
  residueClass_add_period hn hk

-- Stability under adding multiple periods: k + n * m ∈ U_r.
example (n r k m : ℕ) (hn : 0 < n) (hk : k ∈ residueClass n r) :
    k + n * m ∈ residueClass n r :=
  residueClass_add_mul_period hn hk

-- Infinitude compiles directly from the lemma.
example (n r : ℕ) (hn : 0 < n) (hr : r < n) :
    (residueClass n r).Infinite :=
  residueClass_infinite (n := n) (r := r) hn hr

end