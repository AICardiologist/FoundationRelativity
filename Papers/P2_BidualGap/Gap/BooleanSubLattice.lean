/-
Papers/P2_BidualGap/Gap/BooleanSubLattice.lean

Paper §3: Boolean Sublattice constructions (finite partition + later: indicators/embeddings)
This file provides the residue–class partition of ℕ used in §3.3.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Lattice  -- for Set.infinite_of_not_bddAbove

namespace Papers.P2.Gap.BooleanSubLattice

/-- Residue class for remainder `r` modulo `n`. -/
def residueClass (n r : ℕ) : Set ℕ := {k : ℕ | k % n = r}

/-- Each residue class is infinite when `0 < n` and `r < n`. -/
lemma residueClass_infinite {n r : ℕ} (hn : 0 < n) (hr : r < n) :
    (residueClass n r).Infinite := by
  -- We show "not bounded above" by producing, for any bound M, an element `> M`.
  apply Set.infinite_of_not_bddAbove
  intro hBdd
  rcases hBdd with ⟨M, hM⟩
  -- Take `k = r + n * (M+1)`. It lies in the residue class and is > M.
  set k := r + n * (M + 1) with hk
  have hk_mem : k ∈ residueClass n r := by
    have hmod_mul : (n * (M + 1)) % n = 0 := by
      rw [Nat.mul_mod, Nat.mod_self]
      simp
    have hmod_r : r % n = r := Nat.mod_eq_of_lt hr
    simp [residueClass, hk, Nat.add_mod, hmod_mul, hmod_r]
  have h1n : 1 ≤ n := Nat.succ_le_of_lt hn
  have hk_gt : M < k := by
    rw [hk]
    -- M < n*(M+1) ≤ r + n*(M+1)
    have h1 : M + 1 ≤ n * (M + 1) := by
      have : 1 * (M + 1) ≤ n * (M + 1) := Nat.mul_le_mul_right (M + 1) h1n
      rwa [Nat.one_mul] at this
    have h2 : M < n * (M + 1) :=
      lt_of_lt_of_le (Nat.lt_succ_self M) h1
    have h3 : n * (M + 1) ≤ r + n * (M + 1) := Nat.le_add_left _ _
    exact lt_of_lt_of_le h2 h3
  -- Contradiction with `k ≤ M`
  have : k < k := lt_of_le_of_lt (hM hk_mem) hk_gt
  exact lt_irrefl _ this

/-- Different residue classes are disjoint. -/
lemma residueClass_disjoint {n r₁ r₂ : ℕ} (hne : r₁ ≠ r₂) :
    Disjoint (residueClass n r₁) (residueClass n r₂) := by
  -- If k % n = r₁ and k % n = r₂ then r₁ = r₂.
  rw [Set.disjoint_left]
  intro k hk₁ hk₂
  simp [residueClass] at hk₁ hk₂
  have h1 : r₁ = k % n := hk₁.symm
  have h2 : k % n = r₂ := hk₂  
  have : r₁ = r₂ := h1.trans h2
  exact hne this

/-- The residue classes for remainders `0,1,…,n-1` cover ℕ (for `0 < n`). -/
lemma residueClass_cover {n : ℕ} (hn : 0 < n) :
    (⋃ r ∈ Finset.range n, residueClass n r) = Set.univ := by
  ext k
  -- choose r := k % n
  constructor
  · intro _; trivial
  · intro _
    refine ?_ 
    -- Build membership witnesses: r = k % n with r ∈ range n
    refine Set.mem_iUnion.mpr ?_
    refine ⟨k % n, ?_⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt k hn), ?_⟩
    simp [residueClass]

@[simp] lemma mem_residueClass {n r k : ℕ} :
  k ∈ residueClass n r ↔ k % n = r := Iff.rfl

/-- Stability under adding one period: if `k % n = r` then `(k + n) % n = r`. -/
lemma residueClass_add_period {n r k : ℕ}
    (hn : 0 < n) (hk : k ∈ residueClass n r) :
    k + n ∈ residueClass n r := by
  have hk' : k % n = r := by simpa [residueClass] using hk
  have hlt : k % n < n := Nat.mod_lt k hn
  -- (k + n) % n = (k % n + n % n) % n = ((k % n) + 0) % n = k % n
  have : (k + n) % n = k % n := by simp
  simp [residueClass, hk', this]

/-- Stability under adding multiple periods: k + n * m has same residue as k. -/
lemma residueClass_add_mul_period {n r k m : ℕ}
    (hn : 0 < n) (hk : k ∈ residueClass n r) :
    k + n * m ∈ residueClass n r := by
  induction m with
  | zero =>
      simpa [Nat.mul_zero, Nat.add_zero] using hk
  | succ m ih =>
      -- k + n * (m+1) = (k + n * m) + n
      simpa [Nat.mul_succ, Nat.add_assoc] using
        residueClass_add_period (n := n) (r := r) (k := k + n * m) hn ih

end Papers.P2.Gap.BooleanSubLattice