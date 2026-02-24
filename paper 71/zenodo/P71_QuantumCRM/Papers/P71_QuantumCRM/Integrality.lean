/-
  Paper 71 — Engineering Consequences of the Archimedean Principle
  Integrality.lean: The sum-of-integer-squares lemma

  Core mathematical theorem: if integers v₁², ..., vₙ² sum to 1,
  then exactly one vᵢ is ±1 and all others are 0. This is the
  algebraic content of the signed permutation theorem: integer
  orthogonal matrices have rows with exactly one ±1 entry.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset

-- ============================================================
-- Helper: v^2 = 1 over ℤ implies v = ±1
-- ============================================================

private theorem int_sq_eq_one (v : Int) (h : v ^ 2 = 1) : v = 1 ∨ v = -1 := by
  have h1 : (v - 1) * (v + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with h2 | h2 <;> omega

-- ============================================================
-- The sum-of-squares lemma for natural numbers
-- ============================================================

/-- If natural numbers v₀, ..., v_{n-1} sum to 1, then exactly one
    equals 1 and the rest equal 0. -/
theorem Fin.sum_eq_one_iff {n : Nat} (v : Fin n → Nat)
    (h : ∑ i : Fin n, v i = 1) :
    ∃ j : Fin n, v j = 1 ∧ ∀ k : Fin n, k ≠ j → v k = 0 := by
  -- Find a nonzero term
  have hne : ∃ j ∈ univ, v j ≠ 0 := by
    by_contra h'
    push_neg at h'
    have : ∀ i : Fin n, v i = 0 := fun i => h' i (mem_univ i)
    simp [this] at h
  obtain ⟨j, _, hj⟩ := hne
  refine ⟨j, ?_, ?_⟩
  · have hle : v j ≤ ∑ i : Fin n, v i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (v i)) (mem_univ j)
    rw [h] at hle; omega
  · -- Decompose: sum = v j + ∑_{i ≠ j} v i
    intro k hk
    have hj1 : v j = 1 := by
      have hle : v j ≤ ∑ i : Fin n, v i :=
        Finset.single_le_sum (fun i _ => Nat.zero_le (v i)) (mem_univ j)
      rw [h] at hle; omega
    have hdecomp := Finset.add_sum_erase univ v (mem_univ j)
    -- ∑_{i ≠ j} v i = 0
    have hrest : ∑ i ∈ univ.erase j, v i = 0 := by omega
    -- v k ≤ ∑_{i ≠ j} v i = 0
    have hk_in : k ∈ univ.erase j := mem_erase.mpr ⟨hk, mem_univ k⟩
    have hkle : v k ≤ ∑ i ∈ univ.erase j, v i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (v i)) hk_in
    omega

-- ============================================================
-- The signed permutation row lemma (integer version)
-- ============================================================

/-- If integer squares v₁², ..., vₙ² sum to 1, then exactly one
    vᵢ is ±1 and all others are 0.

    This is the row condition for signed permutation matrices:
    each row of an integer orthogonal matrix has exactly one
    nonzero entry, which is ±1. -/
theorem int_sq_sum_one {n : Nat} (v : Fin n → Int)
    (h : ∑ i : Fin n, v i ^ 2 = 1) :
    ∃ j : Fin n, (v j = 1 ∨ v j = -1) ∧ ∀ k : Fin n, k ≠ j → v k = 0 := by
  -- Find j with v j ≠ 0
  have hne : ∃ j ∈ univ, v j ^ 2 ≠ 0 := by
    by_contra h'; push_neg at h'
    have : ∀ i : Fin n, v i ^ 2 = 0 := fun i => h' i (mem_univ i)
    simp [this] at h
  obtain ⟨j, _, hj⟩ := hne
  -- v j ^ 2 ≤ sum = 1
  have hle : v j ^ 2 ≤ ∑ i : Fin n, v i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (mem_univ j)
  rw [h] at hle
  -- v j ^ 2 ≥ 1 (nonzero integer squared)
  have hvj : v j ≠ 0 := fun heq => by simp [heq] at hj
  have hge : 1 ≤ v j ^ 2 := by
    by_contra h'; push_neg at h'
    have : v j ^ 2 = 0 := by linarith [sq_nonneg (v j)]
    have : v j * v j = 0 := by nlinarith
    exact hvj (mul_self_eq_zero.mp this)
  have hjsq : v j ^ 2 = 1 := by linarith
  refine ⟨j, int_sq_eq_one _ hjsq, ?_⟩
  -- For k ≠ j: decompose and show v k ^ 2 = 0
  intro k hk
  have hdecomp := Finset.add_sum_erase univ (fun i => v i ^ 2) (mem_univ j)
  -- Normalize beta-redexes in hdecomp
  simp only [] at hdecomp
  -- ∑_{i ≠ j} v i ^ 2 = 0
  have hrest : ∑ i ∈ univ.erase j, v i ^ 2 = 0 := by linarith
  have hk_in : k ∈ univ.erase j := mem_erase.mpr ⟨hk, mem_univ k⟩
  have hkle : v k ^ 2 ≤ ∑ i ∈ univ.erase j, v i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (v i)) hk_in
  -- v k ^ 2 ≤ 0 and v k ^ 2 ≥ 0, so v k ^ 2 = 0
  have hksq : v k ^ 2 = 0 := by linarith [sq_nonneg (v k)]
  have : v k * v k = 0 := by nlinarith
  exact mul_self_eq_zero.mp this
