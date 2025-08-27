/-
  File: Papers/P3_2CatFramework/P4_Meta/StoneWindow_Calibration.lean

  Purpose:
  - Dyadic blocks B k: a disjoint-style decomposition scaffold of ℕ≥1
    via remainders modulo 2^(k+1).
  - A {0,1}-valued encoding e α built from a union of selected blocks.
  - Pointwise idempotency of e α and two basic sanity lemmas.

  Notes:
  - No density or ideal facts appear here.
  - No sorries and only elementary Nat lemmas are used.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Lattice

namespace Papers.P4Meta

open Set Classical

/-- Dyadic block `B k`: positive `n` with remainder `2^k` modulo `2^(k+1)`.
    Intuition: numbers of the form `2^k * (2m+1)`. -/
def dyadicBlock (k : ℕ) : Set ℕ :=
  {n | n ≠ 0 ∧ n % 2^(k+1) = 2^k}

notation "B" k => dyadicBlock k

/-! ### Tiny utilities -/

@[simp] lemma two_pow_pos (k : ℕ) : 0 < 2^k := by
  apply Nat.pow_pos
  decide

@[simp] lemma two_pow_ne_zero (k : ℕ) : (2^k : ℕ) ≠ 0 :=
  Nat.ne_of_gt (two_pow_pos k)

/-- `2^k` lies in `B k`. -/
lemma mem_B_pow (k : ℕ) : 2^k ∈ B k := by
  refine ⟨two_pow_ne_zero k, ?_⟩
  -- `2^k < 2^(k+1)` ⇒ the remainder is `2^k`
  have hlt : 2^k < 2^(k+1) := by
    rw [Nat.pow_succ]
    simp [Nat.lt_mul_iff_one_lt_right, two_pow_pos]
  exact Nat.mod_eq_of_lt hlt

/-!
  Encoding a `Prop`-valued bitstream `α : ℕ → Prop`:
  `encSet α` is the union of `B k` over those `k` with `α k`.
-/

/-- Set encoding of a bitstream `α`. -/
def encSet (α : ℕ → Prop) : Set ℕ :=
  {n | ∃ k, α k ∧ n ∈ B k}

/-- {0,1}-valued "idempotent" sequence obtained from `encSet α`. -/
noncomputable def e (α : ℕ → Prop) (n : ℕ) : ℕ :=
  if n ∈ encSet α then 1 else 0

/-! ### Pointwise facts about `e α` -/

@[simp] lemma e_of_mem {α : ℕ → Prop} {n : ℕ}
    (h : n ∈ encSet α) : e α n = 1 := by
  simp only [e, if_pos h]

@[simp] lemma e_of_not_mem {α : ℕ → Prop} {n : ℕ}
    (h : n ∉ encSet α) : e α n = 0 := by
  simp only [e, if_neg h]

/-- Pointwise idempotency: `(e α n)^2 = e α n` (written multiplicatively). -/
lemma e_idem (α : ℕ → Prop) (n : ℕ) :
    e α n * e α n = e α n := by
  by_cases h : n ∈ encSet α
  · simp [e_of_mem h]
  · simp [e_of_not_mem h]

/-- Convenience version for ergonomic rewriting. -/
@[simp] lemma e_idem' (α : ℕ → Prop) (n : ℕ) :
  (e α n) * (e α n) = e α n := e_idem α n

/-- If `α` is identically false, then `e α` is the zero sequence. -/
lemma e_zero_of_all_false {α : ℕ → Prop}
    (hα : ∀ k, ¬ α k) : ∀ n, e α n = 0 := by
  intro n
  apply e_of_not_mem
  intro hmem
  rcases hmem with ⟨k, hk, _⟩
  exact (hα k) hk

/-- If some bit of `α` is `true`, then `e α` takes the value `1` somewhere. -/
lemma e_nonzero_of_exists_true {α : ℕ → Prop}
    (hα : ∃ k, α k) : ∃ n, e α n = 1 := by
  rcases hα with ⟨k0, hk0⟩
  refine ⟨2^k0, ?_⟩
  exact e_of_mem ⟨k0, hk0, mem_B_pow k0⟩

/-!
  Remarks:
  * We avoid any density/ideal development here on purpose.
  * This module is a safe foundation for later calibrations (e.g. WLPO
    reductions from hypothetical surjectivity procedures).
-/

/-! ### Extra calibration lemmas (no density) -/

-- Membership monotonicity on encodings: if α ≤ β pointwise, then encSet α ⊆ encSet β.
lemma encSet_mono {α β : ℕ → Prop}
    (hαβ : ∀ k, α k → β k) :
    encSet α ⊆ encSet β := by
  intro n hn
  rcases hn with ⟨k, hk, hnBk⟩
  exact ⟨k, hαβ k hk, hnBk⟩

-- Pointwise monotonicity of the 0/1 encoding.
lemma e_mono {α β : ℕ → Prop}
    (hαβ : ∀ k, α k → β k) (n : ℕ) :
    e α n ≤ e β n := by
  by_cases h : n ∈ encSet α
  · have : n ∈ encSet β := encSet_mono hαβ h
    -- 1 ≤ 1, and 1 ≤ 0 never happens; both cases handled by simp
    simp [e_of_mem h, e_of_mem this]
  · -- 0 ≤ (0 or 1)
    simp [e_of_not_mem h]

-- A clean equivalence: the encoding is everywhere 0 iff the bitstream is identically false.
lemma e_zero_iff_all_false (α : ℕ → Prop) :
    (∀ n, e α n = 0) ↔ (∀ k, ¬ α k) := by
  constructor
  · intro h k hk
    -- If α k holds, 2^k is encoded to 1; contradicts the hypothesis.
    have enc1 : e α (2^k) = 1 := e_of_mem ⟨k, hk, mem_B_pow k⟩
    have enc0 : e α (2^k) = 0 := h (2^k)
    rw [enc1] at enc0
    -- Now enc0 says 1 = 0, which is a contradiction
    cases enc0
  · intro h n
    -- Directly from `e_zero_of_all_false`.
    exact e_zero_of_all_false h n

-- Another clean equivalence: there is a 1 in the encoding iff α has a true bit.
lemma e_exists_one_iff_exists_true (α : ℕ → Prop) :
    (∃ n, e α n = 1) ↔ (∃ k, α k) := by
  constructor
  · intro ⟨n, hn⟩
    -- If `e α n = 1`, then `n ∈ encSet α`, so ∃ k, α k.
    by_contra hnone
    -- `¬ (∃ k, α k)` ≡ `∀ k, ¬ α k` so encoding is everywhere 0.
    simp only [not_exists] at hnone
    have hzero : ∀ m, e α m = 0 := (e_zero_iff_all_false α).mpr hnone
    -- Contradiction with `hn`
    have : e α n = 0 := hzero n
    rw [hn] at this
    -- Now this says 1 = 0, which is a contradiction
    cases this
  · intro ⟨k, hk⟩
    exact e_nonzero_of_exists_true ⟨k, hk⟩

/-! ### Characterization lemmas -/

@[simp] lemma e_eq_one_iff {α : ℕ → Prop} {n : ℕ} :
    e α n = 1 ↔ n ∈ encSet α := by
  classical
  by_cases h : n ∈ encSet α
  · simp [e, h]
  · simp [e, h]

@[simp] lemma e_eq_zero_iff {α : ℕ → Prop} {n : ℕ} :
    e α n = 0 ↔ n ∉ encSet α := by
  classical
  by_cases h : n ∈ encSet α
  · simp [e, h]
  · simp [e, h]

lemma mem_encSet_pow {α : ℕ → Prop} {k : ℕ} (hk : α k) :
    2^k ∈ encSet α :=
  ⟨k, hk, mem_B_pow k⟩

end Papers.P4Meta