/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  Defs/LLPO.lean — Omniscience principle definitions and hierarchy

  Defines LLPO (Lesser Limited Principle of Omniscience) and re-declares
  LPO, WLPO as standalone definitions. Paper 24 is a self-contained bundle.

  Key hierarchy: BISH ⊊ LLPO ⊊ WLPO ⊊ LPO
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic

namespace Papers.P24

-- ========================================================================
-- AtMostOne predicate
-- ========================================================================

/-- A binary sequence has at most one `true` value.
    This is the precondition for LLPO: given α with at most one 1,
    decide whether the 1 (if any) is at an even or odd index. -/
def AtMostOne (α : ℕ → Bool) : Prop :=
  ∀ m n, α m = true → α n = true → m = n

-- ========================================================================
-- LLPO (Lesser Limited Principle of Omniscience)
-- ========================================================================

/-- Lesser Limited Principle of Omniscience.
    For every binary sequence with at most one `true`, either all
    even-indexed entries are `false`, or all odd-indexed entries are `false`.

    Equivalent to the real sign decision x ≤ 0 ∨ 0 ≤ x
    (Ishihara 2006, Bridges–Richman 1987). -/
def LLPO : Prop :=
  ∀ (α : ℕ → Bool), AtMostOne α →
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)

-- ========================================================================
-- LPO (Limited Principle of Omniscience)
-- ========================================================================

/-- Limited Principle of Omniscience.
    For every binary sequence, either all entries are `false`, or there
    exists an entry that is `true`. Re-declared locally. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

-- ========================================================================
-- WLPO (Weak Limited Principle of Omniscience)
-- ========================================================================

/-- Weak Limited Principle of Omniscience.
    For every binary sequence, either all entries are `false`, or it is
    not the case that all entries are `false`. Re-declared locally. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

-- ========================================================================
-- Hierarchy: LPO → WLPO → LLPO
-- ========================================================================

/-- LPO implies WLPO. -/
theorem lpo_implies_wlpo : LPO → WLPO := by
  intro hLPO α
  rcases hLPO α with h_all | ⟨n, hn⟩
  · exact Or.inl h_all
  · right
    intro h_all
    exact absurd (h_all n) (by simp [hn])

/-- WLPO implies LLPO. -/
theorem wlpo_implies_llpo : WLPO → LLPO := by
  intro hWLPO α hamo
  let β : ℕ → Bool := fun n => α (2 * n)
  rcases hWLPO β with h_all | h_not_all
  · exact Or.inl h_all
  · right
    intro j
    by_contra h
    push_neg at h
    simp at h
    apply h_not_all
    intro k
    by_contra hk
    push_neg at hk
    simp at hk
    have := hamo (2 * k) (2 * j + 1) hk h
    omega

/-- LPO implies LLPO (via WLPO or directly). -/
theorem lpo_implies_llpo : LPO → LLPO :=
  fun h => wlpo_implies_llpo (lpo_implies_wlpo h)

-- ========================================================================
-- Basic lemma about AtMostOne
-- ========================================================================

/-- The identically false sequence has AtMostOne (vacuously). -/
lemma atMostOne_of_all_false {α : ℕ → Bool} (h : ∀ n, α n = false) :
    AtMostOne α := by
  intro m n hm _hn
  simp [h m] at hm

end Papers.P24
