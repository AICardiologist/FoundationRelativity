/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  Defs/Markov.lean — Omniscience principle definitions and hierarchy

  Defines MarkovPrinciple (MP) and re-declares LPO, WLPO, LLPO as standalone
  definitions. Paper 22 is a self-contained bundle.

  Key hierarchy: LPO → {MP, WLPO → LLPO} (partial order, MP branches off)
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic

namespace Papers.P22

-- ========================================================================
-- Markov's Principle
-- ========================================================================

/-- Markov's Principle for binary sequences.
    If a sequence is not all zeros, then there exists an index where it is one.
    The hypothesis provides a negative fact (¬ all false);
    the conclusion provides a positive witness (∃ n, true).

    MP is accepted in the Russian constructive school (Markov, Shanin)
    but rejected in Brouwerian intuitionism and Bishop's BISH. -/
def MarkovPrinciple : Prop :=
  ∀ (α : ℕ → Bool), ¬(∀ n, α n = false) → ∃ n, α n = true

-- ========================================================================
-- LPO (Limited Principle of Omniscience)
-- ========================================================================

/-- Limited Principle of Omniscience.
    For every binary sequence, either all entries are false, or there
    exists an entry that is true. Re-declared locally. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

-- ========================================================================
-- WLPO (Weak Limited Principle of Omniscience)
-- ========================================================================

/-- Weak Limited Principle of Omniscience.
    For every binary sequence, either all entries are false, or it is
    not the case that all entries are false. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

-- ========================================================================
-- LLPO (Lesser Limited Principle of Omniscience)
-- ========================================================================

/-- A binary sequence has at most one `true` value. -/
def AtMostOne (α : ℕ → Bool) : Prop :=
  ∀ m n, α m = true → α n = true → m = n

/-- Lesser Limited Principle of Omniscience. -/
def LLPO : Prop :=
  ∀ (α : ℕ → Bool), AtMostOne α →
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)

-- ========================================================================
-- Hierarchy: LPO → MP, LPO → WLPO → LLPO
-- ========================================================================

/-- LPO implies Markov's Principle (trivial: LPO decides the disjunction outright). -/
theorem lpo_implies_mp : LPO → MarkovPrinciple := by
  intro hLPO α hne
  rcases hLPO α with hall | ⟨n, hn⟩
  · exact absurd hall hne
  · exact ⟨n, hn⟩

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

/-- LPO implies LLPO. -/
theorem lpo_implies_llpo : LPO → LLPO :=
  fun h => wlpo_implies_llpo (lpo_implies_wlpo h)

end Papers.P22
