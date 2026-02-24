/-
  Paper 51: The Constructive Archimedean Rescue in BSD
  Principles.lean — Omniscience principles and BISH decidability

  Re-declares Markov's Principle and defines BISH decidability
  (bounded exhaustive search). Paper 51 is a self-contained bundle.

  The central thesis: the Archimedean metric converts MP-level
  search (unbounded) to BISH-level search (bounded). These
  definitions make that conversion precise.

  Re-stated from Paper 23 (Papers.P23.MarkovPrinciple).
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Basic

namespace Papers.P51

-- ========================================================================
-- Markov's Principle
-- ========================================================================

/-- Markov's Principle for binary sequences.
    If a binary sequence is not all-false, then there exists n
    with α(n) = true. Constructively weaker than LPO but sufficient
    for semi-decision procedures known to terminate.

    In BSD context: "if L'(E,1) ≠ 0, eventually find a Heegner prime"
    is an MP-level search (unbounded). The Archimedean rescue converts
    this to a bounded search. -/
def MarkovPrinciple : Prop :=
  ∀ (α : ℕ → Bool), ¬(∀ n, α n = false) → ∃ n, α n = true

-- ========================================================================
-- BISH Decidability (bounded exhaustive search)
-- ========================================================================

/-- A search problem is BISH-decidable with bound B if:
    the existence of a witness is equivalent to the existence of
    a witness within the bound.

    This is the key concept: once we have an explicit B, the search
    terminates by exhaustion over {0, ..., B}. No omniscience
    principle is needed — just a finite loop. -/
def BISHDecidable (P : ℕ → Prop) (B : ℕ) : Prop :=
  (∃ n, P n) ↔ (∃ n, n ≤ B ∧ P n)

/-- BISH decidability for a decidable predicate is constructively
    equivalent to computability: we can evaluate P(n) for each
    n ∈ {0, ..., B} and return the first witness (or certify none). -/
theorem bish_decidable_of_bound {P : ℕ → Prop} [DecidablePred P] {B : ℕ}
    (hB : ∀ n, P n → n ≤ B) : BISHDecidable P B :=
  ⟨fun ⟨n, hn⟩ => ⟨n, hB n hn, hn⟩, fun ⟨n, _, hn⟩ => ⟨n, hn⟩⟩

end Papers.P51
