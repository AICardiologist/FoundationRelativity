/-
  Paper 61: Lang's Conjecture as the MP → BISH Gate
  Basic/Decidability.lean — Decidability hierarchy definitions

  Defines BISH, MP, and LPO as in Papers 23, 51.
  Self-contained: no cross-paper imports.
-/
import Mathlib.Tactic

namespace Papers.P61_LangBISH

/-! ## Omniscience Principles -/

/-- Limited Principle of Omniscience:
    For any binary sequence, either all terms are false, or some term is true.
    Classically trivial. Constructively: equivalent to "every bounded monotone
    sequence of reals converges" (Bridges–Vîță 2006). -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Markov's Principle for binary sequences:
    If a binary sequence is not all-false, then there exists n with α(n) = true.
    Accepted by the Russian constructive school. Weaker than LPO. -/
def MarkovPrinciple : Prop :=
  ∀ (α : ℕ → Bool), ¬(∀ n, α n = false) → ∃ n, α n = true

/-- A search problem is BISH-decidable with bound B if:
    the existence of a witness is equivalent to having a witness within [0, B].
    Once B is known, the search terminates by exhaustion — no omniscience needed. -/
def BISHDecidable (P : ℕ → Prop) (B : ℕ) : Prop :=
  (∃ n, P n) ↔ (∃ n, n ≤ B ∧ P n)

/-- BISH decidability from a computable bound. -/
theorem bish_decidable_of_bound {P : ℕ → Prop} [DecidablePred P] {B : ℕ}
    (hB : ∀ n, P n → n ≤ B) : BISHDecidable P B :=
  ⟨fun ⟨n, hn⟩ => ⟨n, hB n hn, hn⟩, fun ⟨n, _, hn⟩ => ⟨n, hn⟩⟩

/-! ## Hierarchy -/

/-- LPO implies Markov's Principle. -/
theorem lpo_implies_mp : LPO → MarkovPrinciple := by
  intro hLPO α hne
  rcases hLPO α with hall | ⟨n, hn⟩
  · exact absurd hall hne
  · exact ⟨n, hn⟩

end Papers.P61_LangBISH
