/-
  Paper 43: What the Ceiling Means — Constructive Schools,
  Physical Actualisation, and the Fine Structure of BISH+LPO
  Defs/Principles.lean — Omniscience principles and hierarchy

  Re-declares LPO, WLPO, LLPO, MP as standalone definitions.
  Paper 43 is a self-contained bundle.

  Key hierarchy: LPO → {MP, WLPO → LLPO} (partial order)
  FT is independent of all of these (Berger 2005).

  Partial order:
              LPO  (= WLPO + MP)
             /   \
          WLPO    MP
             \   /
              ??? (WLPO and MP are independent)
              |
             LLPO (independent of MP)
              |
             BISH
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Push

namespace Papers.P43

-- ========================================================================
-- Markov's Principle
-- ========================================================================

/-- Markov's Principle for binary sequences.
    From ¬(∀n, α(n) = false), extract ∃n, α(n) = true.
    Accepted by the Russian school. Rejected by Brouwer.
    Bishop takes no position. -/
def MarkovPrinciple : Prop :=
  ∀ (α : ℕ → Bool), ¬(∀ n, α n = false) → ∃ n, α n = true

-- ========================================================================
-- LPO, WLPO, LLPO
-- ========================================================================

/-- Limited Principle of Omniscience.
    For any binary sequence, either all terms are false, or some term is true.
    Rejected by both Brouwer and Markov. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Weak Limited Principle of Omniscience.
    For any binary sequence, either all terms are false, or not all are false.
    Weaker than LPO: does not provide a witness. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- A binary sequence has at most one `true` value. -/
def AtMostOne (α : ℕ → Bool) : Prop :=
  ∀ m n, α m = true → α n = true → m = n

/-- Lesser Limited Principle of Omniscience.
    For a binary sequence with at most one `true`, either
    all even-indexed or all odd-indexed entries are `false`. -/
def LLPO : Prop :=
  ∀ (α : ℕ → Bool), AtMostOne α →
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)

end Papers.P43
