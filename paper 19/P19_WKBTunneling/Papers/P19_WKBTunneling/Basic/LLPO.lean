/-
Papers/P19_WKBTunneling/Basic/LLPO.lean
Core omniscience principle definitions for Paper 19.

Defines LLPO (Lesser Limited Principle of Omniscience) and re-declares
LPO, WLPO, BMC as standalone definitions (Paper 19 is a self-contained bundle).

Key hierarchy: BISH < LLPO < WLPO < LPO
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic

namespace Papers.P19

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

    Equivalent to the Intermediate Value Theorem (Bridges-Richman 1987,
    Ishihara 1989). Strictly between BISH and LPO. -/
def LLPO : Prop :=
  ∀ (α : ℕ → Bool), AtMostOne α →
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)

/-- Typeclass for assuming LLPO. -/
class HasLLPO where
  llpo : LLPO

-- ========================================================================
-- LPO (Limited Principle of Omniscience) — re-declared
-- ========================================================================

/-- Limited Principle of Omniscience.
    For every binary sequence, either all entries are `false`, or there
    exists an entry that is `true`.

    Equivalent to Bounded Monotone Convergence (Bridges-Vîță 2006).
    Re-declared locally; Paper 8 has the canonical formalization. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Typeclass for assuming LPO. -/
class HasLPO where
  lpo : LPO

-- ========================================================================
-- WLPO (Weak Limited Principle of Omniscience) — re-declared
-- ========================================================================

/-- Weak Limited Principle of Omniscience.
    For every binary sequence, either all entries are `false`, or it is
    not the case that all entries are `false`.

    Strictly between LLPO and LPO. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- Typeclass for assuming WLPO. -/
class HasWLPO where
  wlpo : WLPO

-- ========================================================================
-- BMC (Bounded Monotone Convergence) — re-declared
-- ========================================================================

/-- Bounded Monotone Convergence: every bounded non-decreasing sequence
    of reals has a limit.
    Equivalent to LPO over BISH [Bridges-Vîță 2006].
    Re-declared locally; Paper 8 has the canonical formalization. -/
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

-- ========================================================================
-- Basic lemmas about AtMostOne
-- ========================================================================

/-- The identically false sequence has AtMostOne (vacuously). -/
lemma atMostOne_of_all_false {α : ℕ → Bool} (h : ∀ n, α n = false) :
    AtMostOne α := by
  intro m n hm _hn
  simp [h m] at hm

/-- A sequence with exactly one true at index k has AtMostOne. -/
lemma atMostOne_of_unique {α : ℕ → Bool} {k : ℕ}
    (_hk : α k = true) (huniq : ∀ n, α n = true → n = k) :
    AtMostOne α := by
  intro m n hm hn
  exact (huniq m hm).trans (huniq n hn).symm

end Papers.P19
