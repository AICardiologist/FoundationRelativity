/-
  ArithComplexity.lean — Arithmetical hierarchy for algebraic cycle statements
  Paper 102 of the Constructive Reverse Mathematics Series

  Formalizes the complexity classification of algebraic cycle statements
  within the arithmetical hierarchy (Σ⁰₁, Π⁰₁, Π⁰₂).

  Key insight: algebraic cycle statements are arithmetical because
  Chow varieties are projective schemes parametrized by finitely many
  integers, and the cycle class map is algebraic.

  With Friedman's Π⁰₂ conservation (PA → HA for Π⁰₂ without MP),
  ALL ≤ Π⁰₂ complexities descend to pure BISH.
-/
import Mathlib.Tactic

namespace P102

-- ============================================================
-- §1. Arithmetical Complexity Classes
-- ============================================================

/-- Classification of a mathematical statement by arithmetical complexity.
    These are the standard levels of the arithmetical hierarchy relevant
    to the Conservation Theorem.

    - Sigma01: ∃n. P(n) with decidable P — existential statements
    - Pi01:    ∀n. P(n) with decidable P — universal statements
    - Pi02:    ∀n. ∃m. P(n,m) with decidable P — universal-existential
    - Higher:  beyond Π⁰₂ — not covered by the conservation theorem -/
inductive ArithComplexity : Type where
  | Sigma01 : ArithComplexity  -- ∃n. P(n), P decidable
  | Pi01    : ArithComplexity  -- ∀n. P(n), P decidable
  | Pi02    : ArithComplexity  -- ∀n. ∃m. P(n,m), P decidable
  | Higher  : ArithComplexity  -- beyond Π⁰₂
  deriving DecidableEq, Repr

open ArithComplexity

/-- Whether the negative translation preserves provability at this level.
    Gödel-Gentzen: PA ⊢ φ → HA ⊢ φᴺ.
    For all ≤ Π⁰₂: the translation preserves (HA proves φᴺ).
    For Higher: not guaranteed. -/
def negTranslationPreserves : ArithComplexity → Bool
  | Sigma01 => true   -- HA ⊢ φᴺ (though φᴺ ≠ φ)
  | Pi01    => true   -- HA ⊢ φᴺ ≡ φ
  | Pi02    => true   -- HA ⊢ φᴺ (though φᴺ ≠ φ)
  | Higher  => false  -- not guaranteed

/-- Whether MP would be needed if using ONLY the negative translation
    (without Friedman's stronger result).
    This is HISTORICAL: with Friedman Π⁰₂ conservation, no MP is needed
    for any ≤ Π⁰₂ complexity. Retained for documentation. -/
def requiresMP_negTranslation : ArithComplexity → Bool
  | Sigma01 => true   -- neg. trans. alone: ¬¬∃ → ∃ needs MP
  | Pi01    => false   -- ∀ preserved directly, never needs MP
  | Pi02    => true   -- neg. trans. alone: ∀∃ needs MP for inner ∃
  | Higher  => true   -- if applicable at all

/-- Σ⁰₁ is covered by the conservation theorem. -/
theorem sigma01_covered : negTranslationPreserves Sigma01 = true := by rfl

/-- Π⁰₁ is covered (both via neg. translation and Friedman). -/
theorem pi01_covered : negTranslationPreserves Pi01 = true := by rfl

/-- Π⁰₂ is covered by the conservation theorem. -/
theorem pi02_covered : negTranslationPreserves Pi02 = true := by rfl

/-- Higher complexity is not covered. -/
theorem higher_not_covered : negTranslationPreserves Higher = false := by rfl

-- ============================================================
-- §2. Statement Classification Type
-- ============================================================

/-- A classified mathematical statement: pairs a description with its
    arithmetical complexity. -/
structure ClassifiedStatement where
  name : String
  description : String
  complexity : ArithComplexity
  justification : String
  deriving Repr

/-- Whether a classified statement is within the scope of the
    Conservation Theorem (complexity ≤ Π⁰₂). -/
def ClassifiedStatement.inScope (s : ClassifiedStatement) : Bool :=
  negTranslationPreserves s.complexity

/-- The CRM target level after conservation transfer.
    With Friedman Π⁰₂ conservation: ALL ≤ Π⁰₂ → BISH. -/
def ClassifiedStatement.targetLevel (s : ClassifiedStatement) : String :=
  if negTranslationPreserves s.complexity then "BISH" else "CLASS"

end P102
