/-
Papers/P7_PhysicalBidualGap/Basic.lean
Core definitions for Paper 7: Physical Bidual Gap.

Defines WLPO and classical reflexivity (surjectivity of the canonical
embedding J_X : X → X**) used throughout the formalization.
-/
import Mathlib.Analysis.Normed.Module.Dual

universe u

namespace Papers.P7

open NormedSpace

-- ========================================================================
-- Logical principles
-- ========================================================================

/-- Weak Limited Principle of Omniscience. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

-- ========================================================================
-- Reflexivity
-- ========================================================================

/-- A normed space X is reflexive if the canonical embedding J_X : X → X**
    is surjective. Uses Mathlib's `inclusionInDoubleDual`. -/
def IsReflexive (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X] : Prop :=
  Function.Surjective (inclusionInDoubleDual 𝕜 X)

end Papers.P7
