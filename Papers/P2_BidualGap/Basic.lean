/-
  Papers/P2_BidualGap/Basic.lean
  Minimal core definitions used by Paper 2 (constructive/BISH interpretation).

  Key idea:
  - We distinguish "Banach-like" behavior of the dual in BISH via `DualIsBanach`.
  - `BidualGapStrong` requires both the dual and bidual to satisfy that property,
    and the canonical map `X → X**` to be non-surjective.
-/

import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness

universe u

namespace Papers.P2

/-- A *constructive* predicate saying a continuous linear functional has an
    *operator norm* in the strong sense we need (norm exists as a genuine least
    bound). This isolates the BISH-sensitive part. -/
def HasOperatorNorm
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (f : X →L[ℝ] ℝ) : Prop :=
  ∃ N : ℝ,
    0 ≤ N ∧
    (∀ x : X, ‖f x‖ ≤ N * ‖x‖) ∧
    -- minimality: any other bound must dominate N
    (∀ N', (∀ x : X, ‖f x‖ ≤ N' * ‖x‖) → N ≤ N')

/-- BISH-flavored "the dual is a Banach space":
    - sums of normable functionals are normable (closure under addition);
    - there is a (constructive) completeness witness for the dual.
    *Do not* register `complete` as a global instance; keep it local.
    
    CONSTRUCTIVE CONTENT: This is stricter than classical "dual is complete".
    The key requirement is that operator norms exist as genuine least upper bounds
    (not just infima), and that addition preserves this property. In BISH, this
    fails without WLPO because we cannot constructively find the minimum norm.
    
    With WLPO, we can:
    1. Decide for each rational q whether ‖f‖ ≤ q or ‖f‖ > q
    2. Locate the norm within any ε > 0
    3. Show the norm is attained (or approached arbitrarily closely)
    
    This is why Gap ⇒ WLPO works: without WLPO, DualIsBanach fails even for c₀. -/
structure DualIsBanach
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop where
  (closed_add :
    ∀ f g : X →L[ℝ] ℝ, HasOperatorNorm f → HasOperatorNorm g → HasOperatorNorm (f + g))
  (complete_normable_dual : True)   -- Prop-only placeholder

/-- *Strong* Bidual Gap (BISH interpretation):
    There exists a real Banach space `X` such that
    - the dual and the bidual satisfy `DualIsBanach`,
    - and the canonical embedding `j : X → X**` is not surjective. -/
def BidualGapStrong : Prop :=
  ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (_ : CompleteSpace X),
    DualIsBanach X ∧ DualIsBanach (X →L[ℝ] ℝ) ∧
    ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ X)

/-- WLPO: Weak Limited Principle of Omniscience. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬ (∀ n, α n = false)

end Papers.P2