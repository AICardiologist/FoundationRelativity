/-
Papers/P19_WKBTunneling/Barrier/Definitions.lean
Core structures for potential barriers, classical turning points, and the
Turning Point Problem (TPP).

Design choice: we use plain ℝ with explicit range hypotheses instead of
Set.Icc subtypes to avoid coercion pain throughout the formalization.
-/
import Papers.P19_WKBTunneling.Basic.IVT
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace Papers.P19

-- ========================================================================
-- Barrier structure
-- ========================================================================

/-- A potential barrier on [0, 1].
    V is a continuous potential, E is the particle energy.
    The barrier satisfies:
    - V(0) < E  (particle is classically allowed at left endpoint)
    - V(c) > E  for some c ∈ [0,1] (barrier peak above energy)
    - V(1) < E  (particle is classically allowed at right endpoint) -/
structure Barrier where
  V : ℝ → ℝ
  hV_cont : Continuous V
  E : ℝ
  h_left : V 0 < E
  h_peak : ∃ c, 0 ≤ c ∧ c ≤ 1 ∧ V c > E
  h_right : V 1 < E

-- ========================================================================
-- Turning points
-- ========================================================================

/-- Classical turning points of a barrier: points x₁ < x₂ where V = E,
    with V > E in the interior (classically forbidden region). -/
structure TurningPoints (B : Barrier) where
  x₁ : ℝ
  x₂ : ℝ
  h_x₁_range : 0 ≤ x₁ ∧ x₁ ≤ 1
  h_x₂_range : 0 ≤ x₂ ∧ x₂ ≤ 1
  h_left_root : B.V x₁ = B.E
  h_right_root : B.V x₂ = B.E
  h_order : x₁ < x₂

-- ========================================================================
-- The Turning Point Problem
-- ========================================================================

/-- The Turning Point Problem (TPP): every barrier has turning points.
    This is the physical content that requires LLPO — finding where a
    general continuous potential crosses the energy level. -/
def TPP : Prop := ∀ (B : Barrier), Nonempty (TurningPoints B)

-- ========================================================================
-- Specific barrier: rectangular
-- ========================================================================

/-- A rectangular-like barrier: constant V₀ in the middle of [0,1],
    with explicit turning points at x₁ and x₂.
    Used for Part A (BISH computability). -/
structure SpecificBarrier where
  V : ℝ → ℝ
  hV_cont : Continuous V
  E : ℝ
  x₁ : ℝ
  x₂ : ℝ
  h_x₁_root : V x₁ = E
  h_x₂_root : V x₂ = E
  h_order : x₁ < x₂
  h_barrier : ∀ x, x₁ < x → x < x₂ → V x ≥ E

end Papers.P19
end
