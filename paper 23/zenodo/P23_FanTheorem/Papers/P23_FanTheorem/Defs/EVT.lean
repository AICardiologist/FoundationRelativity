/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  Defs/EVT.lean — Extreme Value Theorem and Fan Theorem definitions

  Key definitions:
    - EVT_max: every continuous f on [0,1] attains its maximum
    - EVT_min: every continuous f on [0,1] attains its minimum
    - CompactOptimization: every continuous f on [a,b] attains its minimum
    - FanTheorem := EVT_max (Berger 2005 equivalence, by definition)
-/
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Bounds.Basic

namespace Papers.P23

-- ========================================================================
-- The Extreme Value Theorem (two forms)
-- ========================================================================

/-- The Extreme Value Theorem (max form) on [0,1].
    Every continuous function on [0,1] attains its maximum. -/
def EVT_max : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
    ∃ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), f y ≤ f x

/-- The Extreme Value Theorem (min form) on [0,1].
    Every continuous function on [0,1] attains its minimum. -/
def EVT_min : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
    ∃ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), f x ≤ f y

-- ========================================================================
-- Compact optimization on arbitrary [a, b]
-- ========================================================================

/-- Compact optimization: every continuous function on [a,b] attains
    its minimum. This is the physical assertion — optimizing free energy
    over a compact parameter space. -/
def CompactOptimization : Prop :=
  ∀ (a b : ℝ), a < b →
    ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc a b) →
    ∃ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, f x ≤ f y

-- ========================================================================
-- The Fan Theorem (defined via EVT)
-- ========================================================================

/-- The Fan Theorem, defined via its EVT equivalent.
    The equivalence with the bar-theoretic Fan Theorem is due to
    Berger (2005) and Bridges–Vîță (2006).

    By defining FT := EVT_max rather than axiomatizing the equivalence,
    we achieve ZERO custom axioms in the formalization. -/
def FanTheorem : Prop := EVT_max

end Papers.P23
