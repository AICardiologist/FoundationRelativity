/-
  Paper 28: Newton vs. Lagrange — Constructive Stratification of Classical Mechanics
  Defs.lean — Core definitions

  Defines the Fan Theorem (re-stated from Paper 23), harmonic oscillator
  parameters, and the discrete action functional for N=2 time steps.

  Key insight: with N=2, there is exactly one free interior node q₁ ∈ [0,1],
  making the domain one-dimensional and directly compatible with Paper 23's
  EVT on [0,1].
-/
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Papers.P28

-- ========================================================================
-- Fan Theorem and EVT (re-stated from Paper 23)
-- ========================================================================

/-- The Extreme Value Theorem (max form) on [0,1].
    Every continuous function on [0,1] attains its maximum.
    Re-stated from Paper 23 (Papers.P23.EVT_max). -/
def EVT_max : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
    ∃ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), f y ≤ f x

/-- The Extreme Value Theorem (min form) on [0,1].
    Every continuous function on [0,1] attains its minimum.
    Re-stated from Paper 23 (Papers.P23.EVT_min). -/
def EVT_min : Prop :=
  ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
    ∃ x ∈ Set.Icc (0 : ℝ) (1 : ℝ), ∀ y ∈ Set.Icc (0 : ℝ) (1 : ℝ), f x ≤ f y

/-- The Fan Theorem, defined as EVT_max.
    The equivalence with the bar-theoretic Fan Theorem is due to
    Berger (2005) and Bridges–Vîță (2006).
    Re-stated from Paper 23 (Papers.P23.FanTheorem). -/
def FanTheorem : Prop := EVT_max

-- ========================================================================
-- Harmonic Oscillator Parameters
-- ========================================================================

/-- Harmonic oscillator parameters for the discrete mechanics formalization.
    - m : mass (positive)
    - k : spring constant (positive)
    - A, B : boundary positions in [0,1] (endpoints of the discrete path)
    The system uses N=2 time steps on [0,1], so Δt = 1/2 and
    q₀ = A, q₂ = B are fixed, with q₁ as the single free variable. -/
structure HOParams where
  m : ℝ
  k : ℝ
  A : ℝ
  B : ℝ
  hm : 0 < m
  hk : 0 < k
  hA : A ∈ Set.Icc (0 : ℝ) 1
  hB : B ∈ Set.Icc (0 : ℝ) 1

-- ========================================================================
-- Discrete Action Functional (N=2)
-- ========================================================================

/-- Discrete harmonic action for N=2 time steps, T=1, Δt=1/2.

    The Lagrangian is L(q, q̇, t) = (m/2)q̇² − (k/2)q².
    With q₀ = A, q₁ = q (free), q₂ = B, Δt = 1/2:

      S(q) = Σᵢ₌₀¹ L(qᵢ, (qᵢ₊₁ − qᵢ)/Δt, tᵢ) · Δt

    Expanding:
      S(q) = [m/2 · ((q−A)/(1/2))² − k/2 · A²] · (1/2)
           + [m/2 · ((B−q)/(1/2))² − k/2 · q²] · (1/2)
           = m · (q−A)² + m · (B−q)² − (k/4) · (A² + q²)

    This is a quadratic polynomial in q, hence continuous on [0,1]. -/
noncomputable def harmonicAction2 (p : HOParams) (q : ℝ) : ℝ :=
  p.m * (q - p.A) ^ 2 + p.m * (p.B - q) ^ 2 - p.k / 4 * (p.A ^ 2 + q ^ 2)

end Papers.P28
