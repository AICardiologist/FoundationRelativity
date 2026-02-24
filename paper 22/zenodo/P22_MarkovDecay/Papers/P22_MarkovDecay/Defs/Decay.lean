/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  Defs/Decay.lean — Physical definitions for radioactive decay

  survivalProb(λ, t) = exp(-λ · t)
  detectionTime(ε, q) = ln(1/ε) / q
  EventualDecay: for nonzero decay rate, survival drops below any threshold
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Papers.P22

noncomputable section

/-- Survival probability: P(t, λ) = exp(-λ · t).
    For a radioactive nucleus with decay rate λ, the probability of
    surviving until time t. -/
def survivalProb (lambda_ t : ℝ) : ℝ :=
  Real.exp (-(lambda_ * t))

/-- Detection time: T(ε, q) = ln(1/ε) / q.
    Given a lower bound q > 0 on the decay rate and a threshold ε ∈ (0,1),
    this is the time after which survival probability is at most ε. -/
def detectionTime (eps q : ℝ) : ℝ :=
  Real.log (1 / eps) / q

/-- Eventual decay: for any non-negative decay rate that is not zero,
    the survival probability eventually drops below any threshold.

    Note: the hypothesis is λ ≥ 0 ∧ λ ≠ 0 (nonzero nonneg rate),
    not λ > 0 (positive with explicit lower bound). The gap between
    these is exactly where MP operates. -/
def EventualDecay : Prop :=
  ∀ (lambda_ : ℝ), 0 ≤ lambda_ → lambda_ ≠ 0 →
    ∀ (eps : ℝ), 0 < eps → eps < 1 →
      ∃ (T : ℝ), 0 < T ∧ survivalProb lambda_ T < eps

end

end Papers.P22
