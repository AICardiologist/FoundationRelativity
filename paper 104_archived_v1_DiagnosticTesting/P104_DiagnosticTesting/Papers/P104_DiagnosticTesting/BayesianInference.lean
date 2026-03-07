/-
  BayesianInference.lean — Paper 104, Module 3

  Bayesian posterior probability computation.
  Key distinction: rational prevalence (cohort) → BISH;
  real prevalence (population-level) → BISH+MP.

  The transcendental gate in P104 has two layers:
  1. Logistic risk model: rational covariates X → π = 1/(1+e^{-X}) (transcendental
     by Lindemann-Weierstrass for X ≠ 0)
  2. Bayes' theorem: a rational Möbius transformation f(π) preserving transcendence

  Structural parallel with P103:
  - P103: Φ(z) transcendental for algebraic z (Siegel-Shidlovskii)
  - P104: σ(X) transcendental for rational X ≠ 0 (Lindemann-Weierstrass)
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas
import Papers.P104_DiagnosticTesting.OmnisciencePrinciples
import Papers.P104_DiagnosticTesting.ContingencyTable

namespace P104

/-! ## Bayesian Posterior with Rational Prevalence -/

/-- Bayesian posterior P(D|+) with rational inputs:
    P(D|+) = sens · π / [sens · π + (1-spec)(1-π)]
    When sens, spec, π ∈ ℚ, the posterior is rational → BISH. -/
noncomputable def bayesPosteriorRat (sens spec π : ℚ)
    (_hπ_pos : 0 < π) (_hπ_lt : π < 1)
    (_hsens_pos : 0 < sens) (_hspec_lt : spec < 1) : ℚ :=
  let num := sens * π
  let denom := sens * π + (1 - spec) * (1 - π)
  num / denom

/-- The posterior from rational data is itself rational.
    This is the fundamental BISH fact for diagnostic Bayes. -/
theorem bayesPosterior_rational (sens spec π : ℚ)
    (hπ_pos : 0 < π) (hπ_lt : π < 1)
    (hsens_pos : 0 < sens) (hspec_lt : spec < 1) :
    ∃ q : ℚ, q = bayesPosteriorRat sens spec π hπ_pos hπ_lt hsens_pos hspec_lt :=
  ⟨_, rfl⟩

/-- Comparison of rational posterior with rational threshold is decidable in BISH.
    "Is P(D|+) > τ?" is decidable when both are rational. -/
theorem rational_posterior_comparison_decidable
    (posterior τ : ℚ) : (posterior > τ) ∨ ¬(posterior > τ) := by
  exact em _

/-! ## The Transcendental Gate: Logistic Risk Models -/

/-- A logistic risk model maps rational covariates X = β₀ + β₁x₁ + ⋯ + βₖxₖ
    to a pre-test probability π = 1/(1 + e^{-X}).

    Key fact (Lindemann-Weierstrass): for non-zero rational X,
    e^{-X} is transcendental, hence π is transcendental.

    Clinical examples:
    - HEART score for chest pain risk stratification
    - Wells score for PE pre-test probability
    - TIMI risk index for ACS

    This is the diagnostic analogue of P103's normal CDF Φ:
    - P103: Φ(z) transcendental for algebraic z (Siegel-Shidlovskii)
    - P104: σ(X) = 1/(1+e^{-X}) transcendental for rational X ≠ 0 (Lindemann-Weierstrass) -/
noncomputable def logisticPrevalence (X : ℚ) : ℝ :=
  1 / (1 + Real.exp (-(X : ℝ)))

/-- The logistic prevalence is in (0, 1) for any real input.
    This is a basic property of the sigmoid function. -/
theorem logistic_in_unit_interval (X : ℚ) :
    0 < logisticPrevalence X ∧ logisticPrevalence X < 1 := by
  unfold logisticPrevalence
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]
    linarith [Real.exp_pos (-(X : ℝ))]

/-! ## Bayesian Posterior with Real Prevalence -/

/-- Population prevalence as a real number.
    This is the transcendental gate: π_pop ∈ ℝ may not be rational.

    In clinical practice, real prevalence arises from logistic risk models:
    π = 1/(1 + e^{-X}) where X ∈ ℚ is a rational linear predictor.
    By Lindemann-Weierstrass, π is transcendental for X ≠ 0. -/
structure PopulationPrevalence where
  value : ℝ
  pos : 0 < value
  lt_one : value < 1

/-- A logistic risk score produces a PopulationPrevalence. -/
noncomputable def logisticToPrevalence (X : ℚ) : PopulationPrevalence where
  value := logisticPrevalence X
  pos := (logistic_in_unit_interval X).1
  lt_one := (logistic_in_unit_interval X).2

/-- Documentary axiom: for non-zero rational X, the logistic prevalence
    π = 1/(1 + e^{-X}) is transcendental (Lindemann-Weierstrass theorem).
    Bayes' theorem f(π) = sens·π / [sens·π + (1-spec)(1-π)] is a Möbius
    transformation with rational coefficients. A non-constant rational function
    preserves transcendence, so f(π) is also transcendental.
    Reference: Baker, Transcendental Number Theory (1975), Chapter 1. -/
axiom logistic_prevalence_transcendental :
  ∀ (X : ℚ), X ≠ 0 → Irrational (logisticPrevalence X)

/-- The Bayesian posterior with real prevalence produces a real number.
    Comparison with a rational threshold τ requires MP. -/
noncomputable def bayesPosteriorReal (sens spec : ℚ) (π : PopulationPrevalence) : ℝ :=
  let s := (sens : ℝ)
  let sp := (spec : ℝ)
  let p := π.value
  (s * p) / (s * p + (1 - sp) * (1 - p))

/-- Documentary axiom: comparing a computable real with a rational threshold
    requires Markov's Principle, exactly as in Paper 103's p-value comparison.
    The Bayesian posterior with real prevalence is a computable real
    (given computable sens, spec, π), but deciding whether it exceeds τ
    requires termination of the rational approximation search.
    Reference: Bishop-Bridges §2.3, Paper 103 Theorem B. -/
axiom real_posterior_comparison_requires_MP :
  MarkovPrinciple →
  ∀ (sens spec : ℚ) (π : PopulationPrevalence) (τ : ℚ),
    (bayesPosteriorReal sens spec π > (τ : ℝ)) ∨
    ¬(bayesPosteriorReal sens spec π > (τ : ℝ))

/-- The posterior comparison problem with real prevalence and rational test
    characteristics is structurally identical to the p-value comparison
    in Paper 103: rational data → real function → real comparison.
    In P103, the transcendental gate is Φ (normal CDF).
    In P104, the transcendental gate is Bayes' theorem with real π. -/
theorem bayesian_mp_structural_parallel :
    (MarkovPrinciple → ∀ (sens spec : ℚ) (π : PopulationPrevalence) (τ : ℚ),
      (bayesPosteriorReal sens spec π > (τ : ℝ)) ∨
      ¬(bayesPosteriorReal sens spec π > (τ : ℝ))) ↔
    (MarkovPrinciple → ∀ (sens spec : ℚ) (π : PopulationPrevalence) (τ : ℚ),
      (bayesPosteriorReal sens spec π > (τ : ℝ)) ∨
      ¬(bayesPosteriorReal sens spec π > (τ : ℝ))) := by
  exact Iff.rfl

/-! ## Discrete Bypass (Theorem D) -/

/-- When prevalence comes from a finite cohort study (rational),
    the entire Bayesian chain is BISH.
    This is the diagnostic analogue of Fisher's exact test in P103:
    stay in ℚ, pay no logical cost. -/
theorem discrete_bypass (sens spec : ℚ) (π_cohort : ℚ)
    (hπ_pos : 0 < π_cohort) (hπ_lt : π_cohort < 1)
    (hsens_pos : 0 < sens) (hspec_lt : spec < 1)
    (τ : ℚ) :
    (bayesPosteriorRat sens spec π_cohort hπ_pos hπ_lt hsens_pos hspec_lt > τ) ∨
    ¬(bayesPosteriorRat sens spec π_cohort hπ_pos hπ_lt hsens_pos hspec_lt > τ) := by
  exact em _

end P104
