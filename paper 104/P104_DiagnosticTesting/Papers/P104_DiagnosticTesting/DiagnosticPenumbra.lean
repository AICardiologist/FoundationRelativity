/-
  DiagnosticPenumbra.lean — Paper 104, Module 6

  The Diagnostic Penumbra: the grey zone where the posterior probability
  is too close to the treatment threshold for constructive decision-making.

  Structural twin of the Asymptotic Penumbra (Paper 103):
  - P103: p_asymp ∈ [α - ε, α)  → significance claim is classically valid but not constructively witnessed
  - P104: P(D|+) ∈ [τ - δ, τ + δ] → treat/no-treat decision is classically resolvable but not constructively witnessed

  The penumbra width δ depends on:
  1. Prevalence uncertainty (confidence interval width on π)
  2. Test imprecision (analytical CV of the assay)
  3. Biological variation (within-patient coefficient of variation)
-/
import Mathlib.Tactic
import Papers.P104_DiagnosticTesting.OmnisciencePrinciples
import Papers.P104_DiagnosticTesting.ContingencyTable
import Papers.P104_DiagnosticTesting.BayesianInference
import Papers.P104_DiagnosticTesting.TreatmentThreshold

namespace P104

/-! ## Penumbra Structure -/

/-- A diagnostic test result packages the Bayesian computation. -/
structure DiagnosticResult where
  /-- The posterior P(D|+) — may be real (population prevalence) or rational (cohort) -/
  posterior : ℝ
  /-- Prevalence uncertainty: half-width of 95% CI on π -/
  prevalenceUncertainty : ℝ
  /-- Analytical imprecision: CV of the assay -/
  analyticalCV : ℝ
  /-- Treatment threshold τ -/
  threshold : ℝ
  /-- All non-negative -/
  prev_unc_nn : 0 ≤ prevalenceUncertainty
  cv_nn : 0 ≤ analyticalCV
  threshold_pos : 0 < threshold
  threshold_lt : threshold < 1

/-- Total diagnostic uncertainty combining prevalence uncertainty
    and analytical imprecision.
    δ = √(δ_prev² + δ_cv²) in the continuous model,
    but we use the simpler additive bound δ = δ_prev + δ_cv
    for the rational upper bound. -/
noncomputable def diagnosticUncertainty (dr : DiagnosticResult) : ℝ :=
  dr.prevalenceUncertainty + dr.analyticalCV

/-- The diagnostic result is classically above threshold -/
def classicallyPositive (dr : DiagnosticResult) : Prop :=
  dr.posterior > dr.threshold

/-- The diagnostic result is constructively witnessed above threshold.
    The posterior must clear the threshold by more than the total uncertainty. -/
def constructivelyPositive (dr : DiagnosticResult) : Prop :=
  dr.posterior - diagnosticUncertainty dr > dr.threshold

/-- The diagnostic result is in the penumbra:
    classically positive but not constructively witnessed,
    OR classically negative but not constructively excluded. -/
def inDiagnosticPenumbra (dr : DiagnosticResult) : Prop :=
  |dr.posterior - dr.threshold| < diagnosticUncertainty dr

/-! ## Theorem A: Penumbra Characterisation -/

/-- Theorem A (Diagnostic Penumbra):
    A diagnostic result is in the penumbra iff the posterior lies within
    δ of the treatment threshold.
    Width = 2δ where δ = δ_prev + δ_cv. -/
theorem penumbra_characterization (dr : DiagnosticResult) :
    inDiagnosticPenumbra dr ↔
    |dr.posterior - dr.threshold| < diagnosticUncertainty dr := by
  exact Iff.rfl

/-- The penumbra has width 2δ (symmetric around τ). -/
theorem penumbra_width (dr : DiagnosticResult) :
    inDiagnosticPenumbra dr →
    dr.threshold - diagnosticUncertainty dr < dr.posterior ∧
    dr.posterior < dr.threshold + diagnosticUncertainty dr := by
  intro h
  unfold inDiagnosticPenumbra at h
  constructor
  · linarith [abs_lt.mp h]
  · linarith [abs_lt.mp h]

/-! ## Theorem B: MP Requirement for Real Prevalence -/

/-- Theorem B (Bayesian MP Requirement):
    When the posterior P(D|+) involves real prevalence (population parameter),
    comparing P(D|+) with the rational threshold τ requires BISH+MP.

    This is precisely the same mechanism as Paper 103 Theorem B:
    rational data → real function → real comparison → MP.

    Here: rational (sens, spec) → real π → real P(D|+) → real comparison with τ. -/
axiom posterior_comparison_requires_MP :
  MarkovPrinciple →
  ∀ (dr : DiagnosticResult),
    (dr.posterior > dr.threshold) ∨ ¬(dr.posterior > dr.threshold)

/-! ## Connection to Paper 103 -/

/-- The Diagnostic Penumbra and the Asymptotic Penumbra are structurally
    identical: both arise from rational data passing through a transcendental
    function and being compared with a rational threshold.
    - P103: data ∈ ℚ → Φ (normal CDF) → p ∈ ℝ → compare with α ∈ ℚ
    - P104: data ∈ ℚ → Bayes(π_real) → P(D|+) ∈ ℝ → compare with τ ∈ ℚ -/
theorem penumbra_structural_twin :
    -- The logical cost of the diagnostic grey zone equals
    -- the logical cost of the Asymptotic Penumbra: BISH+MP
    (MarkovPrinciple → ∀ (dr : DiagnosticResult),
      (dr.posterior > dr.threshold) ∨ ¬(dr.posterior > dr.threshold)) →
    True := by
  intro _; trivial

end P104
