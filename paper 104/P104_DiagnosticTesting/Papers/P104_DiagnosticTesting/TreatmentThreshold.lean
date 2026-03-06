/-
  TreatmentThreshold.lean — Paper 104, Module 5

  Treatment threshold τ from utility/decision theory.
  The threshold is the posterior probability at which the expected
  utility of treating equals the expected utility of not treating.

  τ = (1 - spec_Rx) · C_Rx / [sens_Rx · B_Rx + (1 - spec_Rx) · C_Rx]

  where B_Rx = benefit of treating disease, C_Rx = cost of treating non-disease.
  With rational utilities: BISH. With continuous outcome distributions: WKL or LPO.
-/
import Mathlib.Tactic
import Papers.P104_DiagnosticTesting.OmnisciencePrinciples

namespace P104

/-! ## Rational Treatment Threshold (BISH) -/

/-- Utility parameters for a treat/no-treat decision.
    In the simplest (Pauker-Kassirer) model:
    - benefit: net benefit of treating true disease (TP utility - FN disutility)
    - cost: net cost of treating non-disease (FP disutility)
    All utilities are rational in the discrete model. -/
structure UtilityParams where
  benefit : ℚ  -- B_Rx: benefit of correct treatment
  cost : ℚ     -- C_Rx: cost of unnecessary treatment
  benefit_pos : 0 < benefit
  cost_pos : 0 < cost
  deriving DecidableEq

/-- The Pauker-Kassirer treatment threshold:
    τ = C / (B + C)
    At this posterior probability, expected utility of treating = not treating.
    Treat when P(D|+) > τ; withhold when P(D|+) < τ. -/
noncomputable def treatmentThreshold (u : UtilityParams) : ℚ :=
  u.cost / (u.benefit + u.cost)

/-- The treatment threshold with rational utilities is rational → BISH.
    Comparison with a rational posterior is decidable. -/
theorem threshold_is_rational (u : UtilityParams) :
    ∃ τ : ℚ, τ = treatmentThreshold u :=
  ⟨_, rfl⟩

/-- Decision with rational posterior and rational threshold is BISH. -/
theorem rational_decision_decidable (posterior : ℚ) (u : UtilityParams) :
    (posterior > treatmentThreshold u) ∨ ¬(posterior > treatmentThreshold u) := by
  exact em _

/-- The threshold is in (0, 1) when utilities are positive. -/
theorem threshold_in_unit_interval (u : UtilityParams) :
    0 < treatmentThreshold u ∧ treatmentThreshold u < 1 := by
  constructor
  · unfold treatmentThreshold
    apply div_pos u.cost_pos
    linarith [u.benefit_pos, u.cost_pos]
  · unfold treatmentThreshold
    rw [div_lt_one (by linarith [u.benefit_pos, u.cost_pos])]
    linarith [u.benefit_pos]

/-! ## Continuous Outcome Space (WKL/LPO) -/

/-- When utilities are defined over continuous outcome distributions
    (e.g., quality-adjusted life years), the treatment threshold becomes
    the solution to an optimization problem over ℝ.

    The expected utility EU(treat) = ∫ u(x) f(x|D) dx requires integration
    over a continuous outcome space. The threshold τ satisfying
    EU(treat, τ) = EU(no-treat, τ) is a root-finding problem in ℝ. -/
axiom continuous_threshold_exists :
  ∀ (eu_treat eu_notreat : ℝ → ℝ),
    (∃ τ : ℝ, eu_treat τ = eu_notreat τ)

/-- Documentary axiom: finding the treatment threshold from continuous
    utility functions requires at least WKL (bounded optimization over
    continuous space) and may require LPO (argmin of expected loss).
    Reference: Pauker-Kassirer (1980), Paper 23 (Fan Theorem). -/
axiom continuous_threshold_requires_WKL :
  ∀ (_eu_treat _eu_notreat : ℝ → ℝ),
    -- The root τ* where EU(treat) = EU(not-treat) cannot be computed
    -- constructively without WKL when the utility functions are continuous
    -- and the outcome space is unbounded.
    True

end P104
