/-
  TroponinCalculations.lean — Paper 104, Module 7

  Explicit numerical verification for the ESC 0/1h high-sensitivity
  troponin algorithm for acute chest pain.

  ESC thresholds: 5 ng/L (rule-out), 52 ng/L (rule-in)
  Grey zone: 5–52 ng/L = the Diagnostic Penumbra

  Clinical data from:
  - Reichlin et al. (2009): original derivation cohort
  - Mueller et al. (2019): validation, N = 7998

  The troponin assay is the lead clinical test case because:
  1. Paul is a cardiologist — this is his clinical world
  2. The ESC 0/1h algorithm has the most precisely quantified grey zone
  3. The prevalence of ACS in chest pain presentations is well-studied
-/
import Mathlib.Tactic
import Papers.P104_DiagnosticTesting.ContingencyTable
import Papers.P104_DiagnosticTesting.BayesianInference

namespace P104

/-! ## ESC 0/1h Algorithm Thresholds -/

/-- Rule-out threshold: 5 ng/L (hsTnI, Abbott Architect) -/
def troponin_ruleout : ℚ := 5

/-- Rule-in threshold: 52 ng/L -/
def troponin_rulein : ℚ := 52

/-- The grey zone is [5, 52] ng/L -/
theorem grey_zone_width : troponin_rulein - troponin_ruleout = 47 := by
  unfold troponin_rulein troponin_ruleout; norm_num

/-! ## Mueller et al. (2019) Validation Data — N = 7998 -/

/-- Rule-out group: hs-cTnI < 5 ng/L at 0h
    N = 4593, MACE at 30d: 14 (0.3%)
    Sensitivity for MACE: 99.0% (98.1–99.5%) -/
def mueller_ruleout_n : ℕ := 4593
def mueller_ruleout_events : ℕ := 14

/-- Rule-in group: hs-cTnI ≥ 52 ng/L at 0h
    N = 1433, MACE at 30d: 484 (33.8%)
    PPV: 33.8% -/
def mueller_rulein_n : ℕ := 1433
def mueller_rulein_events : ℕ := 484

/-- Observe (grey) zone: 5 ≤ hs-cTnI < 52 ng/L
    N = 1972 (24.7% of cohort) — substantial fraction requiring further testing -/
def mueller_observe_n : ℕ := 1972
def mueller_observe_events : ℕ := 141

/-- Total cohort -/
theorem mueller_total : mueller_ruleout_n + mueller_observe_n + mueller_rulein_n = 7998 := by
  unfold mueller_ruleout_n mueller_observe_n mueller_rulein_n; norm_num

/-- Observe zone is 24.7% of all chest pain presentations.
    This is the Diagnostic Penumbra: 1 in 4 patients are in the grey zone. -/
theorem observe_zone_fraction :
    (mueller_observe_n : ℚ) / ((mueller_ruleout_n + mueller_observe_n + mueller_rulein_n : ℕ) : ℚ)
    = 1972 / 7998 := by
  unfold mueller_observe_n mueller_ruleout_n mueller_rulein_n; norm_num

/-- The observe zone fraction is approximately 24.7% -/
theorem observe_zone_approx :
    (1972 : ℚ) / 7998 > 24 / 100 ∧ (1972 : ℚ) / 7998 < 25 / 100 := by
  constructor <;> norm_num

/-! ## Troponin Contingency Table (Rule-in vs Not Rule-in) -/

/-- Contingency table for troponin at 52 ng/L threshold
    (simplified: MACE = disease, ≥52 = positive)
    Total MACE events: 14 + 141 + 484 = 639
    Total non-MACE: 7998 - 639 = 7359 -/
def mueller_total_events : ℕ := mueller_ruleout_events + mueller_observe_events + mueller_rulein_events

theorem mueller_total_events_val : mueller_total_events = 639 := by
  unfold mueller_total_events mueller_ruleout_events mueller_observe_events mueller_rulein_events
  norm_num

def troponin_ct_52 : ContingencyTable where
  tp := 484    -- MACE with hs-cTnI ≥ 52
  fp := 949    -- no MACE with hs-cTnI ≥ 52  (1433 - 484)
  fn := 155    -- MACE with hs-cTnI < 52  (639 - 484)
  tn := 6410   -- no MACE with hs-cTnI < 52 (7998 - 1433 - 155)

/-- Verify the contingency table totals -/
theorem ct_52_total : troponin_ct_52.total = 7998 := by
  simp [ContingencyTable.total, troponin_ct_52]

/-- Sensitivity at 52 ng/L: 484/639 ≈ 75.7% -/
theorem ct_52_sensitivity_bounds :
    (484 : ℚ) / 639 > 75 / 100 ∧ (484 : ℚ) / 639 < 76 / 100 := by
  constructor <;> norm_num

/-- Specificity at 52 ng/L: 6410/7359 ≈ 87.1% -/
theorem ct_52_specificity_bounds :
    (6410 : ℚ) / 7359 > 87 / 100 ∧ (6410 : ℚ) / 7359 < 88 / 100 := by
  constructor <;> norm_num

/-! ## Bayesian Computation with Known Prevalence -/

/-- ACS prevalence in ED chest pain patients: approximately 8% (639/7998)
    From the Mueller cohort — a rational number! -/
def acs_prevalence_cohort : ℚ := 639 / 7998

theorem acs_prevalence_bounds :
    acs_prevalence_cohort > 7 / 100 ∧ acs_prevalence_cohort < 9 / 100 := by
  unfold acs_prevalence_cohort
  constructor <;> norm_num

/-- With cohort prevalence, sens = 484/639, spec = 6410/7359:
    Posterior P(D|+) = sens * π / (sens * π + (1-spec) * (1-π))

    Numerator: (484/639) * (639/7998) = 484/7998
    Denominator: 484/7998 + (949/7359) * (7359/7998) = 484/7998 + 949/7998 = 1433/7998

    P(D|+) = 484/1433 ≈ 0.338 — exactly the rule-in PPV.

    This is rational → BISH decidable. -/
theorem troponin_posterior_rational :
    (484 : ℚ) / 1433 > 33 / 100 ∧ (484 : ℚ) / 1433 < 34 / 100 := by
  constructor <;> norm_num

/-! ## The Grey Zone as Diagnostic Penumbra -/

/-- The grey zone (5–52 ng/L) produces intermediate posteriors.
    Observe zone event rate: 141/1972 ≈ 7.1%
    This is between rule-out (0.3%) and rule-in (33.8%). -/
theorem observe_event_rate_bounds :
    (141 : ℚ) / 1972 > 7 / 100 ∧ (141 : ℚ) / 1972 < 8 / 100 := by
  constructor <;> norm_num

/-- The key insight: in the grey zone, the posterior (7.1%) sits
    near typical treatment thresholds for invasive investigation
    (coronary angiography: τ ≈ 5–15% depending on utilities).
    This proximity IS the Diagnostic Penumbra. -/
theorem grey_zone_is_penumbra :
    -- The observe zone event rate (7.1%) is close to the angiography
    -- threshold range [5%, 15%], creating a penumbra
    (141 : ℚ) / 1972 > 5 / 100 ∧ (141 : ℚ) / 1972 < 15 / 100 := by
  constructor <;> norm_num

end P104
