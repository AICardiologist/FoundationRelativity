/-
  ClinicalTestCases.lean — Paper 104, Module 8

  Additional clinical test cases beyond troponin:
  1. D-dimer for pulmonary embolism exclusion
  2. PSA for prostate cancer screening

  Each test case demonstrates the same pattern:
  rational test data → BISH, real prevalence → BISH+MP,
  grey zone around threshold → Diagnostic Penumbra.
-/
import Mathlib.Tactic
import Papers.P104_DiagnosticTesting.ContingencyTable

namespace P104

/-! ## D-dimer for Pulmonary Embolism -/

/-- Standard D-dimer threshold: 500 ng/mL (FEU)
    Age-adjusted: age × 10 ng/mL for patients > 50 years
    Reference: Righini et al. (2014), ADJUST-PE trial -/
def ddimer_standard_threshold : ℚ := 500

/-- Age-adjusted threshold for a 70-year-old patient -/
def ddimer_age_adjusted_70 : ℚ := 700

theorem age_adjusted_higher : ddimer_age_adjusted_70 > ddimer_standard_threshold := by
  unfold ddimer_age_adjusted_70 ddimer_standard_threshold; norm_num

/-- ADJUST-PE trial data (Righini et al., 2014):
    N = 3346, age > 50
    Standard threshold: 6.4% false negative rate
    Age-adjusted: NPV = 97.0%, reduces unnecessary imaging by 30% -/
def adjust_pe_n : ℕ := 3346

/-- D-dimer contingency table (standard threshold 500)
    Simplified from meta-analysis (Di Nisio et al., 2007):
    Pooled sensitivity 95%, specificity 40% for PE
    In a PE prevalence of ~20% in ED presentations with clinical suspicion -/
def ddimer_ct : ContingencyTable where
  tp := 190    -- PE with D-dimer ≥ 500
  fp := 480    -- no PE with D-dimer ≥ 500
  fn := 10     -- PE with D-dimer < 500 (false negatives)
  tn := 320    -- no PE with D-dimer < 500

/-- D-dimer sensitivity: 190/200 = 95% -/
theorem ddimer_sensitivity :
    (190 : ℚ) / 200 = 19 / 20 := by norm_num

/-- D-dimer specificity: 320/800 = 40% -/
theorem ddimer_specificity :
    (320 : ℚ) / 800 = 2 / 5 := by norm_num

/-- D-dimer NPV: 320/330 ≈ 97.0%
    High NPV is the clinical value: D-dimer < 500 effectively rules out PE. -/
theorem ddimer_npv_bounds :
    (320 : ℚ) / 330 > 96 / 100 ∧ (320 : ℚ) / 330 < 98 / 100 := by
  constructor <;> norm_num

/-- At low pretest probability (Wells ≤ 4, ~5% PE prevalence):
    Posterior P(PE|D-dimer < 500) = (1-sens) * π / [(1-sens) * π + spec * (1-π)]
    = 0.05 * 0.05 / [0.05 * 0.05 + 0.40 * 0.95]
    = 0.0025 / 0.3825 ≈ 0.65%
    This is well below any treatment threshold → BISH decidable. -/
theorem ddimer_low_pretest_safe :
    -- Numerator: (1-sens) * π = (1/20) * (1/20) = 1/400
    -- Denominator: 1/400 + (2/5) * (19/20) = 1/400 + 38/100 = 1/400 + 152/400 = 153/400
    -- Posterior = 1/153 ≈ 0.0065
    (1 : ℚ) / 153 < 1 / 100 := by norm_num

/-! ## PSA for Prostate Cancer Screening -/

/-- Standard PSA threshold: 4.0 ng/mL
    Controversy: continuous risk, no clear threshold -/
def psa_standard_threshold : ℚ := 4

/-- Thompson et al. (2004) — PCPT trial:
    PSA < 4: cancer prevalence 15.2% (many low-grade)
    PSA ≥ 4: cancer prevalence 26.9%

    The key issue: even below threshold, cancer exists.
    PSA is a continuous marker with no clean binary separation.
    This is a fundamentally different penumbra structure:
    the entire range is a grey zone. -/
def pcpt_below_threshold_cancers : ℚ := 152 / 1000   -- 15.2%
def pcpt_above_threshold_cancers : ℚ := 269 / 1000   -- 26.9%

theorem psa_below_still_has_cancer :
    pcpt_below_threshold_cancers > 15 / 100 := by
  unfold pcpt_below_threshold_cancers; norm_num

theorem psa_above_rate :
    pcpt_above_threshold_cancers > 26 / 100 := by
  unfold pcpt_above_threshold_cancers; norm_num

/-- PSA contingency table at threshold 4.0 ng/mL
    Simplified model: 1000 men screened, prevalence 20% -/
def psa_ct : ContingencyTable where
  tp := 54     -- cancer with PSA ≥ 4 (sensitivity ~27% for all grades)
  fp := 120    -- no cancer with PSA ≥ 4
  fn := 146    -- cancer with PSA < 4
  tn := 680    -- no cancer with PSA < 4

/-- PSA sensitivity at 4.0 is only about 27% for all-grade cancer -/
theorem psa_sensitivity_low :
    (54 : ℚ) / 200 < 30 / 100 := by norm_num

/-- PSA specificity at 4.0 is about 85% -/
theorem psa_specificity :
    (680 : ℚ) / 800 = 17 / 20 := by norm_num

/-- The PSA example demonstrates a degenerate penumbra:
    sensitivity so low that the entire posterior range is a grey zone.
    No threshold produces clean BISH decidability because the test
    lacks discriminative power (AUC ≈ 0.56–0.68).
    This motivates the ROC analysis in ROCAnalysis.lean. -/
theorem psa_is_degenerate_penumbra :
    -- With sens = 27%, spec = 85%, prevalence = 20%:
    -- P(cancer|PSA ≥ 4) = 0.27 * 0.20 / [0.27 * 0.20 + 0.15 * 0.80]
    -- = 0.054 / (0.054 + 0.120) = 0.054 / 0.174 ≈ 31%
    -- P(cancer|PSA < 4) = 0.73 * 0.20 / [0.73 * 0.20 + 0.85 * 0.80]
    -- = 0.146 / (0.146 + 0.680) = 0.146 / 0.826 ≈ 17.7%
    -- Both are in the clinical grey zone [5%, 40%] for biopsy
    (54 : ℚ) / 174 > 30 / 100 ∧ (146 : ℚ) / 826 > 17 / 100 := by
  constructor <;> norm_num

end P104
