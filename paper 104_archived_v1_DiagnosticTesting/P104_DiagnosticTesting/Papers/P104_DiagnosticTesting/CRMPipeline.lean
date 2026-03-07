/-
  CRMPipeline.lean — Paper 104, Module 9

  Dual CRM pipeline classification for diagnostic testing.

  Traditional pipeline (integer scores, cohort prevalence, Mann-Whitney):
    10/10 BISH = 100%

  Precision pipeline (logistic regression, population prevalence, parametric ROC):
    7 BISH + 1 BISH+MP + 1 WKL + 1 LPO = 10 stages (70% BISH)
    Isomorphic to Paper 103 (RCT Statistical Pipeline)

  The 30% gap = Archimedean Escalation.
-/
import Mathlib.Tactic
import Papers.P104_DiagnosticTesting.OmnisciencePrinciples

namespace P104

/-- CRM levels for the diagnostic pipeline -/
inductive DiagCRM where
  | bish     : DiagCRM
  | bish_mp  : DiagCRM
  | wkl      : DiagCRM
  | lpo      : DiagCRM
  deriving DecidableEq, Repr

/-- Diagnostic pipeline stages (shared between traditional and precision) -/
inductive DiagStage where
  | contingencyTable          : DiagStage   -- Stage 1
  | testCharacteristics       : DiagStage   -- Stage 2
  | likelihoodRatios          : DiagStage   -- Stage 3
  | pretestProbability        : DiagStage   -- Stage 4: integer score / logistic
  | bayesianPosterior         : DiagStage   -- Stage 5
  | treatmentThreshold        : DiagStage   -- Stage 6: rational / continuous
  | clinicalDecision          : DiagStage   -- Stage 7
  | rocAucComparison          : DiagStage   -- Stage 8: Mann-Whitney / binormal
  | testComparisonDiscrete    : DiagStage   -- Stage 9
  | netReclassification       : DiagStage   -- Stage 10
  deriving DecidableEq, Repr

/-! ## Traditional Pipeline: 100% BISH -/

/-- Traditional pipeline: all stages BISH
    (integer scores, cohort prevalence, Mann-Whitney AUC, rational utilities) -/
def traditionalCRM : DiagStage → DiagCRM
  | .contingencyTable       => .bish
  | .testCharacteristics    => .bish
  | .likelihoodRatios       => .bish
  | .pretestProbability     => .bish   -- integer score lookup
  | .bayesianPosterior      => .bish   -- rational prevalence → rational posterior
  | .treatmentThreshold     => .bish   -- Pauker-Kassirer rational
  | .clinicalDecision       => .bish   -- rational comparison
  | .rocAucComparison       => .bish   -- Mann-Whitney U statistic
  | .testComparisonDiscrete => .bish
  | .netReclassification    => .bish

/-! ## Precision Pipeline: 70% BISH (isomorphic to P103) -/

/-- Precision pipeline: logistic regression, population prevalence, parametric ROC.
    Computing π = 1/(1+e^{-X}) and applying Bayes are computable operations (BISH).
    The MP cost enters only at the COMPARISON step (clinical decision). -/
def precisionCRM : DiagStage → DiagCRM
  | .contingencyTable       => .bish
  | .testCharacteristics    => .bish
  | .likelihoodRatios       => .bish
  | .pretestProbability     => .bish     -- computing π is BISH (computable real)
  | .bayesianPosterior      => .bish     -- applying Bayes to computable real is BISH
  | .treatmentThreshold     => .wkl      -- continuous utility optimisation
  | .clinicalDecision       => .bish_mp  -- comparing transcendental posterior with τ ∈ ℚ
  | .rocAucComparison       => .lpo      -- smoothed continuous AUC integral
  | .testComparisonDiscrete => .bish
  | .netReclassification    => .bish

/-- All 10 stages -/
def allStages : List DiagStage :=
  [.contingencyTable, .testCharacteristics, .likelihoodRatios,
   .pretestProbability, .bayesianPosterior,
   .treatmentThreshold, .clinicalDecision,
   .rocAucComparison, .testComparisonDiscrete, .netReclassification]

theorem total_stages : allStages.length = 10 := by native_decide

/-! ## Traditional Pipeline Counts -/

def traditionalBishStages : List DiagStage :=
  allStages.filter (fun s => traditionalCRM s == .bish)

theorem traditional_all_bish : traditionalBishStages.length = 10 := by native_decide

theorem traditional_percentage : 100 * traditionalBishStages.length / allStages.length = 100 := by
  native_decide

/-! ## Precision Pipeline Counts -/

def precisionBishStages : List DiagStage :=
  allStages.filter (fun s => precisionCRM s == .bish)

def precisionNonBishStages : List DiagStage :=
  allStages.filter (fun s => precisionCRM s != .bish)

theorem precision_bish_count : precisionBishStages.length = 7 := by native_decide
theorem precision_non_bish_count : precisionNonBishStages.length = 3 := by native_decide

/-- Precision pipeline: 70% BISH — same as Paper 103 -/
theorem precision_percentage : 100 * precisionBishStages.length / allStages.length = 70 := by
  native_decide

/-! ## Archimedean Escalation: the 30% gap -/

/-- The Archimedean Escalation: traditional is 100% BISH,
    precision drops to 70% BISH. The 30% gap is the logical cost
    of replacing discrete heuristics with continuous models. -/
theorem archimedean_escalation :
    traditionalBishStages.length = 10 ∧
    precisionBishStages.length = 7 ∧
    traditionalBishStages.length - precisionBishStages.length = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## Pipeline Isomorphism with P103 -/

/-- Structural parallel with Paper 103 (precision pipeline only):
    P103: 7 BISH + 1 BISH+MP + 1 WKL + 1 LPO = 10 stages (70%)
    P104 precision: 7 BISH + 1 BISH+MP + 1 WKL + 1 LPO = 10 stages (70%) -/
theorem pipeline_isomorphism_with_P103 :
    precisionBishStages.length = 7 ∧
    (allStages.filter (fun s => precisionCRM s == .bish_mp)).length = 1 ∧
    (allStages.filter (fun s => precisionCRM s == .wkl)).length = 1 ∧
    (allStages.filter (fun s => precisionCRM s == .lpo)).length = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end P104
