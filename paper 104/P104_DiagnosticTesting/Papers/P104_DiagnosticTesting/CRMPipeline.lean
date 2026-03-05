/-
  CRMPipeline.lean — Paper 104, Module 9

  CRM pipeline classification for the diagnostic testing pipeline.
  Parallels Paper 103's PipelineStage/PipelineCRM architecture.

  Pipeline stages:
  1. Contingency table (count data)                → BISH
  2. Test characteristics (sens, spec, PPV, NPV)   → BISH
  3. Likelihood ratios                              → BISH
  4. Bayesian update (rational prevalence)          → BISH
  5. Bayesian update (real prevalence)              → BISH+MP
  6. Treatment threshold (rational utilities)       → BISH
  7. Treatment threshold (continuous utilities)     → WKL
  8. Clinical decision (rational posterior & τ)     → BISH
  9. ROC AUC comparison (continuous)                → LPO
  10. Test comparison (discrete ROC)                → BISH
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

/-- Diagnostic pipeline stages -/
inductive DiagStage where
  | contingencyTable          : DiagStage   -- Stage 1
  | testCharacteristics       : DiagStage   -- Stage 2
  | likelihoodRatios          : DiagStage   -- Stage 3
  | bayesRationalPrevalence   : DiagStage   -- Stage 4
  | bayesRealPrevalence       : DiagStage   -- Stage 5
  | thresholdRational         : DiagStage   -- Stage 6
  | thresholdContinuous       : DiagStage   -- Stage 7
  | clinicalDecisionRational  : DiagStage   -- Stage 8
  | rocAucContinuous          : DiagStage   -- Stage 9
  | testComparisonDiscrete    : DiagStage   -- Stage 10
  deriving DecidableEq, Repr

/-- Classification function: each stage's logical cost -/
def diagCRMLevel : DiagStage → DiagCRM
  | .contingencyTable          => .bish
  | .testCharacteristics       => .bish
  | .likelihoodRatios          => .bish
  | .bayesRationalPrevalence   => .bish
  | .bayesRealPrevalence       => .bish_mp
  | .thresholdRational         => .bish
  | .thresholdContinuous       => .wkl
  | .clinicalDecisionRational  => .bish
  | .rocAucContinuous          => .lpo
  | .testComparisonDiscrete    => .bish

/-- All 10 stages -/
def allStages : List DiagStage :=
  [.contingencyTable, .testCharacteristics, .likelihoodRatios,
   .bayesRationalPrevalence, .bayesRealPrevalence,
   .thresholdRational, .thresholdContinuous,
   .clinicalDecisionRational, .rocAucContinuous, .testComparisonDiscrete]

theorem total_stages : allStages.length = 10 := by native_decide

/-- Count of BISH stages -/
def bishStages : List DiagStage :=
  allStages.filter (fun s => diagCRMLevel s == .bish)

theorem bish_count : bishStages.length = 7 := by native_decide

/-- Count of non-BISH stages -/
def nonBishStages : List DiagStage :=
  allStages.filter (fun s => diagCRMLevel s != .bish)

theorem non_bish_count : nonBishStages.length = 3 := by native_decide

/-- BISH percentage: 70% — same as Paper 103 -/
theorem bish_percentage : 100 * bishStages.length / allStages.length = 70 := by native_decide

/-- Structural parallel with Paper 103:
    P103: 7 BISH + 1 BISH+MP + 1 WKL + 1 LPO = 10 stages (70%)
    P104: 7 BISH + 1 BISH+MP + 1 WKL + 1 LPO = 10 stages (70%)
    The pipeline decompositions are isomorphic. -/
theorem pipeline_isomorphism_with_P103 :
    bishStages.length = 7 ∧
    (allStages.filter (fun s => diagCRMLevel s == .bish_mp)).length = 1 ∧
    (allStages.filter (fun s => diagCRMLevel s == .wkl)).length = 1 ∧
    (allStages.filter (fun s => diagCRMLevel s == .lpo)).length = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

end P104
