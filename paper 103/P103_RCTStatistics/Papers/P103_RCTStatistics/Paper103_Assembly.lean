/-
  Paper103_Assembly.lean — Master theorem and programme summary

  The Constructive Cost of Statistical Inference:
  RCT Penumbra and the Asymptotic Premium

  Paper 103 of the Constructive Reverse Mathematics Series
  Author: Paul Chun-Kit Lee (NYU, interventional cardiologist)
-/
import Papers.P103_RCTStatistics.OmnisciencePrinciples
import Papers.P103_RCTStatistics.RealDecidability
import Papers.P103_RCTStatistics.TrialData
import Papers.P103_RCTStatistics.ExactTests
import Papers.P103_RCTStatistics.StudentizedBerryEsseen
import Papers.P103_RCTStatistics.AsymptoticPenumbra
import Papers.P103_RCTStatistics.CoxBypass
import Papers.P103_RCTStatistics.EffectSizeConjecture

namespace P103

/-! ## CRM Pipeline Classification -/

/-- CRM levels for the statistical pipeline. -/
inductive PipelineCRM where
  | bish     : PipelineCRM  -- pure Bishop constructive
  | bish_mp  : PipelineCRM  -- Bishop + Markov's Principle
  | wkl      : PipelineCRM  -- Weak König's Lemma
  | lpo      : PipelineCRM  -- Limited Principle of Omniscience
  deriving DecidableEq, Repr

/-- Pipeline stage classification. -/
inductive PipelineStage where
  | testStatistic        : PipelineStage  -- ℚ computation
  | studentizedBE        : PipelineStage  -- ℚ bound
  | normalCDF            : PipelineStage  -- Φ evaluation
  | pLessAlpha_universal : PipelineStage  -- p < α for all ℝ
  | pLessAlpha_witnessed : PipelineStage  -- p + err < α via ℝ
  | pLessAlpha_rational  : PipelineStage  -- p + err < α via ℚ
  | fisherExact          : PipelineStage  -- exact permutation
  | coxMLE_coercive      : PipelineStage  -- no separation
  | coxMLE_separation    : PipelineStage  -- complete separation
  | coxMLE_firth         : PipelineStage  -- Firth correction
  deriving DecidableEq, Repr

/-- The CRM classification function for the RCT pipeline. -/
def pipelineCRMLevel : PipelineStage → PipelineCRM
  | .testStatistic        => .bish
  | .studentizedBE        => .bish
  | .normalCDF            => .bish
  | .pLessAlpha_universal => .lpo
  | .pLessAlpha_witnessed => .bish_mp
  | .pLessAlpha_rational  => .bish
  | .fisherExact          => .bish
  | .coxMLE_coercive      => .bish
  | .coxMLE_separation    => .wkl
  | .coxMLE_firth         => .bish

/-- Count BISH stages. -/
def bishCount : Nat :=
  [PipelineStage.testStatistic, .studentizedBE, .normalCDF,
   .pLessAlpha_rational, .fisherExact, .coxMLE_coercive, .coxMLE_firth].length

/-- Count non-BISH stages. -/
def nonBishCount : Nat :=
  [PipelineStage.pLessAlpha_universal, .pLessAlpha_witnessed,
   .coxMLE_separation].length

theorem bish_count_eq : bishCount = 7 := by native_decide
theorem nonbish_count_eq : nonBishCount = 3 := by native_decide

/-- 7 BISH + 1 BISH+MP + 1 WKL + 1 LPO = 10 total stages -/
theorem total_stages : bishCount + nonBishCount = 10 := by native_decide

/-- BISH percentage: 70% -/
theorem bish_percentage : 100 * bishCount / (bishCount + nonBishCount) = 70 := by
  native_decide

/-! ## Master Theorem -/

/-- Paper 103 master theorem: assembles all main results. -/
theorem paper103_main :
    -- (1) Omniscience hierarchy
    (LPO → WLPO) ∧ (LPO → MarkovPrinciple) ∧ (LPO → LLPO)
    -- (2) Rational comparison: trichotomy (BISH)
    ∧ (∀ (p q : ℚ), p < q ∨ p = q ∨ p > q)
    -- (3) Penumbra characterisation
    ∧ (∀ (tr : TrialResult) (α : ℝ),
        inPenumbra tr α ↔
        (tr.p_asymp < α ∧ α ≤ tr.p_asymp + tr.studentBE_err))
    -- (4) Universal real trichotomy requires LPO
    ∧ ((∀ (p α : ℝ), p < α ∨ p = α ∨ p > α) → LPO)
    -- (5) Studentized constant ratio
    ∧ ((3.19 : ℝ) / 0.4748 > 6)
    -- (6) Cox classification
    ∧ classifyCoxMLE false false = .bish_coercive
    ∧ classifyCoxMLE true true = .bish_firth
    ∧ classifyCoxMLE true false = .wkl_separation
    -- (7) Pipeline statistics
    ∧ bishCount = 7
    ∧ nonBishCount = 3
    ∧ 100 * bishCount / (bishCount + nonBishCount) = 70
    := by
  exact ⟨LPO_implies_WLPO, LPO_implies_MP, LPO_implies_LLPO,
         rat_trichotomy,
         penumbra_characterization,
         classical_significance_requires_LPO,
         studentized_wider_than_oracle,
         cox_bish_without_separation, cox_bish_with_firth,
         cox_wkl_with_separation_no_firth,
         bish_count_eq, nonbish_count_eq, bish_percentage⟩

/-! ## Axiom Documentation

Documentary axioms (modelling external mathematical facts):
- `trichotomy_implies_LPO_encoding`: Bishop-Bridges §2.3 encoding
- `studentizedBEConstant/pos/bound`: Bentkus 2003
- `berryEsseenConstant_oracle/pos/bound`: Berry 1941, Esseen 1942
- `exactPermutationPValue`: combinatorial implementation (standard)
- `constructive_witnessing_requires_MP`: MP for rational approximation search
- `concave_coercive_has_unique_max`: coercivity + EVT + concavity
- `hasCompleteSeparation/decidable`: decidable over ℚ data
- `firth_restores_coercivity`: Firth 1993, Jeffreys prior penalty

Sorries (proofs not yet completed):
- `studentizedBE_computable_bound`: rational arithmetic bounding
- `subgroup_penalty`: existence of n_min from BE bound
- `penumbra_shrinks_with_n`: monotonicity in √n
- `penumbra_grows_with_skewness`: monotonicity in ρ̂
  (strictlyConcave_unique_max is now fully proved)
-/

end P103
