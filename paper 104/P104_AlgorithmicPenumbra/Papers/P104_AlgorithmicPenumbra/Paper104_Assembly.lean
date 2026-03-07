/-
  Paper104_Assembly.lean — Master theorem and programme summary

  The Algorithmic Penumbra: Constructive Reverse Mathematics
  of Clinical Machine Learning

  Paper 104 of the Constructive Reverse Mathematics Series
  Author: Paul Chun-Kit Lee (NYU, interventional cardiologist)
-/
import Papers.P104_AlgorithmicPenumbra.OmnisciencePrinciples
import Papers.P104_AlgorithmicPenumbra.MLArchitectures
import Papers.P104_AlgorithmicPenumbra.ReLUBypass
import Papers.P104_AlgorithmicPenumbra.SigmoidCost
import Papers.P104_AlgorithmicPenumbra.IntegerScores
import Papers.P104_AlgorithmicPenumbra.ClinicalTestCases
import Papers.P104_AlgorithmicPenumbra.ConstructiveRegularization
import Papers.P104_AlgorithmicPenumbra.GridOptimality

namespace P104

/-! ## CRM Pipeline Summary -/

/-- Pipeline component classification -/
inductive PipelineComponent where
  | integerScores     : PipelineComponent  -- qSOFA, NEWS, HEART
  | treeModels        : PipelineComponent  -- XGBoost, Random Forest
  | reluInference     : PipelineComponent  -- ReLU forward pass
  | sigmoidInference  : PipelineComponent  -- Sigmoid/Softmax forward pass
  | logisticInference : PipelineComponent  -- Logistic regression
  | plattScaledTrees  : PipelineComponent  -- σ(a·tree(x)+b) calibration
  | thresholdRational : PipelineComponent  -- ℚ threshold on ℚ output
  | thresholdSigmoid  : PipelineComponent  -- ℚ threshold on σ output
  deriving DecidableEq, Repr

/-- CRM classification for each component -/
def componentCRM : PipelineComponent → InferenceCRM
  | .integerScores     => .bish
  | .treeModels        => .bish
  | .reluInference     => .bish
  | .sigmoidInference  => .bish_mp
  | .logisticInference => .bish_mp
  | .plattScaledTrees  => .bish_mp
  | .thresholdRational => .bish
  | .thresholdSigmoid  => .bish_mp

/-- BISH components -/
def bishComponents : List PipelineComponent :=
  [.integerScores, .treeModels, .reluInference, .thresholdRational]

/-- BISH+MP components -/
def mpComponents : List PipelineComponent :=
  [.sigmoidInference, .logisticInference, .plattScaledTrees, .thresholdSigmoid]

theorem bish_count : bishComponents.length = 4 := by native_decide
theorem mp_count : mpComponents.length = 4 := by native_decide
theorem total_components : bishComponents.length + mpComponents.length = 8 := by native_decide

/-- BISH percentage: 50% -/
theorem bish_percentage :
    100 * bishComponents.length / (bishComponents.length + mpComponents.length) = 50 := by
  native_decide

/-! ## Master Theorem -/

/-- Paper 104 master theorem: assembles all main results. -/
theorem paper104_main :
    -- (1) Omniscience hierarchy
    (LPO → WLPO) ∧ (LPO → MarkovPrinciple)
    -- (2) Theorem A: Integer scores are BISH
    ∧ (∀ inp : QSofaInput, qsofaScore inp ≤ 3)
    ∧ (∀ inp : NEWSInput, newsScore inp ≤ 21)
    ∧ (∀ inp : HEARTInput, heartScore inp ≤ 10)
    -- (3) Theorem B: ReLU bypass
    ∧ classifyInference .reluNetwork = .bish
    -- (4) Theorem C: Sigmoid escalation
    ∧ classifyInference .sigmoidNetwork = .bish_mp
    ∧ (∀ q : ℚ, q ≠ 0 → Irrational (sigmoid (q : ℝ)))
    ∧ ((∀ (r : ℝ), Irrational r → ∀ (τ : ℚ), Decidable (r ≥ (τ : ℝ))) →
       MarkovPrinciple)
    -- (5) Clinical comparisons: ML always higher CRM cost
    ∧ (∀ c ∈ allComparisons, c.mlCRM = .bish_mp ∧ c.scoreCRM = .bish)
    -- (6) Proposition E: Constructive regularization (grid-factored, not merely BISH)
    ∧ (∀ {X : Type} [DecidableEq X] (quantize : X → ℤ) (H : Set (X → Bool))
         (_hG : ∀ c ∈ H, IsGridFactored quantize c)
         (S : Set X) (x y : X) (_hx : x ∈ S) (_hy : y ∈ S)
         (_hN : x ≠ y) (_hQ : quantize x = quantize y),
         ¬ Shatters H S)
    -- (7) Proposition F: Grid optimality (Bayes-optimal is grid-factored)
    ∧ (∀ {X : Type} (quantize : X → ℤ) (bayes : X → Bool),
         IsGridFactored quantize bayes)
    -- (8) Theorem F corollary: MP cannot improve accuracy
    ∧ (∀ {X : Type} (quantize : X → ℤ) (bayes c : X → Bool)
         (x y : X) (_hG : quantize x = quantize y) (_hS : c x ≠ c y),
         c x ≠ bayes x ∨ c y ≠ bayes y)
    -- (9) Pipeline statistics
    ∧ bishComponents.length = 4
    ∧ mpComponents.length = 4
    ∧ 100 * bishComponents.length / (bishComponents.length + mpComponents.length) = 50
    := by
  exact ⟨LPO_implies_WLPO, LPO_implies_MP,
         qsofa_range, news_range, heart_range,
         reluNetwork_bish,
         sigmoidNetwork_mp, sigmoid_rational_irrational,
         irrational_comparison_requires_MP,
         ml_always_higher_cost,
         fun q H hG S x y hx hy hN hQ => grid_factored_cannot_shatter_noise q H hG S x y hx hy hN hQ,
         fun q b => grid_optimality q b,
         fun q b c x y hG hS => mp_cannot_improve q b c x y hG hS,
         bish_count, mp_count, bish_percentage⟩

/-! ## Axiom Documentation

Documentary axioms (modelling external mathematical facts):
- `lindemann_weierstrass`: Baker (1975), Theorem 1.4
- `sigmoid_rational_irrational`: consequence of L-W via algebra of irrationals
- `irrational_comparison_requires_MP`: Bridges-Richman (1987) §3.4
- `sigmoid_preserves_irrationality`: conditional on Schanuel's conjecture
  for general case; unconditional for algebraic independence
- `bounded_biological_resolution`: physical premise (not mathematical)
- `bbr_sufficiency`: Under Axiom 2.5, quantization is a sufficient statistic
  for the clinical label.  Devroye-Györfi-Lugosi (1996), Chapter 2.

No sorry in this bundle.
-/

end P104
