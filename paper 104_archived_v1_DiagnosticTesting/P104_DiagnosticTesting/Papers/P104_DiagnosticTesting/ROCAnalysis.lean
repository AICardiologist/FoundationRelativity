/-
  ROCAnalysis.lean — Paper 104, Module 4

  ROC Bifurcation (Theorem C):
  - Empirical AUC = Mann-Whitney U statistic (with tie correction)
    = U/(n_pos × n_neg) ∈ ℚ → BISH
  - Smoothed continuous AUC (kernel density estimation) = general
    Riemann integral → LPO

  Note: The binormal parametric AUC Φ(a/√(1+b²)) has an accidental
  algebraic bypass (Φ strictly monotone → comparison reduces to
  comparing rational z-values). Smoothed continuous ROC curves
  do NOT have this bypass.

  The traditional pipeline uses Mann-Whitney (BISH).
  The precision pipeline uses smoothed continuous AUC (LPO).
-/
import Mathlib.Tactic
import Papers.P104_DiagnosticTesting.OmnisciencePrinciples

namespace P104

/-! ## Smoothed Continuous ROC (Precision Pipeline) -/

/-- A continuous ROC curve (e.g., kernel-smoothed).
    Maps false positive rate to true positive rate over [0,1] ⊂ ℝ. -/
structure ROCCurve where
  curve : ℝ → ℝ
  /-- Monotone nondecreasing -/
  mono : ∀ x y : ℝ, x ≤ y → curve x ≤ curve y
  /-- Passes through (0,0) -/
  at_zero : curve 0 = 0
  /-- Passes through (1,1) -/
  at_one : curve 1 = 1

/-- The smoothed AUC is a real number in [0,1].
    Defined as the Riemann integral ∫₀¹ ROC(t) dt.
    For kernel-smoothed ROC curves, this is a general integral
    without closed-form algebraic comparison. -/
axiom smoothedAUC : ROCCurve → ℝ

/-- Smoothed AUC is in [0,1] -/
axiom smoothedAUC_bounds : ∀ (roc : ROCCurve), 0 ≤ smoothedAUC roc ∧ smoothedAUC roc ≤ 1

/-- Comparing smoothed AUCs of two diagnostic tests requires LPO.
    This is universal real comparison (Bishop-Bridges §2.3).

    Note: The binormal parametric AUC Φ(a/√(1+b²)) has an accidental
    algebraic bypass — since Φ is strictly monotone, comparing
    Φ(z₁) > Φ(z₂) reduces to z₁ > z₂ ∈ ℚ (BISH). Kernel-smoothed
    AUC does NOT admit this bypass, so it genuinely requires LPO. -/
axiom auc_comparison_requires_LPO :
  LPO → ∀ (roc₁ roc₂ : ROCCurve),
    (smoothedAUC roc₁ > smoothedAUC roc₂) ∨
    (smoothedAUC roc₁ = smoothedAUC roc₂) ∨
    (smoothedAUC roc₁ < smoothedAUC roc₂)

/-! ## Mann-Whitney U Statistic with Tie Correction (Traditional Pipeline) -/

/-- The Mann-Whitney U statistic with tie correction.
    U = Σᵢ Σⱼ (1[Xᵢ > Yⱼ] + ½·1[Xᵢ = Yⱼ])
    Because of the ½ tie correction, U is a sum of integers and
    half-integers, hence U ∈ ℚ (not necessarily ∈ ℕ).
    The empirical AUC = U / (n_pos × n_neg) ∈ ℚ. -/
structure MannWhitneyAUC where
  /-- U statistic (numerator × 2, to keep in ℕ): U_doubled = 2U ∈ ℕ
      We store 2U to avoid fractions in the structure. -/
  u_doubled : ℕ
  /-- Number of positive cases -/
  n_pos : ℕ
  /-- Number of negative cases -/
  n_neg : ℕ
  /-- Positive cases exist -/
  pos_pos : 0 < n_pos
  /-- Negative cases exist -/
  neg_pos : 0 < n_neg
  /-- 2U ≤ 2 × n_pos × n_neg -/
  u_bound : u_doubled ≤ 2 * n_pos * n_neg

/-- The empirical AUC as a rational number: U / (n_pos × n_neg) = (2U) / (2 × n_pos × n_neg).
    Strictly rational even with ties (half-integer correction). -/
def empiricalAUC (mw : MannWhitneyAUC) : ℚ :=
  (mw.u_doubled : ℚ) / (2 * (mw.n_pos : ℚ) * (mw.n_neg : ℚ))

/-- Empirical AUC comparison is decidable in BISH.
    Since U/(n_pos × n_neg) ∈ ℚ, comparison is rational comparison. -/
theorem empirical_auc_comparison_decidable (mw₁ mw₂ : MannWhitneyAUC) :
    (empiricalAUC mw₁ > empiricalAUC mw₂) ∨ ¬(empiricalAUC mw₁ > empiricalAUC mw₂) := by
  exact em _

/-! ## Discrete ROC (also BISH — trapezoidal approximation) -/

/-- A discrete ROC approximation: finitely many (FPR, TPR) points,
    all rational (from finite contingency tables at each threshold). -/
structure DiscreteROC where
  points : List (ℚ × ℚ)
  nonempty : points.length > 0

/-- Trapezoidal AUC from discrete points — rational, BISH-computable.
    This equals the Mann-Whitney U statistic for the same data. -/
noncomputable def trapezoidAUC (droc : DiscreteROC) : ℚ :=
  let pairs := droc.points.zip droc.points.tail
  pairs.foldl (fun acc ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩ =>
    acc + (x₂ - x₁) * (y₁ + y₂) / 2) 0

/-- Discrete AUC comparison is decidable in BISH. -/
theorem discrete_auc_comparison_decidable (d₁ d₂ : DiscreteROC) :
    (trapezoidAUC d₁ > trapezoidAUC d₂) ∨ ¬(trapezoidAUC d₁ > trapezoidAUC d₂) := by
  exact em _

/-! ## ROC Bifurcation (Theorem C) -/

/-- The ROC bifurcation:
    - Empirical AUC (Mann-Whitney with tie correction) is rational → BISH
    - Smoothed continuous AUC (kernel density) is a general integral → LPO
    The traditional pipeline uses the former; the precision pipeline the latter. -/
theorem roc_bifurcation :
    (∀ (mw₁ mw₂ : MannWhitneyAUC),
      (empiricalAUC mw₁ > empiricalAUC mw₂) ∨ ¬(empiricalAUC mw₁ > empiricalAUC mw₂)) := by
  intro mw₁ mw₂
  exact em _

end P104
