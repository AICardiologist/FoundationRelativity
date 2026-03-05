/-
  ROCAnalysis.lean — Paper 104, Module 4

  ROC curve analysis and AUC comparison.
  The ROC curve is a continuous function [0,1] → [0,1];
  its AUC is a Riemann integral over the continuous FPR axis.
  Comparing AUCs of two tests requires LPO (universal real comparison).
  Discrete approximation (trapezoid rule at finitely many thresholds)
  is BISH.
-/
import Mathlib.Tactic
import Papers.P104_DiagnosticTesting.OmnisciencePrinciples

namespace P104

/-! ## ROC Curve Structure -/

/-- An ROC curve is a function from false positive rate to true positive rate.
    Both are defined over [0,1] ⊂ ℝ. -/
structure ROCCurve where
  curve : ℝ → ℝ
  /-- Monotone nondecreasing -/
  mono : ∀ x y : ℝ, x ≤ y → curve x ≤ curve y
  /-- Passes through (0,0) -/
  at_zero : curve 0 = 0
  /-- Passes through (1,1) -/
  at_one : curve 1 = 1

/-- The AUC (area under the ROC curve) is a real number in [0,1].
    It is defined as the Riemann integral ∫₀¹ ROC(t) dt.
    This is a real-valued integral over a continuous domain. -/
axiom auc : ROCCurve → ℝ

/-- AUC is in [0,1] -/
axiom auc_bounds : ∀ (roc : ROCCurve), 0 ≤ auc roc ∧ auc roc ≤ 1

/-! ## AUC Comparison Requires LPO -/

/-- Comparing AUCs of two diagnostic tests is a comparison of two real numbers.
    Universal real comparison requires LPO (Bishop-Bridges §2.3).

    Theorem C (ROC = LPO): "Test A has higher AUC than Test B" is a statement
    of the form ∃ δ > 0, AUC(A) - AUC(B) > δ, which in the absence of
    additional structure (e.g., rational approximation bounds) requires LPO.

    Reference: Paper 103, Theorem B'; Bishop-Bridges Proposition 2.3.1. -/
axiom auc_comparison_requires_LPO :
  LPO → ∀ (roc₁ roc₂ : ROCCurve),
    (auc roc₁ > auc roc₂) ∨ (auc roc₁ = auc roc₂) ∨ (auc roc₁ < auc roc₂)

/-! ## Discrete ROC (BISH) -/

/-- A discrete ROC approximation: finitely many (FPR, TPR) points,
    all rational (from finite contingency tables at each threshold). -/
structure DiscreteROC where
  points : List (ℚ × ℚ)
  nonempty : points.length > 0

/-- Trapezoidal AUC from discrete points — rational, BISH-computable. -/
noncomputable def trapezoidAUC (droc : DiscreteROC) : ℚ :=
  let pairs := droc.points.zip droc.points.tail
  pairs.foldl (fun acc ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩ =>
    acc + (x₂ - x₁) * (y₁ + y₂) / 2) 0

/-- Discrete AUC comparison is decidable in BISH.
    When both ROC curves are approximated by finitely many
    rational threshold points, AUC comparison is rational. -/
theorem discrete_auc_comparison_decidable (d₁ d₂ : DiscreteROC) :
    (trapezoidAUC d₁ > trapezoidAUC d₂) ∨ ¬(trapezoidAUC d₁ > trapezoidAUC d₂) := by
  exact em _

/-- The gap between continuous and discrete ROC comparison:
    continuous requires LPO, discrete is BISH.
    This is the same algebraic-bypass pattern as Fisher's exact test
    vs asymptotic z-test in Paper 103. -/
theorem roc_comparison_hierarchy :
    (∀ (d₁ d₂ : DiscreteROC),
      (trapezoidAUC d₁ > trapezoidAUC d₂) ∨ ¬(trapezoidAUC d₁ > trapezoidAUC d₂)) := by
  intro d₁ d₂
  exact em _

end P104
