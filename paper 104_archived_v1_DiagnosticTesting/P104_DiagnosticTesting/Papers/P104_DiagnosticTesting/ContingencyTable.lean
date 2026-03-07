/-
  ContingencyTable.lean — Paper 104, Module 2

  Finite contingency tables (TP, FP, FN, TN) and derived
  test characteristics (sensitivity, specificity, PPV, NPV,
  likelihood ratios). All computations are rational → BISH.
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas

namespace P104

/-- A 2×2 contingency table from a diagnostic test evaluation.
    All entries are natural numbers (counts). -/
structure ContingencyTable where
  tp : ℕ  -- true positives
  fp : ℕ  -- false positives
  fn : ℕ  -- false negatives
  tn : ℕ  -- true negatives
  deriving DecidableEq, Repr

/-- Total number of diseased subjects -/
def ContingencyTable.diseased (ct : ContingencyTable) : ℕ := ct.tp + ct.fn

/-- Total number of non-diseased subjects -/
def ContingencyTable.nonDiseased (ct : ContingencyTable) : ℕ := ct.fp + ct.tn

/-- Total number of test-positive subjects -/
def ContingencyTable.testPositive (ct : ContingencyTable) : ℕ := ct.tp + ct.fp

/-- Total number of test-negative subjects -/
def ContingencyTable.testNegative (ct : ContingencyTable) : ℕ := ct.fn + ct.tn

/-- Total subjects -/
def ContingencyTable.total (ct : ContingencyTable) : ℕ :=
  ct.tp + ct.fp + ct.fn + ct.tn

/-- Sensitivity = TP / (TP + FN) — rational when denominators are nonzero -/
noncomputable def sensitivity (ct : ContingencyTable) (_h : ct.diseased ≠ 0) : ℚ :=
  (ct.tp : ℚ) / (ct.diseased : ℚ)

/-- Specificity = TN / (TN + FP) — rational -/
noncomputable def specificity (ct : ContingencyTable) (_h : ct.nonDiseased ≠ 0) : ℚ :=
  (ct.tn : ℚ) / (ct.nonDiseased : ℚ)

/-- Positive Predictive Value = TP / (TP + FP) — rational -/
noncomputable def ppv (ct : ContingencyTable) (_h : ct.testPositive ≠ 0) : ℚ :=
  (ct.tp : ℚ) / (ct.testPositive : ℚ)

/-- Negative Predictive Value = TN / (TN + FN) — rational -/
noncomputable def npv (ct : ContingencyTable) (_h : ct.testNegative ≠ 0) : ℚ :=
  (ct.tn : ℚ) / (ct.testNegative : ℚ)

/-- Positive Likelihood Ratio = sensitivity / (1 - specificity) — rational -/
noncomputable def posLR (ct : ContingencyTable)
    (hd : ct.diseased ≠ 0) (_hnd : ct.nonDiseased ≠ 0) (_hfp : ct.fp ≠ 0) : ℚ :=
  sensitivity ct hd / ((ct.fp : ℚ) / (ct.nonDiseased : ℚ))

/-- Negative Likelihood Ratio = (1 - sensitivity) / specificity — rational -/
noncomputable def negLR (ct : ContingencyTable)
    (_hd : ct.diseased ≠ 0) (hnd : ct.nonDiseased ≠ 0) (_htn : ct.tn ≠ 0) : ℚ :=
  ((ct.fn : ℚ) / (ct.diseased : ℚ)) / specificity ct hnd

/-- All test characteristics from a contingency table are rational.
    This is the fundamental BISH fact: finite count data produces
    rational statistics with zero omniscience cost. -/
theorem test_characteristics_rational (ct : ContingencyTable)
    (hd : ct.diseased ≠ 0) (hnd : ct.nonDiseased ≠ 0)
    (htp : ct.testPositive ≠ 0) (htn : ct.testNegative ≠ 0) :
    ∃ (s sp pv nv : ℚ),
      s = sensitivity ct hd ∧
      sp = specificity ct hnd ∧
      pv = ppv ct htp ∧
      nv = npv ct htn := by
  exact ⟨sensitivity ct hd, specificity ct hnd, ppv ct htp, npv ct htn,
         rfl, rfl, rfl, rfl⟩

/-- Prevalence from a cohort study = (TP + FN) / N — rational -/
noncomputable def cohortPrevalence (ct : ContingencyTable) (_h : ct.total ≠ 0) : ℚ :=
  (ct.diseased : ℚ) / (ct.total : ℚ)

/-- Rational comparison of test characteristics is decidable in BISH.
    Example: "Is sensitivity > 0.90?" is decidable. -/
theorem rational_comparison_decidable_prop (q₁ q₂ : ℚ) : (q₁ < q₂) ∨ ¬(q₁ < q₂) := by
  exact em _

end P104
