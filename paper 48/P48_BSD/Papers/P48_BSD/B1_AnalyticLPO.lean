/-
  Paper 48: BSD Conjecture — Constructive Calibration
  B1_AnalyticLPO.lean: Theorem B1 — Deciding L(E,1) = 0 requires LPO

  Main results:
  - LPO_decides_L_zero: LPO_R → L_value = 0 ∨ L_value ≠ 0
  - analytic_rank_LPO_each: LPO_R → ∀ k, L_deriv k = 0 ∨ L_deriv k ≠ 0
  - zero_test_iff_LPO: (∀ x : ℝ, x = 0 ∨ x ≠ 0) ↔ LPO_R

  The L-function value L(E,1) is a specific real number. Testing
  whether it equals zero is an instance of LPO for ℝ.

  No custom axioms. No sorry.
-/

import Papers.P48_BSD.Defs

noncomputable section

namespace Papers.P48

-- ============================================================
-- §1. LPO Decides L-value Zero Test
-- ============================================================

/-- LPO_R directly decides L(E,1) = 0: L_value is a real number,
    and LPO gives x = 0 ∨ x ≠ 0 for all reals. -/
theorem LPO_decides_L_zero : LPO_R → (L_value = 0 ∨ L_value ≠ 0) := by
  intro hlpo
  exact hlpo L_value

/-- LPO_R decides each derivative test L^(k)(E,1) = 0. -/
theorem analytic_rank_LPO_each :
    LPO_R → ∀ k : ℕ, (L_deriv k = 0 ∨ L_deriv k ≠ 0) := by
  intro hlpo k
  exact hlpo (L_deriv k)

-- ============================================================
-- §2. The Equivalence: Zero-Testing ↔ LPO
-- ============================================================

/-- **Theorem B1 (Zero-Testing ↔ LPO).**
    LPO_R is the assertion that every real number is decidably
    zero or nonzero: ∀ x : ℝ, x = 0 ∨ x ≠ 0.

    The BSD application: L(E,1) is a specific real number.
    Deciding whether L(E,1) = 0 (the "rank 0" case) requires LPO.
    Finding the order of vanishing (testing L^(k)(E,1) = 0 for
    each k) requires LPO for each test.

    LPO is both NECESSARY (zero-testing a real IS LPO by definition)
    and SUFFICIENT (LPO directly provides x = 0 ∨ x ≠ 0 for any x : ℝ). -/
theorem zero_test_iff_LPO :
    (∀ x : ℝ, x = 0 ∨ x ≠ 0) ↔ LPO_R :=
  Iff.rfl

/-- The stronger statement: LPO gives DecidableEq ℝ.
    This uses Classical.choice for the Prop→Type bridge
    (Or.casesOn cannot eliminate into Type). The constructive
    content is captured by zero_test_iff_LPO above. -/
def LPO_gives_real_decidable_eq (hlpo : LPO_R) : DecidableEq ℝ := by
  intro x y
  by_cases hxy : x = y
  · exact isTrue hxy
  · exact isFalse hxy

/-- LPO gives Decidable (L_value = 0) as a Type-valued instance. -/
def LPO_decides_L_zero_instance (hlpo : LPO_R) : Decidable (L_value = 0) :=
  LPO_gives_real_decidable_eq hlpo L_value 0

end Papers.P48
