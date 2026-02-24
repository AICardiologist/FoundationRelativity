/-
Papers/P15_Noether/LPO_BMC.lean
Paper 15: Noether's Theorem and the Logical Cost of Global Conservation Laws.

Re-stated logical principles for standalone compilation.
Paper 15 is a self-contained Lake package and cannot import Papers 8 or 14.

Definitions:
  - LPO (Limited Principle of Omniscience)
  - BMC (Bounded Monotone Convergence)
  - lpo_iff_bmc (LPO ↔ BMC, both directions axiomatized)

These are identical to the definitions in Papers 8 and 14.
The proofs are axiomatized here and cited from their verified sources.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Papers.P15

open Real

-- ========================================================================
-- Logical principles (re-stated from Papers 8/14)
-- ========================================================================

/-- Limited Principle of Omniscience.
    For every binary sequence, either all terms are false or some term is true.
    Equivalent to BMC [Bridges–Vîță 2006].
    Identical to Papers.P8.LPO and Papers.P14.LPO. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Bounded Monotone Convergence: every bounded non-decreasing sequence
    of reals has a limit. Equivalent to LPO over BISH [Bridges–Vîță 2006].
    Identical to Papers.P8.BMC and Papers.P14.BMC. -/
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

-- ========================================================================
-- Equivalence (axiomatized, citing verified sources)
-- ========================================================================

/-- LPO implies BMC. Axiomatized; follows from [Bridges–Vîță 2006, Theorem 2.1.5]. -/
axiom bmc_of_lpo : LPO → BMC

/-- BMC implies LPO. Axiomatized; fully verified in Paper 8 (P8_LPO_IsingBound,
    theorem `lpo_of_bmc` in PartB_Backward.lean). -/
axiom lpo_of_bmc : BMC → LPO

/-- **LPO ↔ BMC.** The fundamental equivalence [Bridges–Vîță 2006]. -/
theorem lpo_iff_bmc : LPO ↔ BMC :=
  ⟨bmc_of_lpo, lpo_of_bmc⟩

end Papers.P15
