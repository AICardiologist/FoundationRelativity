/-
Papers/P14_Decoherence/LPO_BMC.lean
Paper 14: The Measurement Problem as a Logical Artefact.

Re-stated logical principles for standalone compilation.
Paper 14 is a self-contained Lake package and cannot import Paper 8.

Definitions:
  - LPO (Limited Principle of Omniscience)
  - BMC (Bounded Monotone Convergence)
  - lpo_iff_bmc (LPO ↔ BMC, forward axiomatized from Bridges–Vîță 2006,
    backward axiomatized from Paper 8's verified proof)

These are identical to the definitions in Paper 8 (P8_LPO_IsingBound).
The proofs are axiomatized here and cited from their verified sources.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Papers.P14

open Real

-- ========================================================================
-- Logical principles (re-stated from Paper 8)
-- ========================================================================

/-- Limited Principle of Omniscience.
    For every binary sequence, either all terms are false or some term is true.
    Equivalent to BMC [Bridges–Vîță 2006].
    Identical to Papers.P8.LPO. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Bounded Monotone Convergence: every bounded non-decreasing sequence
    of reals has a limit. Equivalent to LPO over BISH [Bridges–Vîță 2006].
    Identical to Papers.P8.BMC. -/
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

-- ========================================================================
-- Equivalence (axiomatized, citing verified sources)
-- ========================================================================

/-- LPO implies BMC. Axiomatized; follows from [Bridges–Vîță 2006, Theorem 2.1.5].
    The classical proof uses binary search on the value axis with LPO decisions. -/
axiom bmc_of_lpo : LPO → BMC

/-- BMC implies LPO. Axiomatized; fully verified in Paper 8 (P8_LPO_IsingBound,
    theorem `lpo_of_bmc` in PartB_Backward.lean) via encoding binary sequences
    into 1D Ising free energy sequences. See Zenodo bundle for Paper 8. -/
axiom lpo_of_bmc : BMC → LPO

/-- **LPO ↔ BMC.** The fundamental equivalence between the Limited Principle
    of Omniscience and Bounded Monotone Convergence [Bridges–Vîță 2006].
    Both directions are axiomatized here; see Paper 8 for the verified proof. -/
theorem lpo_iff_bmc : LPO ↔ BMC :=
  ⟨bmc_of_lpo, lpo_of_bmc⟩

end Papers.P14
