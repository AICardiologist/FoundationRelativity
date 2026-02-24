/-
Papers/P11_Entanglement/PartialTrace.lean
Paper 11: Constructive Cost of Quantum Entanglement — CRM over Mathlib.

Partial trace properties for finite-dimensional bipartite systems.
All proofs are finite computations — BISH-valid.
-/
import Papers.P11_Entanglement.Defs

namespace Papers.P11

open scoped Matrix
open Matrix Finset

noncomputable section

-- ========================================================================
-- Partial trace lemmas for Fin 2 × Fin 2 systems
-- ========================================================================

/-- The partial trace over the second qubit unfolds as a sum of two terms. -/
theorem partialTraceB_apply_two
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (i j : Fin 2) :
    partialTraceB ρ i j = ρ (i, 0) (j, 0) + ρ (i, 1) (j, 1) := by
  simp [partialTraceB, Fin.sum_univ_two]

/-- Trace is preserved under partial trace: Tr(Tr_B(ρ)) = Tr(ρ). -/
theorem trace_partialTraceB
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (partialTraceB ρ).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, partialTraceB, Fintype.sum_prod_type, Fin.sum_univ_two]

end

end Papers.P11
