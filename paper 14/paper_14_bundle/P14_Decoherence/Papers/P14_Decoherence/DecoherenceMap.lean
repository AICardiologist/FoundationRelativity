/-
Papers/P14_Decoherence/DecoherenceMap.lean
Paper 14: The Measurement Problem as a Logical Artefact.

Properties of the single-step decoherence map:
  - Entry-level lemmas (diagonal preservation, off-diagonal damping)
  - Trace preservation
  - Verification that the explicit formula equals the physical definition
    (partial trace of conjugated Kronecker product)

The entry-level lemmas are immediate from the explicit definition.
The verification lemma is the hardest computation (4×4 matrix arithmetic).
-/
import Papers.P14_Decoherence.PartialTrace
import Mathlib.LinearAlgebra.Matrix.Kronecker

namespace Papers.P14

open scoped Matrix Kronecker
open Matrix

noncomputable section

-- ========================================================================
-- Entry-level lemmas (immediate from explicit definition)
-- ========================================================================

@[simp]
theorem decoherenceMap_00 (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    decoherenceMap θ ρ 0 0 = ρ 0 0 := by
  simp [decoherenceMap]

@[simp]
theorem decoherenceMap_11 (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    decoherenceMap θ ρ 1 1 = ρ 1 1 := by
  simp [decoherenceMap]

@[simp]
theorem decoherenceMap_01 (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    decoherenceMap θ ρ 0 1 = ρ 0 1 * ↑(Real.cos (θ / 2)) := by
  simp [decoherenceMap]

@[simp]
theorem decoherenceMap_10 (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    decoherenceMap θ ρ 1 0 = ρ 1 0 * ↑(Real.cos (θ / 2)) := by
  simp [decoherenceMap]

-- ========================================================================
-- Trace preservation
-- ========================================================================

/-- The decoherence map preserves trace: Tr(Φ(ρ)) = Tr(ρ). -/
theorem decoherenceMap_trace (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (decoherenceMap θ ρ).trace = ρ.trace := by
  simp [Matrix.trace, Fin.sum_univ_two, decoherenceMap]

-- ========================================================================
-- Verification: explicit formula = physical definition
-- ========================================================================

/-- The physical decoherence map: embed ρ into ρ ⊗ |0⟩⟨0|, conjugate by
    the controlled-rotation unitary U(θ), and partial trace over the
    environment qubit. -/
def decoherenceMapPhysical (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  partialTraceB (controlledRotation θ * (ρ ⊗ₖ ketZeroBraZero) *
    (controlledRotation θ).conjTranspose)

/-- **Verification theorem:** The explicit decoherence map equals the
    physical definition (partial trace of conjugated Kronecker product).

    This is a brute-force 4×4 matrix computation. Each of the 4 output
    entries requires expanding a sum of products over Fin 2 × Fin 2 indices. -/
theorem decoherenceMap_eq_physical (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    decoherenceMap θ ρ = decoherenceMapPhysical θ ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp (config := { decide := true }) only [
    decoherenceMap, decoherenceMapPhysical,
    partialTraceB_apply_two, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    controlledRotation, ketZeroBraZero, Matrix.kroneckerMap_apply,
    Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.vecTail, Matrix.empty_val',
    star_zero, star_one, map_zero, map_one,
    Complex.ofReal_neg,
    Complex.star_def, Complex.conj_ofReal,
    starRingEnd_self_apply,
    Fin.isValue, Fin.reduceEq,
    Prod.mk.injEq, true_and, false_and, and_true, and_false, and_self,
    ite_true, ite_false,
    mul_zero, mul_one, zero_mul, one_mul, zero_add, add_zero]
  -- Most cases close by ring; the (1,1) case needs cos² + sin² = 1
  all_goals (try ring)
  -- Remaining: ρ 1 1 = cos²·ρ₁₁ + ρ₁₁·sin²
  have h : (↑(Real.cos (θ * (1 / 2))) : ℂ) ^ 2 + (↑(Real.sin (θ * (1 / 2))) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, ← Complex.ofReal_one]
    congr 1
    exact Real.cos_sq_add_sin_sq _
  calc ρ 1 1 = ρ 1 1 * 1 := by ring
    _ = ρ 1 1 * ((↑(Real.cos (θ * (1 / 2)))) ^ 2 + (↑(Real.sin (θ * (1 / 2)))) ^ 2) := by rw [h]
    _ = _ := by ring

end

end Papers.P14
