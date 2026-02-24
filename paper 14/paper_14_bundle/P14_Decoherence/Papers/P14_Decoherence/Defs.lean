/-
Papers/P14_Decoherence/Defs.lean
Paper 14: The Measurement Problem as a Logical Artefact.

Core definitions: partial trace, decoherence map (explicit formula),
coherence sequence, controlled-rotation unitary.

The decoherence map is defined directly via the explicit formula
(diagonal preserved, off-diagonal multiplied by cos(θ/2)) rather than
through the Kronecker product → conjugation → partial trace chain.
A verification lemma in DecoherenceMap.lean connects it to the physical
definition. The explicit formula is derived from the controlled-rotation
unitary U(θ) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ R_y(θ) acting on ρ_S ⊗ |0⟩⟨0|_E.
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Papers.P14

open scoped Matrix Kronecker
open Matrix

noncomputable section

-- ========================================================================
-- Partial trace (re-stated from Paper 11)
-- ========================================================================

/-- Partial trace over the second subsystem (Bob/Environment) of a bipartite
    density matrix. For ρ on ℂ^n ⊗ ℂ^m, returns the reduced state on ℂ^n.
    This is the same definition as in Paper 11 (P11_Entanglement). -/
def partialTraceB {n m : ℕ} (ρ : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ k : Fin m, ρ (i, k) (j, k)

-- ========================================================================
-- Environment initial state
-- ========================================================================

/-- The environment ground state projector |0⟩⟨0| as a 2×2 matrix. -/
def ketZeroBraZero : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, 0]

-- ========================================================================
-- Controlled-rotation unitary
-- ========================================================================

/-- The controlled-rotation unitary on ℂ² ⊗ ℂ²:
    U(θ) = |0⟩⟨0| ⊗ I + |1⟩⟨1| ⊗ R_y(θ)
    where R_y(θ) = [[cos(θ/2), -sin(θ/2)], [sin(θ/2), cos(θ/2)]].

    If the system qubit is |0⟩, the environment is unchanged.
    If the system qubit is |1⟩, the environment rotates by θ.

    Indexing: (system, environment) with system, environment ∈ Fin 2. -/
def controlledRotation (θ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j =>
    if i = (0, 0) ∧ j = (0, 0) then 1
    else if i = (0, 1) ∧ j = (0, 1) then 1
    else if i = (1, 0) ∧ j = (1, 0) then ↑(Real.cos (θ / 2))
    else if i = (1, 0) ∧ j = (1, 1) then ↑(-Real.sin (θ / 2))
    else if i = (1, 1) ∧ j = (1, 0) then ↑(Real.sin (θ / 2))
    else if i = (1, 1) ∧ j = (1, 1) then ↑(Real.cos (θ / 2))
    else 0

-- ========================================================================
-- Decoherence map (explicit formula)
-- ========================================================================

/-- The single-step decoherence map on 2×2 density matrices.

    Given a system density matrix ρ and interaction angle θ, the map sends:
      ρ ↦ Tr_E[U(θ) · (ρ ⊗ |0⟩⟨0|) · U(θ)†]

    The result (verified in DecoherenceMap.lean) is:
      - Diagonal entries preserved: ρ'_{00} = ρ_{00}, ρ'_{11} = ρ_{11}
      - Off-diagonal entries damped: ρ'_{01} = ρ_{01} · cos(θ/2),
                                     ρ'_{10} = ρ_{10} · cos(θ/2) -/
def decoherenceMap (θ : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    match i, j with
    | 0, 0 => ρ 0 0
    | 0, 1 => ρ 0 1 * ↑(Real.cos (θ / 2))
    | 1, 0 => ρ 1 0 * ↑(Real.cos (θ / 2))
    | 1, 1 => ρ 1 1

-- ========================================================================
-- Coherence sequence
-- ========================================================================

/-- The coherence of the system after N decoherence steps:
    c(N) = |ρ_S^(N)_{01}| = |((decoherenceMap θ)^[N] ρ₀) 0 1|.

    This measures the magnitude of the off-diagonal element of the
    reduced density matrix — the quantum coherence between |0⟩ and |1⟩. -/
def coherence (ρ₀ : Matrix (Fin 2) (Fin 2) ℂ) (θ : ℝ) (N : ℕ) : ℝ :=
  ‖((decoherenceMap θ)^[N] ρ₀) 0 1‖

end

end Papers.P14
