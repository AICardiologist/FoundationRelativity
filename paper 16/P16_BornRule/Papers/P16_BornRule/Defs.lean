/-
Papers/P16_BornRule/Defs.lean
Paper 16: The Born Rule as a Logical Artefact.

Core definitions for finite-dimensional quantum measurement:
  - Complex inner product (cdot) on Fin d → ℂ
  - Squared norm (cnorm_sq)
  - Spectral decomposition structure
  - Born probability distribution
  - Quantum expectation value
  - Relative frequency of measurement outcomes
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Papers.P16

open Finset Complex Matrix

noncomputable section

-- ========================================================================
-- Complex inner product on Fin d → ℂ
-- ========================================================================

/-- The standard inner product on ℂ^d:
    ⟨ψ, φ⟩ = Σ_i conj(ψ_i) · φ_i.
    Defined as a finite sum — no Hilbert space infrastructure needed. -/
def cdot {d : ℕ} (ψ φ : Fin d → ℂ) : ℂ :=
  ∑ i : Fin d, starRingEnd ℂ (ψ i) * φ i

/-- Squared norm: ‖ψ‖² = Re⟨ψ, ψ⟩. -/
def cnorm_sq {d : ℕ} (ψ : Fin d → ℂ) : ℝ :=
  (cdot ψ ψ).re

-- ========================================================================
-- Spectral decomposition
-- ========================================================================

/-- A spectral decomposition of a Hermitian operator on ℂ^d.
    Represents A = Σᵢ λᵢ Pᵢ where each Pᵢ is an orthogonal projection
    and the projections sum to the identity. -/
structure SpectralDecomp (d : ℕ) where
  eigenvalues : Fin d → ℝ
  projections : Fin d → Matrix (Fin d) (Fin d) ℂ
  is_projection : ∀ i, projections i * projections i = projections i
  is_hermitian : ∀ i, (projections i).conjTranspose = projections i
  is_orthogonal : ∀ i j, i ≠ j → projections i * projections j = 0
  is_complete : ∑ i, projections i = 1

-- ========================================================================
-- Born probability
-- ========================================================================

/-- Born probability for eigenvalue λᵢ:
    p_i = Re⟨ψ, P_i ψ⟩.
    For a projection P with P² = P and P† = P, this equals ‖P_i ψ‖². -/
def bornProb {d : ℕ} (ψ : Fin d → ℂ) (spec : SpectralDecomp d) (i : Fin d) : ℝ :=
  (cdot ψ ((spec.projections i).mulVec ψ)).re

-- ========================================================================
-- Quantum expectation value
-- ========================================================================

/-- Quantum expectation value ⟨ψ|A|ψ⟩ = ⟨ψ, Aψ⟩.
    A single inner product — one matrix-vector multiply + one dot product. -/
def expectationValue {d : ℕ} (ψ : Fin d → ℂ) (A : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  cdot ψ (A.mulVec ψ)

-- ========================================================================
-- Relative frequency
-- ========================================================================

/-- Relative frequency of outcome i in a sequence of N measurements.
    freq_N(i) = #{j : outcomes_j = i} / N.
    This is a computable rational number. -/
def relativeFreq {d N : ℕ} (outcomes : Fin N → Fin d) (i : Fin d) : ℝ :=
  (Finset.univ.filter (fun j => outcomes j = i)).card / (N : ℝ)

end

end Papers.P16
