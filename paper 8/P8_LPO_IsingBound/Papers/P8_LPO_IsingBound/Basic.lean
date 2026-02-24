/-
Papers/P8_LPO_IsingBound/Basic.lean
Core definitions for Paper 8: Constructive Finite-Size Bounds for the 1D Ising Free Energy.

Defines the LPO omniscience principle, transfer matrix eigenvalues, partition function,
finite-volume and infinite-volume free energy densities.

Key insight: The partition function is defined directly via eigenvalues (λ₊^N + λ₋^N),
not via configuration sums. The BISH-dispensability proof operates entirely on this
algebraic representation.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

universe u

namespace Papers.P8

open Real

-- ========================================================================
-- Logical principles
-- ========================================================================

/-- Limited Principle of Omniscience.
    Equivalent to: every bounded monotone sequence of reals converges
    (Bridges–Vîță 2006). The 1D Ising proof bypasses this entirely. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

-- ========================================================================
-- Transfer matrix eigenvalues
-- ========================================================================

/-- Larger eigenvalue of the 1D Ising transfer matrix: λ₊ = 2·cosh(β). -/
noncomputable def transferEigenPlus (β : ℝ) : ℝ := 2 * cosh β

/-- Smaller eigenvalue of the 1D Ising transfer matrix: λ₋ = 2·sinh(β). -/
noncomputable def transferEigenMinus (β : ℝ) : ℝ := 2 * sinh β

/-- Eigenvalue ratio r = λ₋/λ₊ = tanh(β). For β > 0, satisfies 0 < r < 1. -/
noncomputable def eigenRatio (β : ℝ) : ℝ := tanh β

-- ========================================================================
-- Partition function and free energy
-- ========================================================================

/-- Partition function of the 1D Ising model with N spins and periodic
    boundary conditions: Z_N(β) = λ₊^N + λ₋^N.

    This equals Tr(T^N) where T is the 2×2 transfer matrix (proven in
    PartitionTrace.lean as a bonus lemma). Defined directly via eigenvalues
    to keep the BISH proof chain axiom-free. -/
noncomputable def partitionFn (β : ℝ) (N : ℕ) : ℝ :=
  (transferEigenPlus β) ^ N + (transferEigenMinus β) ^ N

/-- Finite-volume free energy density: f_N(β) = -(1/N)·log Z_N(β). -/
noncomputable def freeEnergyDensity (β : ℝ) (N : ℕ) (_hN : 0 < N) : ℝ :=
  -(1 / (N : ℝ)) * log (partitionFn β N)

/-- Infinite-volume free energy density: f_∞(β) = -log(2·cosh(β)).
    Defined by closed form — NOT as a limit. No omniscience principle needed. -/
noncomputable def freeEnergyInfVol (β : ℝ) : ℝ :=
  -log (transferEigenPlus β)

end Papers.P8
