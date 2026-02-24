/-
Papers/P9_Combinatorial_Ising/Basic.lean
Core definitions for Paper 9: Formulation-Invariance Test for the 1D Ising Free Energy.

Defines the LPO omniscience principle, the combinatorial partition function
Z_N(β) = (2·cosh β)^N + (2·sinh β)^N, and the free energy densities.

Key difference from Paper 8: The partition function is derived from finite sums
over {±1}^N via bond variables and the parity sieve identity, NOT from transfer
matrix eigenvalues. The algebraic form is identical — the derivation differs.

NO imports from LinearAlgebra.Matrix.*, Analysis.NormedSpace.*, or any
functional-analytic Mathlib module. This is the formulation-invariance constraint.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

universe u

namespace Papers.P9

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
-- Combinatorial partition function ingredients
-- ========================================================================

/-- 2·cosh(β): the combinatorial sum over even-parity bond configurations.
    In the transfer matrix formulation, this equals λ₊. -/
noncomputable def twoCosh (β : ℝ) : ℝ := 2 * cosh β

/-- 2·sinh(β): the combinatorial sum over odd-parity bond configurations.
    In the transfer matrix formulation, this equals λ₋. -/
noncomputable def twoSinh (β : ℝ) : ℝ := 2 * sinh β

/-- Ratio r = tanh(β) = (2·sinh β)/(2·cosh β).
    For β > 0, satisfies 0 < r < 1. -/
noncomputable def tanhRatio (β : ℝ) : ℝ := tanh β

-- ========================================================================
-- Partition function and free energy
-- ========================================================================

/-- Partition function of the 1D Ising model with N spins and periodic
    boundary conditions: Z_N(β) = (2·cosh β)^N + (2·sinh β)^N.

    Derived combinatorially via bond variables and the parity sieve identity
    (see PartitionIdentity.lean). Defined directly via the algebraic formula
    to keep the BISH proof chain axiom-free. -/
noncomputable def partitionFn (β : ℝ) (N : ℕ) : ℝ :=
  (twoCosh β) ^ N + (twoSinh β) ^ N

/-- Finite-volume free energy density: f_N(β) = -(1/N)·log Z_N(β). -/
noncomputable def freeEnergyDensity (β : ℝ) (N : ℕ) (_hN : 0 < N) : ℝ :=
  -(1 / (N : ℝ)) * log (partitionFn β N)

/-- Infinite-volume free energy density: f_∞(β) = -log(2·cosh(β)).
    Defined by closed form — NOT as a limit. No omniscience principle needed. -/
noncomputable def freeEnergyInfVol (β : ℝ) : ℝ :=
  -log (twoCosh β)

end Papers.P9
