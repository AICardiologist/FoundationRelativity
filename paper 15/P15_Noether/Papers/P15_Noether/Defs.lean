/-
Papers/P15_Noether/Defs.lean
Paper 15: Noether's Theorem and the Logical Cost of Global Conservation Laws.

Core definitions for lattice scalar field theory:
  - Field configuration and momenta on Fin N (finite lattice)
  - Index wrapping for periodic boundary conditions
  - Energy density components (kinetic, gradient, potential)
  - Total energy as Finset.sum
  - Non-negativity of energy density (the key structural theorem)
  - Discrete Laplacian for equations of motion
  - Partial energy on the infinite lattice (ℕ-indexed, open BC)
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Papers.P15

open Finset

noncomputable section

-- ========================================================================
-- Lattice field types
-- ========================================================================

/-- Field configuration on N sites with periodic boundary conditions. -/
abbrev FieldConfig (N : ℕ) := Fin N → ℝ

/-- Conjugate momenta at N sites. -/
abbrev Momenta (N : ℕ) := Fin N → ℝ

/-- A state of the lattice scalar field: field values + momenta. -/
structure LatticeState (N : ℕ) where
  φ : FieldConfig N
  π : Momenta N

-- ========================================================================
-- Index wrapping (periodic boundary conditions)
-- ========================================================================

/-- Next site index with periodic boundary conditions.
    For i ∈ Fin N, next wraps around: next (N-1) = 0. -/
def fnext (hN : 0 < N) (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ hN⟩

/-- Previous site index with periodic boundary conditions.
    For i ∈ Fin N, prev wraps around: prev 0 = N-1. -/
def fprev (hN : 0 < N) (i : Fin N) : Fin N :=
  ⟨(i.val + N - 1) % N, Nat.mod_lt _ hN⟩

-- ========================================================================
-- Energy density components (finite lattice, periodic BC)
-- ========================================================================

/-- Kinetic energy density at site i: T_kin(i) = ½ π_i². -/
def kineticDensity (s : LatticeState N) (i : Fin N) : ℝ :=
  (1 / 2) * (s.π i) ^ 2

/-- Gradient energy density at site i (periodic BC):
    T_grad(i) = ½ (φ_{i+1} - φ_i)². -/
def gradientDensity (hN : 0 < N) (s : LatticeState N) (i : Fin N) : ℝ :=
  (1 / 2) * (s.φ (fnext hN i) - s.φ i) ^ 2

/-- Potential energy density at site i: T_pot(i) = V(φ_i).
    The potential V : ℝ → ℝ is assumed non-negative (hypothesis hV in theorems). -/
def potentialDensity (V : ℝ → ℝ) (s : LatticeState N) (i : Fin N) : ℝ :=
  V (s.φ i)

/-- Total energy density at site i:
    ε_i = ½ π_i² + ½ (φ_{i+1} - φ_i)² + V(φ_i). -/
def energyDensity (V : ℝ → ℝ) (hN : 0 < N) (s : LatticeState N) (i : Fin N) : ℝ :=
  kineticDensity s i + gradientDensity hN s i + potentialDensity V s i

-- ========================================================================
-- Total energy (finite lattice)
-- ========================================================================

/-- Total energy of an N-site lattice field system:
    E = Σ_{i=0}^{N-1} [½ π_i² + ½ (φ_{i+1} - φ_i)² + V(φ_i)]. -/
def totalEnergy (V : ℝ → ℝ) (hN : 0 < N) (s : LatticeState N) : ℝ :=
  ∑ i : Fin N, energyDensity V hN s i

-- ========================================================================
-- Non-negativity (the key structural theorem)
-- ========================================================================

/-- Kinetic energy density is non-negative. -/
theorem kineticDensity_nonneg (s : LatticeState N) (i : Fin N) :
    0 ≤ kineticDensity s i := by
  unfold kineticDensity
  positivity

/-- Gradient energy density is non-negative. -/
theorem gradientDensity_nonneg (hN : 0 < N) (s : LatticeState N) (i : Fin N) :
    0 ≤ gradientDensity hN s i := by
  unfold gradientDensity
  positivity

/-- Energy density is non-negative when V ≥ 0. This is the theorem
    that makes the entire paper work: positivity of T⁰⁰ enables
    bounded monotone convergence → LPO. -/
theorem energyDensity_nonneg (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hN : 0 < N) (s : LatticeState N) (i : Fin N) :
    0 ≤ energyDensity V hN s i := by
  unfold energyDensity
  apply add_nonneg (add_nonneg (kineticDensity_nonneg s i) (gradientDensity_nonneg hN s i))
  exact hV _

/-- Total energy is non-negative when V ≥ 0. -/
theorem totalEnergy_nonneg (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (hN : 0 < N) (s : LatticeState N) :
    0 ≤ totalEnergy V hN s := by
  unfold totalEnergy
  exact Finset.sum_nonneg fun i _ => energyDensity_nonneg V hV hN s i

-- ========================================================================
-- Discrete Laplacian (for equations of motion)
-- ========================================================================

/-- Discrete Laplacian at site i (periodic BC):
    Δ_d φ_i = φ_{i+1} - 2 φ_i + φ_{i-1}. -/
def discreteLaplacian (hN : 0 < N) (φ : FieldConfig N) (i : Fin N) : ℝ :=
  φ (fnext hN i) - 2 * φ i + φ (fprev hN i)

-- ========================================================================
-- Partial energy on infinite lattice (ℕ-indexed, open BC)
-- ========================================================================

/-- Energy density at site i on the infinite lattice (open BC):
    e_i = ½ π_i² + ½ (φ_{i+1} - φ_i)² + V(φ_i). -/
def infiniteEnergyDensity (V : ℝ → ℝ) (φ : ℕ → ℝ) (π : ℕ → ℝ) (i : ℕ) : ℝ :=
  (1 / 2) * (π i) ^ 2 + (1 / 2) * (φ (i + 1) - φ i) ^ 2 + V (φ i)

/-- Partial energy of the first N sites of an infinite field configuration:
    E_N = Σ_{i=0}^{N-1} [½ π_i² + ½ (φ_{i+1} - φ_i)² + V(φ_i)].
    Uses open boundary conditions (no wrapping needed). -/
def partialEnergy (V : ℝ → ℝ) (φ : ℕ → ℝ) (π : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, infiniteEnergyDensity V φ π i

/-- Each term in the infinite-lattice energy sum is non-negative when V ≥ 0. -/
theorem infiniteEnergyDensity_nonneg (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (φ : ℕ → ℝ) (π : ℕ → ℝ) (i : ℕ) :
    0 ≤ infiniteEnergyDensity V φ π i := by
  unfold infiniteEnergyDensity
  have h1 : 0 ≤ (1 / 2) * (π i) ^ 2 := by positivity
  have h2 : 0 ≤ (1 / 2) * (φ (i + 1) - φ i) ^ 2 := by positivity
  linarith [hV (φ i)]

end

end Papers.P15
