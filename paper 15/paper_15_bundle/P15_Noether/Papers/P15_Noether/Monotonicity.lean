/-
Papers/P15_Noether/Monotonicity.lean
Paper 15: Noether's Theorem and the Logical Cost of Global Conservation Laws.

Monotonicity and boundedness of the partial energy sequence on the
infinite lattice. These are the properties that connect the physics
to the BMC ↔ LPO equivalence.

The partial energy E_N = Σ_{i<N} e_i is:
  - Monotone increasing (each summand is non-negative)
  - Non-negative (sum of non-negative terms)
  - E_{N+1} = E_N + e_N (Finset.sum_range_succ)

When bounded above by M, this is exactly the setup for BMC.
-/
import Papers.P15_Noether.Defs

namespace Papers.P15

open Finset

noncomputable section

-- ========================================================================
-- Partial energy recurrence
-- ========================================================================

/-- Partial energy satisfies the recurrence E_{N+1} = E_N + e_N. -/
theorem partialEnergy_succ (V : ℝ → ℝ) (φ : ℕ → ℝ) (π : ℕ → ℝ) (N : ℕ) :
    partialEnergy V φ π (N + 1) =
      partialEnergy V φ π N + infiniteEnergyDensity V φ π N := by
  unfold partialEnergy
  rw [Finset.sum_range_succ]

-- ========================================================================
-- Monotonicity
-- ========================================================================

/-- **Partial energy is monotone increasing** when V ≥ 0.

    This follows from each summand being non-negative: adding a new
    site can only increase (or maintain) the total energy.
    This is the theorem that connects the physics to BMC → LPO. -/
theorem partialEnergy_mono (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (φ : ℕ → ℝ) (π : ℕ → ℝ) :
    Monotone (partialEnergy V φ π) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [partialEnergy_succ]
  linarith [infiniteEnergyDensity_nonneg V hV φ π n]

/-- Partial energy is non-negative when V ≥ 0. -/
theorem partialEnergy_nonneg (V : ℝ → ℝ) (hV : ∀ x, 0 ≤ V x)
    (φ : ℕ → ℝ) (π : ℕ → ℝ) (N : ℕ) :
    0 ≤ partialEnergy V φ π N := by
  unfold partialEnergy
  exact Finset.sum_nonneg fun i _ => infiniteEnergyDensity_nonneg V hV φ π i

/-- Partial energy at 0 sites is zero. -/
theorem partialEnergy_zero (V : ℝ → ℝ) (φ : ℕ → ℝ) (π : ℕ → ℝ) :
    partialEnergy V φ π 0 = 0 := by
  unfold partialEnergy
  simp

end

end Papers.P15
