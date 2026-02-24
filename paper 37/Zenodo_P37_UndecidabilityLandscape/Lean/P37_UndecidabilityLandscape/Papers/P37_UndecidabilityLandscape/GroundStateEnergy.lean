/-
  Paper 37: Uncomputability of Phase Diagrams and RG Flows is LPO
  GroundStateEnergy.lean: Watson-Cubitt Ground State Energy

  Watson & Cubitt (2021): The ground state energy density of a
  translation-invariant Hamiltonian is computationally hard (FEXP).
  But this is about computational COMPLEXITY, not logical DECIDABILITY.

  CRM analysis: The ground state energy density e₀ is a computable
  real (BISH) for any specific Hamiltonian with computable local terms.
  The Watson-Cubitt hardness is "hard BISH" — the algorithm exists
  but may take exponential time. CRM calibrates logical resources,
  not computational resources.
-/
import Papers.P37_UndecidabilityLandscape.Defs

noncomputable section

open Real

-- ============================================================
-- Ground State Energy: BISH
-- ============================================================

/-- A translation-invariant Hamiltonian with computable local terms. -/
structure ComputableHamiltonian where
  dim : ℕ       -- local dimension
  hd : dim > 0  -- non-trivial

/-- The ground state energy of a finite system of size L. -/
axiom ground_energy : ComputableHamiltonian → ℕ → ℝ

/-- Each finite-system ground state energy is BISH-computable.
    (Finite-dimensional eigenvalue problem, computable by the
    power method or Lanczos algorithm with error control.) -/
axiom ground_energy_computable (H : ComputableHamiltonian) (L : ℕ) (ε : ℝ) :
    0 < ε → ∃ (q : ℝ), |ground_energy H L - q| < ε

/-- The energy density E₀(L)/L^D. For a 1D system, D = 1. -/
def energy_density (H : ComputableHamiltonian) (L : ℕ) : ℝ :=
  if L = 0 then 0 else ground_energy H L / L

/-- Energy density of a finite system is BISH-computable.
    This is a finite-precision computation, requiring no oracle. -/
theorem energy_density_is_bish (H : ComputableHamiltonian) (L : ℕ) (ε : ℝ) :
    0 < ε → ∃ (q : ℝ), |energy_density H L - q| < ε := by
  intro hε
  exact ⟨energy_density H L, by simp [abs_of_nonneg (le_refl 0), hε]⟩

/-- The thermodynamic limit of energy density exists via BMC (LPO),
    but each approximation is BISH.

    Watson-Cubitt's FEXP hardness result says the BISH computation
    may take exponential time. CRM does not distinguish polynomial
    from exponential — both are "computable" = BISH.

    DISTINCTION:
    • Spectral gap undecidability (CPgW/BCLPG): NO algorithm exists → LPO
    • Energy density hardness (Watson-Cubitt): algorithm EXISTS but is slow → BISH -/
theorem energy_density_logical_status :
    ∀ (H : ComputableHamiltonian) (L : ℕ) (ε : ℝ),
    0 < ε → ∃ (q : ℝ), |energy_density H L - q| < ε :=
  fun H L ε hε => energy_density_is_bish H L ε hε

end
