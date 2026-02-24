/-
Papers/P9_Combinatorial_Ising/Main.lean
Assembly of the LPO-dispensability theorem for the 1D Ising model
(combinatorial formulation).

Main result (Theorem 4.5):
  For every β > 0 and ε > 0, there exists a constructively computable N₀
  such that for all N ≥ N₀, |f_N(β) - f_∞(β)| < ε.

  f_N(β) = -(1/N)·log((2·cosh β)^N + (2·sinh β)^N)
  f_∞(β) = -log(2·cosh β)

  where Z_N = (2·cosh β)^N + (2·sinh β)^N is derived from finite sums over
  {±1}^N via bond variables and the parity sieve identity — NO transfer matrices.

Every step is BISH-valid. No omniscience principle (LPO, WLPO, LLPO) is used.

Axiom profile: propext, Classical.choice, Quot.sound only.
No custom axioms. No sorry.
-/
import Papers.P9_Combinatorial_Ising.Basic
import Papers.P9_Combinatorial_Ising.CoshSinhProps
import Papers.P9_Combinatorial_Ising.FreeEnergyDecomp
import Papers.P9_Combinatorial_Ising.ErrorBound
import Papers.P9_Combinatorial_Ising.ComputeN0

noncomputable section
namespace Papers.P9

open Real

-- ========================================================================
-- The Dispensability Theorem (Combinatorial Formulation)
-- ========================================================================

/-- **LPO-Dispensability for 1D Ising Empirical Content (Theorem 4.5).**
    **Combinatorial formulation — no transfer matrices.**

    For the 1D Ising model with periodic boundary conditions, the empirical
    content — finite-system free energy approximates the infinite-volume
    prediction within any ε > 0 — is provable in BISH without any
    omniscience principle.

    Specifically: for every β > 0 and ε > 0, there exists N₀ ∈ ℕ
    (constructively computable from β and ε) such that for all N ≥ N₀,

      |f_N(β) - f_∞(β)| < ε

    where:
    • f_N(β) = -(1/N)·log((2cosh β)^N + (2sinh β)^N) is the finite-volume
      free energy density, derived via bond variables and the parity sieve
    • f_∞(β) = -log(2·cosh β) is the infinite-volume free energy density

    The proof uses:
    1. Exact error: |f_N - f_∞| = (1/N)·log(1 + tanh(β)^N)
    2. Bound: log(1 + x) ≤ x for x ≥ 0
    3. Geometric decay: tanh(β)^N → 0 since 0 < tanh β < 1

    No use of monotone convergence theorem (LPO), Bolzano–Weierstrass (LPO),
    transfer matrices, eigenvalues, or any omniscience principle. -/
theorem ising_1d_dispensability_combinatorial
    (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → (hN : 0 < N) →
      |freeEnergyDensity β N hN - freeEnergyInfVol β| < ε := by
  obtain ⟨N₀, hN₀pos, hN₀bound⟩ := constructive_N0 β hβ ε hε
  exact ⟨N₀, hN₀pos, fun N hle hN =>
    lt_of_le_of_lt (freeEnergy_error_le_tanh_pow hβ hN) (hN₀bound N hle hN)⟩

-- ========================================================================
-- Axiom audit
-- ========================================================================

#print axioms ising_1d_dispensability_combinatorial

end Papers.P9
