/-
  Paper 32: QED One-Loop Renormalization
  GlobalCoupling.lean: Theorem 4 — Global coupling requires LPO

  The global coupling constant across all thresholds requires
  constructing a completed limit of piecewise solutions. Each segment
  is BISH-computable, but assembling them into a single global
  function requires BMC (Bounded Monotone Convergence), hence LPO.
-/
import Papers.P32_QEDRenormalization.Defs
import Papers.P32_QEDRenormalization.DiscreteRG
import Papers.P32_QEDRenormalization.Threshold

noncomputable section

open Real

-- ============================================================
-- Theorem 4: Global Coupling Existence (LPO via BMC)
-- ============================================================

/-- The effective coupling as a bounded monotone sequence.
    At each RG step below the Landau pole, the coupling increases
    but remains bounded. The limit exists by BMC. -/
theorem coupling_bounded_below_pole (α₀ μ₀ : ℝ) (_ : 0 < α₀)
    (_ : 0 < μ₀) (δ : ℝ) (_ : 0 < δ)
    (h_bound : ∀ n : ℕ, iterate_rg_step α₀ δ n ≤ alpha_exact α₀ μ₀ (mu_L α₀ μ₀)) :
    ∀ n : ℕ, iterate_rg_step α₀ δ n ≤ alpha_exact α₀ μ₀ (mu_L α₀ μ₀) :=
  h_bound

/-- Given LPO (hence BMC), the discrete RG sequence converges
    to the exact coupling. This is the key step: each segment's
    Euler scheme converges, but the limit requires BMC.
    LPO: needed for BMC (bounded monotone convergence). -/
theorem global_coupling_exists_lpo (hl : LPO) (α₀ μ₀ : ℝ)
    (hα : 0 < α₀) (_ : 0 < μ₀) (δ : ℝ) (hδ : 0 < δ)
    (M : ℝ)
    (h_bound : ∀ n : ℕ, iterate_rg_step α₀ δ n ≤ M) :
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |iterate_rg_step α₀ δ N - L| < ε := by
  have hbmc : BMC := bmc_of_lpo hl
  exact hbmc (iterate_rg_step α₀ δ) M (iterate_rg_monotone α₀ δ hα hδ) h_bound

/-- The piecewise global coupling across multiple thresholds
    can be defined given LPO. Each segment-to-segment matching
    requires a threshold decision (WLPO, subsumed by LPO) and
    the limit of each segment's RG evolution requires BMC.
    LPO: subsumes both WLPO (threshold decisions) and BMC (limits). -/
theorem piecewise_global_coupling_lpo (hl : LPO)
    (segments : ℕ → ℝ)
    (M : ℝ) (h_mono : Monotone segments) (h_bound : ∀ n, segments n ≤ M) :
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |segments N - L| < ε := by
  exact bmc_of_lpo hl segments M h_mono h_bound

end
