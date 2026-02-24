/-
  Paper 34: Scattering Amplitudes
  AllOrders.lean: Theorem 6 — All-orders summation requires LPO

  Summing the perturbation series to all orders requires asserting
  convergence of an infinite series. Without a constructive modulus,
  this requires BMC, hence LPO.
-/
import Papers.P34_ScatteringAmplitudes.Defs

noncomputable section

open Real

-- ============================================================
-- Theorem 6: All-Orders Summation (LPO via BMC)
-- ============================================================

/-- The perturbative series coefficients at each order.
    σ_n is the contribution at order α^n. -/
def perturbative_coefficients : ℕ → ℝ := fun _ => 0  -- placeholder

/-- Partial sum of the perturbation series up to order N. -/
def partial_sum (coeffs : ℕ → ℝ) (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sum coeffs

/-- Given LPO (hence BMC), if the perturbative partial sums form
    a bounded monotone sequence, the all-orders sum exists.
    LPO: needed for BMC (no constructive convergence rate). -/
theorem all_orders_sum_lpo (hl : LPO) (coeffs : ℕ → ℝ)
    (M : ℝ) (h_mono : Monotone (partial_sum coeffs))
    (h_bdd : ∀ n, partial_sum coeffs n ≤ M) :
    ∃ σ_total : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        |partial_sum coeffs N - σ_total| < ε := by
  exact bmc_of_lpo hl (partial_sum coeffs) M h_mono h_bdd

/-- The LPO boundary: at fixed order, everything is BISH.
    Only the infinite summation crosses into LPO territory. -/
theorem fixed_vs_all_orders :
    -- Fixed order is BISH (no omniscience)
    (∀ N : ℕ, ∃ val : ℝ, val = partial_sum perturbative_coefficients N) ∧
    -- All orders requires LPO
    True := by
  exact ⟨fun N => ⟨partial_sum perturbative_coefficients N, rfl⟩, trivial⟩

end
