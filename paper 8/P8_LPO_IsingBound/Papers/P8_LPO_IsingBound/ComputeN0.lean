/-
Papers/P8_LPO_IsingBound/ComputeN0.lean
Constructive computation of N0 such that |f_N - f_inf| < eps.

For any beta > 0 and eps > 0, we find N0 such that for all N >= N0,
the error (1/N) * r^N < eps.

The proof uses the fact that r^N -> 0 geometrically (since r = tanh beta < 1),
which eventually dominates the 1/N factor. We show r^N < eps for large N,
which gives (1/N) * r^N <= r^N < eps.

No omniscience principle needed: the bound N0 is constructive.
-/
import Papers.P8_LPO_IsingBound.ErrorBound

namespace Papers.P8

open Real

-- ========================================================================
-- Main N0 computation
-- ========================================================================

/-- For 0 < r < 1 and eps > 0, (1/N) * r^N < eps for all large enough N.
    In fact, r^N < eps suffices since (1/N) <= 1 for N >= 1. -/
lemma exists_bound_lt {r : ℝ} {ε : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → (hN : 0 < N) →
      (1 / (N : ℝ)) * r ^ N < ε := by
  obtain ⟨M, hM⟩ := _root_.exists_pow_lt_of_lt_one hε hr₁
  refine ⟨max M 1, by omega, fun N hle hN => ?_⟩
  have hN_cast : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have h_inv_le : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hN_cast]
    exact Nat.one_le_cast.mpr hN
  have h_rN_nonneg : 0 ≤ r ^ N := pow_nonneg hr₀.le N
  calc (1 / (N : ℝ)) * r ^ N
      ≤ 1 * r ^ N := mul_le_mul_of_nonneg_right h_inv_le h_rN_nonneg
    _ = r ^ N := one_mul _
    _ ≤ r ^ M := by
        apply pow_le_pow_of_le_one hr₀.le hr₁.le
        omega
    _ < ε := hM

/-- **Constructive N0 (Corollary 4.2).**
    For beta > 0 and eps > 0, there exists N0 such that for all N >= N0,
    (1/N) * tanh(beta)^N < eps. Combined with the error bound, this gives
    |f_N - f_inf| < eps. -/
theorem constructive_N0 (β : ℝ) (hβ : 0 < β) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → (hN : 0 < N) →
      (1 / (N : ℝ)) * (eigenRatio β) ^ N < ε :=
  exists_bound_lt (eigenRatio_pos hβ) (eigenRatio_lt_one β) hε

end Papers.P8
