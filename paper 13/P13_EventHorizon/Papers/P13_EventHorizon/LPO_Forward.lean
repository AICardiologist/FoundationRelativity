/-
Papers/P13_EventHorizon/LPO_Forward.lean
Module 4: SchwarzschildInteriorGeodesicIncompleteness → LPO.

The forward direction: if geodesic incompleteness holds (every bounded
monotone decreasing sequence starting in the interior converges to a
definite limit), then LPO holds.

Proof (mirrors Paper 8, Theorem 4):
  1. Given α : ℕ → Bool, construct geodesicCoupling α M 0 — a non-increasing
     sequence taking values in {M, 0}.
  2. Apply geodesic incompleteness to get a limit L.
  3. Case split on runMax α N₁ (for the N₁ from the convergence modulus):
     - If true: ∃ k ≤ N₁ with α(k) = true → right disjunct of LPO
     - If false: coupling(N₁) = M, but |M - L| < δ/2.
       If ∃ n₀ with α(n₀) = true, then L = 0, so |M - 0| = M < δ/2.
       But δ = M, so M < M/2 — contradiction.
       Therefore ∀ n, α(n) = false → left disjunct of LPO.

The gap δ = M - 0 = M > 0 is the decision amplifier.
-/
import Papers.P13_EventHorizon.Incompleteness

namespace Papers.P13

open Real

-- ========================================================================
-- SchwarzschildInteriorGeodesicIncompleteness → LPO
-- ========================================================================

/-- **Geodesic Incompleteness implies LPO (Theorem — forward direction).**

    The proof encodes an arbitrary binary sequence α into a non-increasing
    non-negative sequence via geodesicCoupling, applies the incompleteness
    hypothesis to get a limit, and uses the gap between the "all false" limit
    (= M) and the "exists true" limit (= 0) to decide α.

    This mirrors Paper 8's BMC → LPO proof, with the Schwarzschild radial
    coordinate replacing the Ising free energy. -/
theorem geodesic_incompleteness_implies_lpo
    (hGI : SchwarzschildInteriorGeodesicIncompleteness) : LPO := by
  intro α
  -- Fix M = 1 (any M > 0 works)
  set M : ℝ := 1
  have hM : M > 0 := one_pos
  -- Build the encoded sequence: geodesicCoupling α M 0
  -- Values in {M, 0}: M when runMax = false, 0 when runMax = true
  set a := geodesicCoupling α M 0 with ha_def
  -- Verify hypotheses for geodesic incompleteness:
  -- (1) a is non-increasing (M ≥ 0 so antitone)
  have h_anti : Antitone a := geodesicCoupling_antitone α (le_of_lt hM)
  -- (2) a(n) ≥ 0 for all n
  have h_nn : ∀ n, 0 ≤ a n := geodesicCoupling_nonneg α (le_of_lt hM) (le_refl 0)
  -- (3) a(0) < 2M = 2
  have h_a0 : a 0 < 2 * M := by
    have := geodesicCoupling_le α (le_of_lt hM) 0
    linarith
  -- Apply geodesic incompleteness to get limit L
  obtain ⟨L, hL⟩ := hGI M hM a h_anti h_nn h_a0
  -- Compute the gap δ = M - 0 = M = 1 > 0
  have hδ : (0 : ℝ) < M := hM
  -- Get N₁ from the convergence modulus with ε = M/2
  obtain ⟨N₁, hN₁⟩ := hL (M / 2) (by linarith)
  have hN₁_self := hN₁ N₁ (le_refl _)
  -- Case split on runMax α N₁ (definitionally decidable: it is a Bool)
  cases hm : runMax α N₁
  · -- Case: runMax α N₁ = false
    -- Then a(N₁) = M (coupling is v₀ = M when runMax = false)
    left
    -- Prove ∀ n, α n = false by contradiction
    apply bool_not_exists_implies_all_false
    intro ⟨n₀, hn₀⟩
    -- If ∃ n₀ with α(n₀) = true, then L = 0
    have hL_val := limit_of_exists_true α M 0 hL hn₀
    -- a(N₁) = M since runMax = false
    have haN₁ : a N₁ = M := by
      simp only [ha_def, geodesicCoupling, hm, Bool.false_eq_true, ↓reduceIte]
    -- Now: |a(N₁) - L| = |M - 0| = M, but modulus gives < M/2
    rw [haN₁, hL_val] at hN₁_self
    simp at hN₁_self
    -- |M - 0| = M < M/2 is a contradiction
    rw [abs_of_pos hM] at hN₁_self
    linarith
  · -- Case: runMax α N₁ = true
    -- Extract witness: ∃ k ≤ N₁ with α k = true
    right
    obtain ⟨k, _, hk⟩ := runMax_witness α (show runMax α N₁ = true from hm)
    exact ⟨k, hk⟩

end Papers.P13
