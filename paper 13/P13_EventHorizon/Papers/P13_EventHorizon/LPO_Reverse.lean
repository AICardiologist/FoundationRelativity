/-
Papers/P13_EventHorizon/LPO_Reverse.lean
Module 5: LPO → SchwarzschildInteriorGeodesicIncompleteness.

The reverse direction: assuming LPO (equivalently, BMC), every bounded
non-increasing non-negative sequence starting in the interior has a
definite real limit.

Proof:
  1. LPO → BMC (axiomatized from Paper 8)
  2. Given a : ℕ → ℝ antitone with a(n) ≥ 0 and a(0) < 2M,
     negate to get (-a) : monotone, bounded above by 0.
  3. Apply BMC to (-a) to get limit L_neg.
  4. Then a converges to -L_neg.

This is straightforward: the Interior hypothesis just ensures the
sequence starts below 2M, and BMC applied to the negation gives the
convergence assertion.
-/
import Papers.P13_EventHorizon.Incompleteness

namespace Papers.P13

open Real

-- ========================================================================
-- LPO → SchwarzschildInteriorGeodesicIncompleteness
-- ========================================================================

/-- **LPO implies Schwarzschild Interior Geodesic Incompleteness.**

    With LPO, BMC holds. A non-increasing non-negative sequence is
    (after negation) a non-decreasing bounded-above sequence, so BMC
    gives a limit. -/
theorem lpo_implies_geodesic_incompleteness (hLPO : LPO) :
    SchwarzschildInteriorGeodesicIncompleteness := by
  intro M _hM a ha hnn _ha0
  -- Use BMC (from LPO) on the negated sequence
  have hBMC := bmc_of_lpo hLPO
  -- (-a) is non-decreasing
  have hMono : Monotone (fun n => -a n) := fun m n hmn => by
    simp only [neg_le_neg_iff]
    exact ha hmn
  -- (-a)(n) ≤ 0 for all n (since a(n) ≥ 0)
  have hBound : ∀ n, (fun n => -a n) n ≤ 0 := fun n => by
    simp only [neg_nonpos]
    exact hnn n
  -- Apply BMC
  obtain ⟨L_neg, hL⟩ := hBMC (fun n => -a n) 0 hMono hBound
  -- a converges to -L_neg
  refine ⟨-L_neg, fun ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hL ε hε
  exact ⟨N₀, fun N hN => by
    have := hN₀ N hN
    rwa [show a N - (-L_neg) = -((-a N) - L_neg) from by ring, abs_neg]⟩

end Papers.P13
