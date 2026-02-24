/-
Papers/P13_EventHorizon/Main.lean
Paper 13 Main Theorem: The Event Horizon as a Logical Boundary.

Main Result (Theorem 1):
  SchwarzschildInteriorGeodesicIncompleteness ↔ LPO

This establishes that the event horizon at r = 2M is simultaneously:
  - A causal boundary (classical GR): no signal can escape to infinity
  - A logical boundary (constructive reverse mathematics):
    the exterior geometry is BISH, but the singularity assertion
    (geodesic incompleteness) is exactly LPO

The BISH content — curvature computations and geodesic focusing over
finite parameter intervals — requires no omniscience (Height 0).
Only the completed assertion "r reaches exactly 0" costs LPO (Height 1).
-/
import Papers.P13_EventHorizon.LPO_Forward
import Papers.P13_EventHorizon.LPO_Reverse
import Papers.P13_EventHorizon.BISH_Content
import Papers.P13_EventHorizon.Certificates

namespace Papers.P13

open Real Set

-- ========================================================================
-- Main Theorem
-- ========================================================================

/-- **Paper 13 Main Theorem: The Event Horizon as a Logical Boundary.**

    Geodesic incompleteness in the Schwarzschild interior (the assertion
    that every bounded monotone decreasing sequence starting in the interior
    converges to a definite real limit) is equivalent to LPO.

    • Forward: Geodesic Incompleteness → LPO
      Encodes binary sequences into monotone sequences via geodesicCoupling.
      The gap between the "all false" limit (M) and "exists true" limit (0)
      serves as the decision amplifier.

    • Reverse: LPO → Geodesic Incompleteness
      LPO implies BMC. A non-increasing non-negative sequence is (after
      negation) a non-decreasing bounded sequence, so BMC gives a limit.

    This places the event horizon as a logical boundary in the constructive
    hierarchy: the exterior Schwarzschild geometry is BISH, the interior's
    singularity assertion is LPO. -/
theorem schwarzschild_interior_geodesic_incompleteness_iff_LPO :
    SchwarzschildInteriorGeodesicIncompleteness ↔ LPO :=
  ⟨geodesic_incompleteness_implies_lpo, lpo_implies_geodesic_incompleteness⟩

-- ========================================================================
-- Axiom certificate for the main theorem
-- ========================================================================

#print axioms schwarzschild_interior_geodesic_incompleteness_iff_LPO

-- ========================================================================
-- Summary of constructive content
-- ========================================================================

/-- The BISH content: approaching the singularity arbitrarily closely
    is constructive (Height 0). No omniscience needed. -/
theorem bish_approaching (M : ℝ) (hM : M > 0) (ε : ℝ) (hε : ε > 0) :
    ∃ η ∈ Set.Ioo 0 π, r_cycloid M η < ε :=
  approaching_singularity_BISH hM hε

/-- The LPO content: asserting the limit exists is exactly LPO.
    This is the completed-limit assertion that upgrades BISH to classical GR. -/
theorem lpo_content :
    SchwarzschildInteriorGeodesicIncompleteness ↔ LPO :=
  schwarzschild_interior_geodesic_incompleteness_iff_LPO

end Papers.P13
