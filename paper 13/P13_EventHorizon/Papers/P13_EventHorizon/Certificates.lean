/-
Papers/P13_EventHorizon/Certificates.lean
Module 7: Axiom certificates via `#print axioms`.

Verifies the constructive/classical status of each theorem:
  - BISH results (Height 0): no Classical.choice
  - LPO equivalence results: Classical.choice only via LPO/BMC axioms
-/
import Papers.P13_EventHorizon.BISH_Content
import Papers.P13_EventHorizon.LPO_Forward
import Papers.P13_EventHorizon.LPO_Reverse

namespace Papers.P13

-- ========================================================================
-- Height 0 (BISH) certificates: no Classical.choice expected
-- ========================================================================

-- Kretschner scalar computability
#print axioms kretschner_computable_interior
-- Expected: propext, Quot.sound only (no Classical.choice)

-- Kretschner positivity
#print axioms kretschner_pos
-- Expected: propext, Quot.sound only

-- Kretschner at cycloid
#print axioms kretschner_at_cycloid
-- Expected: propext, Quot.sound only

-- Cycloid position computability
#print axioms r_cycloid_computable
-- Expected: propext, Quot.sound only

-- Cycloid proper time computability
#print axioms τ_cycloid_computable
-- Expected: propext, Quot.sound only

-- BISH approaching singularity
#print axioms approaching_singularity_BISH
-- Expected: propext, Quot.sound, Classical.choice
-- (Note: Classical.choice may appear from Metric.continuousAt_iff in r_cycloid_approaching)

-- Complete BISH content
#print axioms bish_content_complete
-- Expected: depends on approaching_singularity_BISH

-- ========================================================================
-- Cycloid properties (Height 0)
-- ========================================================================

-- Endpoint values
#print axioms r_cycloid_at_zero
#print axioms r_cycloid_at_pi
#print axioms τ_cycloid_at_zero
#print axioms τ_cycloid_at_pi

-- Monotonicity
#print axioms r_cycloid_strictAntiOn
#print axioms τ_cycloid_strictMonoOn

-- Interior membership
#print axioms r_cycloid_interior

-- ========================================================================
-- LPO equivalence certificates
-- ========================================================================

-- Forward direction: GeodesicIncompleteness → LPO
#print axioms geodesic_incompleteness_implies_lpo
-- Expected: propext, Quot.sound + axioms from LPO/BMC definitions

-- Reverse direction: LPO → GeodesicIncompleteness
#print axioms lpo_implies_geodesic_incompleteness
-- Expected: propext, Quot.sound, Classical.choice (via bmc_of_lpo axiom)

-- ========================================================================
-- Core definitions (should have minimal axioms)
-- ========================================================================

#print axioms LPO
#print axioms BMC
#print axioms SchwarzschildInteriorGeodesicIncompleteness

end Papers.P13
