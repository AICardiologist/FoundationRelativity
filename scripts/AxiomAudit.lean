/-
  Axiom Audit for Paper 5: General Relativity AxCal Analysis
  
  This script audits the axioms used by core Paper 5 theorems.
  Expected axioms are the portal axioms explicitly declared in the framework.
  Any other axioms would indicate unintended dependencies.
-/

import Papers.P5_GeneralRelativity.Main
import Papers.P5_GeneralRelativity.Smoke

-- Check core algebraic theorems (should have no axioms)
#print axioms Papers.P5_GeneralRelativity.maxH_comm
#print axioms Papers.P5_GeneralRelativity.maxAP_comm
#print axioms Papers.P5_GeneralRelativity.route_to_profile_append_eq_maxAP

-- Check the main theorem 
#print axioms Papers.P5_GeneralRelativity.Paper5_Main

-- Check profile computation
#print axioms Papers.P5_GeneralRelativity.Profile_Computation_Works

-- Check smoke test
#print axioms Paper5Smoke.Paper5_Smoke_Success
#print axioms Paper5Smoke.route_to_profile_sanity

-- Check EPS Height 0 theorem
#print axioms Papers.P5_GeneralRelativity.EPS.EPS_Height_Zero

-- Check Schwarzschild vacuum theorem
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.Schwarzschild_Vacuum_Check

-- Check the portal axioms themselves (these are expected)
#print axioms Papers.P5_GeneralRelativity.Zorn_portal
#print axioms Papers.P5_GeneralRelativity.LimitCurve_portal
#print axioms Papers.P5_GeneralRelativity.SerialChain_portal
#print axioms Papers.P5_GeneralRelativity.Reductio_portal

/-
  Expected output:
  - Algebraic theorems: no axioms
  - Main theorems: may use propext, funext (standard Lean axioms)
  - Portal axioms: these are our declared axioms and should appear
  - No unexpected axioms should appear
-/