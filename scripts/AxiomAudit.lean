import Papers.P5_GeneralRelativity.Main
import Papers.P5_GeneralRelativity.GR.Schwarzschild
import Papers.P5_GeneralRelativity.GR.ComposeLaws
import Papers.P5_GeneralRelativity.GR.Portals

/-!
  Axiom Audit (informational) for Paper 5.
  Prints transitive axiom dependencies for representative declarations.
  Expectation:
  * Algebraic composition lemmas: at most `propext`.
  * Deep-dive anchors: no axioms.
  * Portals: axioms by design.
-/

open Papers.P5_GeneralRelativity

#eval (IO.println "=== Paper 5 Axiom Audit (informational) ===")

-- Algebra on heights/profiles
#print axioms Papers.P5_GeneralRelativity.maxH_comm
#print axioms Papers.P5_GeneralRelativity.maxAP_comm
#print axioms Papers.P5_GeneralRelativity.route_to_profile_append_eq_maxAP

-- Portals (axioms by design)
#print axioms Papers.P5_GeneralRelativity.Zorn_portal
#print axioms Papers.P5_GeneralRelativity.LimitCurve_portal
#print axioms Papers.P5_GeneralRelativity.SerialChain_portal
#print axioms Papers.P5_GeneralRelativity.Reductio_portal

-- Deep-dive anchors (should be axiom-free)
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.f_pos_of_hr
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.f_pos_iff_r_gt_2M
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.f_nonpos_iff_r_le_2M
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.r_pos_of_exterior
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.r_ne_zero_of_exterior
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.f_eq_zero_iff_r_eq_2M
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.f_strictMonoOn_Ioi
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_inv_rr_pos_of_hr
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_inv_tt_neg_of_hr
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.f_hasDerivAt
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.f_derivative
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_tt_derivative
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_rr_derivative
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_rr_derivative_exterior
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_inv_rr_derivative
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_inv_tt_derivative
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_inv_tt_derivative_exterior
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_rr_pos_of_hr
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.g_tt_neg_of_hr
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.Christoffel_t_tr_formula
#print axioms Papers.P5_GeneralRelativity.Schwarzschild.Christoffel_r_tt_nonzero