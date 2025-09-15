/-
Paper 5: General Relativity AxCal Analysis - Smoke Test
CI aggregator and verification guard for all GR AxCal components
-/

import Papers.P5_GeneralRelativity.AxCalCore.Axis
import Papers.P5_GeneralRelativity.AxCalCore.Tokens
import Papers.P5_GeneralRelativity.AxCalCore.ProfileLUB
import Papers.P5_GeneralRelativity.GR.Portals
import Papers.P5_GeneralRelativity.GR.ComposeLaws
import Papers.P5_GeneralRelativity.GR.Compose
import Papers.P5_GeneralRelativity.GR.Schwarzschild

namespace Paper5Smoke
open Papers.P5_GeneralRelativity
open AxisProfile

#check Height
#check AxisProfile
#check PortalFlag
#check route_to_profile

theorem route_to_profile_sanity :
  (route_to_profile [PortalFlag.uses_zorn]).hChoice = Height.one
  ∧ (route_to_profile [PortalFlag.uses_limit_curve]).hComp = Height.one
  ∧ (route_to_profile [PortalFlag.uses_serial_chain]).hLogic = Height.one
  ∧ (route_to_profile [PortalFlag.uses_reductio]).hLogic = Height.one := by
  simp [route_to_profile, memFlag, eqb]

#check maxH
#check maxAP
#check maxH_comm
#check maxH_assoc
#check maxH_idem
#check maxAP_comm
#check maxAP_assoc
#check maxAP_idem

#check route_to_profile_append_eq_maxAP
#check composition_associative
#check composition_commutative
#check composition_idempotent

#check LocalPDE_Profile
#check MGHD_Profile
#check G2_Composed_Profile
#check G2_Composed_profile_law
#check G2_Composed_well_formed

#reduce route_to_profile (LocalPDE_flags ++ MGHD_flags)

theorem Belt_and_Suspenders_Normalization_Check :
  route_to_profile (LocalPDE_flags ++ MGHD_flags) = 
  AxisProfile.mk Height.one Height.one Height.zero := by
  simp [LocalPDE_flags, MGHD_flags, route_to_profile, memFlag, eqb]

section SchwarzschildSmokeChecks
open Schwarzschild

#check SchwarzschildCoords
#check f
#check f_derivative
#check g_tt
#check g_rr
#check g_θθ
#check g_φφ
#check g_inv_tt
#check g_inv_rr
#check Γ_t_tr
#check Γ_r_tt
#check Γ_r_rr
#check Christoffel_t_tr_formula
#check Christoffel_r_tt_nonzero

-- Verify that f(r) has the correct form
theorem f_formula_check (M r : ℝ) :
  f M r = 1 - 2*M/r := by
  rfl  -- definitional equality

-- Verify metric components use f correctly
theorem metric_uses_f (M r : ℝ) :
  g_tt M r = -f M r ∧ g_rr M r = (f M r)⁻¹ := by
  constructor <;> rfl

-- Verify inverse metric relationship
theorem inverse_metric_check (M r : ℝ) :
  g_inv_rr M r = f M r ∧ g_inv_tt M r = -(f M r)⁻¹ := by
  constructor <;> rfl

-- Check a specific Christoffel symbol value
example (M r : ℝ) : Γ_t_tr M r = M / (r^2 * f M r) := by
  rfl

end SchwarzschildSmokeChecks

def Paper5_Smoke_Success : True := True.intro

end Paper5Smoke