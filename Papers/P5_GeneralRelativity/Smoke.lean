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

def Paper5_Smoke_Success : True := True.intro

end Paper5Smoke