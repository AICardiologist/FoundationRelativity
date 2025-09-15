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
import Papers.P5_GeneralRelativity.GR.EPSCore

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

section EPSSmokeChecks
open EPS

#check LightRay
#check FreeFall  
#check WeylConnection
#check EPS_CompatibilityData
#check EPS_Implementation
#check EPS_DerivationSteps
#check EPS_Algorithm
#check Kinematics
#check derive_metric

theorem EPS_constructive_witnesses_are_PUnit (S : Spacetime) :
  (∀ lr : LightRay S, lr.is_null = PUnit.unit ∧ lr.is_geodesic = PUnit.unit) ∧
  (∀ ff : FreeFall S, ff.is_timelike = PUnit.unit ∧ ff.is_geodesic = PUnit.unit) ∧
  (∀ W : WeylConnection S, W.preserves_conformal = PUnit.unit ∧ W.torsion_free = PUnit.unit) := by
  constructor
  · intro lr; exact ⟨rfl, rfl⟩
  constructor
  · intro ff; exact ⟨rfl, rfl⟩
  · intro W; cases W; exact ⟨rfl, rfl⟩

theorem EPS_compatibility_preserves_all (S : Spacetime) :
  ∀ (compat : EPS_CompatibilityData S) (lr : LightRay S) (ff : FreeFall S),
    compat.preserves_light lr = PUnit.unit ∧ compat.preserves_geodes ff = PUnit.unit := by
  intros; exact ⟨rfl, rfl⟩

theorem ScaleIntegrable_always_holds (S : Spacetime) :
  ∀ W : WeylConnection S, ScaleIntegrable W := by
  exact ScaleIntegrable_always

#check EPS_Height_Zero
#check EPS_Height_Zero_Structured
#check EPS_Lorentz_Recovery
#check EPS_Kinematics_Height0

end EPSSmokeChecks

def Paper5_Smoke_Success : True := True.intro

end Paper5Smoke