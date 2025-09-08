/-
  Paper 5: GR - Composition examples
-/
import Papers.P5_GeneralRelativity.GR.Portals
import Papers.P5_GeneralRelativity.AxCalCore.ProfileLUB
import Papers.P5_GeneralRelativity.GR.ComposeLaws

namespace Papers.P5_GeneralRelativity

def LocalPDE_flags : List PortalFlag := [PortalFlag.uses_limit_curve]
def MGHD_flags : List PortalFlag := [PortalFlag.uses_zorn]

def LocalPDE_Profile : AxisProfile := route_to_profile LocalPDE_flags
def MGHD_Profile : AxisProfile := route_to_profile MGHD_flags

def G2_Composed_Profile : AxisProfile :=
  maxAP LocalPDE_Profile MGHD_Profile

def G2_Composed_Cert_flags : List PortalFlag :=
  LocalPDE_flags ++ MGHD_flags

def G2_Composed_profile_law :
  route_to_profile G2_Composed_Cert_flags = G2_Composed_Profile := by
  unfold G2_Composed_Cert_flags G2_Composed_Profile LocalPDE_Profile MGHD_Profile
  exact route_to_profile_append_eq_maxAP LocalPDE_flags MGHD_flags

def G2_Composed_well_formed :
  (route_to_profile G2_Composed_Cert_flags).hChoice = Height.one := by
  simp [G2_Composed_Cert_flags, LocalPDE_flags, MGHD_flags, 
        route_to_profile, memFlag, eqb]

end Papers.P5_GeneralRelativity