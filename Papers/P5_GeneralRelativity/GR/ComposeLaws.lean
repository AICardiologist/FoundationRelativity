/-
  Paper 5: GR - Composition Laws (ASCII-only, def-based)
-/
import Papers.P5_GeneralRelativity.AxCalCore.ProfileLUB
import Papers.P5_GeneralRelativity.GR.Portals

namespace Papers.P5_GeneralRelativity

def route_to_profile_append_eq_maxAP (xs ys : List PortalFlag) :
  route_to_profile (xs ++ ys) = maxAP (route_to_profile xs) (route_to_profile ys) := by
  ext
  · simp [route_to_profile, maxAP, maxH, memFlag_append_simp]
    cases h1 : memFlag PortalFlag.uses_zorn xs <;> cases h2 : memFlag PortalFlag.uses_zorn ys <;> simp
  · simp [route_to_profile, maxAP, maxH, memFlag_append_simp]
    cases h1 : memFlag PortalFlag.uses_limit_curve xs <;> cases h2 : memFlag PortalFlag.uses_limit_curve ys <;> simp
  · simp [route_to_profile, maxAP, maxH, memFlag_append_simp]
    cases h1 : memFlag PortalFlag.uses_serial_chain xs <;> cases h2 : memFlag PortalFlag.uses_reductio xs <;>
    cases h3 : memFlag PortalFlag.uses_serial_chain ys <;> cases h4 : memFlag PortalFlag.uses_reductio ys <;> simp

def composition_associative (xs ys zs : List PortalFlag) :
  route_to_profile (xs ++ ys ++ zs) = 
  route_to_profile ((xs ++ ys) ++ zs) := by
  simp [List.append_assoc]

def composition_commutative (xs ys : List PortalFlag) :
  maxAP (route_to_profile xs) (route_to_profile ys) =
  maxAP (route_to_profile ys) (route_to_profile xs) := by
  rw [maxAP_comm]

def composition_idempotent (xs : List PortalFlag) :
  maxAP (route_to_profile xs) (route_to_profile xs) =
  route_to_profile xs := by
  rw [maxAP_idem]

end Papers.P5_GeneralRelativity