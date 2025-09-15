/-
  Paper 5: GR - Composition Laws (ASCII-only, def-based)
-/
import Papers.P5_GeneralRelativity.AxCalCore.ProfileLUB
import Papers.P5_GeneralRelativity.GR.Portals

namespace Papers.P5_GeneralRelativity

/-- Profiles compose under append via componentwise `maxAP`. -/
theorem route_to_profile_append_eq_maxAP (xs ys : List PortalFlag) :
  route_to_profile (xs ++ ys) = maxAP (route_to_profile xs) (route_to_profile ys) := by
  -- Updated for Diener CRM alignment where serial_chain is on Choice axis
  ext
  · -- Choice axis: uses_zorn OR uses_serial_chain
    simp [route_to_profile, maxAP, maxH, memFlag_append]
    cases h1 : memFlag PortalFlag.uses_zorn xs <;> 
    cases h2 : memFlag PortalFlag.uses_serial_chain xs <;>
    cases h3 : memFlag PortalFlag.uses_zorn ys <;> 
    cases h4 : memFlag PortalFlag.uses_serial_chain ys <;> simp
  · -- Compactness axis: uses_limit_curve
    simp [route_to_profile, maxAP, maxH, memFlag_append]
    cases h1 : memFlag PortalFlag.uses_limit_curve xs <;> 
    cases h2 : memFlag PortalFlag.uses_limit_curve ys <;> simp
  · -- Logic axis: uses_reductio only
    simp [route_to_profile, maxAP, maxH, memFlag_append]
    cases h1 : memFlag PortalFlag.uses_reductio xs <;>
    cases h2 : memFlag PortalFlag.uses_reductio ys <;> simp

theorem composition_associative (xs ys zs : List PortalFlag) :
  route_to_profile (xs ++ ys ++ zs) = 
  route_to_profile ((xs ++ ys) ++ zs) := by
  simp [List.append_assoc]

theorem composition_commutative (xs ys : List PortalFlag) :
  maxAP (route_to_profile xs) (route_to_profile ys) =
  maxAP (route_to_profile ys) (route_to_profile xs) := by
  rw [maxAP_comm]

theorem composition_idempotent (xs : List PortalFlag) :
  maxAP (route_to_profile xs) (route_to_profile xs) =
  route_to_profile xs := by
  rw [maxAP_idem]

end Papers.P5_GeneralRelativity