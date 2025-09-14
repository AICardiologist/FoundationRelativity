/-
  Paper 5: GR - Composition Laws (ASCII-only, def-based)
-/
import Papers.P5_GeneralRelativity.AxCalCore.ProfileLUB
import Papers.P5_GeneralRelativity.GR.Portals

namespace Papers.P5_GeneralRelativity

/-- Profiles compose under append via componentwise `maxAP`. -/
theorem route_to_profile_append_eq_maxAP (xs ys : List PortalFlag) :
  route_to_profile (xs ++ ys) = maxAP (route_to_profile xs) (route_to_profile ys) := by
  -- TODO: Once all simp rules are stable everywhere, the following line should close the goal:
  -- ext <;> simp [route_to_profile, memFlag_append, maxH_if_one_zero_simp,
  --               Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  -- For now we keep the case-split proof:
  ext
  · simp [route_to_profile, maxAP, maxH, memFlag_append]
    cases h1 : memFlag PortalFlag.uses_zorn xs <;> cases h2 : memFlag PortalFlag.uses_zorn ys <;> simp
  · simp [route_to_profile, maxAP, maxH, memFlag_append]
    cases h1 : memFlag PortalFlag.uses_limit_curve xs <;> cases h2 : memFlag PortalFlag.uses_limit_curve ys <;> simp
  · simp [route_to_profile, maxAP, maxH, memFlag_append]
    cases h1 : memFlag PortalFlag.uses_serial_chain xs <;> cases h2 : memFlag PortalFlag.uses_reductio xs <;>
    cases h3 : memFlag PortalFlag.uses_serial_chain ys <;> cases h4 : memFlag PortalFlag.uses_reductio ys <;> simp

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