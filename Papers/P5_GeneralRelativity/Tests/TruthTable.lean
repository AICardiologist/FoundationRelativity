/-
  Exhaustive check of route_to_profile on the 4-flag truth table.
-/
import Papers.P5_GeneralRelativity.GR.Portals
import Papers.P5_GeneralRelativity.AxCalCore.ProfileLUB

namespace Papers.P5_GeneralRelativity
open AxisProfile

def flagset (z lc sc rd : Bool) : List PortalFlag :=
  ([] : List PortalFlag)
    ++ (if z  then [PortalFlag.uses_zorn]         else [])
    ++ (if lc then [PortalFlag.uses_limit_curve]  else [])
    ++ (if sc then [PortalFlag.uses_serial_chain] else [])
    ++ (if rd then [PortalFlag.uses_reductio]     else [])

theorem route_truth_table :
  ∀ z lc sc rd,
    (route_to_profile (flagset z lc sc rd)).hChoice =
      (if z then Height.one else Height.zero) ∧
    (route_to_profile (flagset z lc sc rd)).hComp   =
      (if lc then Height.one else Height.zero) ∧
    (route_to_profile (flagset z lc sc rd)).hLogic  =
      (if (sc || rd) then Height.one else Height.zero) := by
  intro z lc sc rd
  cases z <;> cases lc <;> cases sc <;> cases rd <;>
    simp [flagset, route_to_profile, memFlag, eqb]

end Papers.P5_GeneralRelativity