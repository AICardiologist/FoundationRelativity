import Found.InterpCore
import Found.BaseGroupoids

open CategoryTheory Foundation FoundationRelativity

namespace RNPFail

/-- Covariant functor Foundation ⥤ Cat -/
def RNP_Fail₂ : Foundation ⥤ Cat where
  obj := Obj
  map f := match f with
  | Interp.id_bish => 𝟭 _
  | Interp.id_zfc  => 𝟭 _
  | Interp.forget  => fromEmpty
  map_id := by intro F; cases F <;> rfl
  map_comp := by
    intro _ _ _ f g
    cases f <;> cases g <;> rfl

end RNPFail