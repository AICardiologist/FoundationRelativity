import Mathlib.CategoryTheory.Bicategory.Basic
import Gap2.WitnessFixed
import Found.InterpCore

open CategoryTheory
open Foundation
namespace Gap

/-- Action on objects. -/
def obj : Foundationᵒᵖ → Type*
  | ⟨F⟩ => Groupoid F

/-- Helper: functor induced by a 1‑cell (contravariant). -/
def mapCore :
    {F F' : Foundation} →
    Interp F' F →                    -- notice the order! (op)
    (Groupoid F) → (Groupoid F')
  | bish, bish, .id_bish => id
  | zfc , zfc , .id_zfc  => id
  | zfc , bish, .forget  => fun x => nomatch x.down
  | _, _, h => nomatch h          -- impossible cases

/-- Simplified contravariant functor structure. -/
structure Gap₂_Simple where
  obj_map : Foundation → Type*
  mor_map : {F F' : Foundation} → Interp F' F → (obj_map F → obj_map F')

def Gap₂ : Gap₂_Simple where
  obj_map := Groupoid
  mor_map := @mapCore

end Gap