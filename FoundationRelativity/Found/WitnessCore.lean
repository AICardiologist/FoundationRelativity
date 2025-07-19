import Found.InterpCore
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Category.Cat

/-!
# Witness API Core
A generic typeclass-based witness API for pathology functors.
This replaces hand-rolled Empty/PUnit patterns with a unified abstraction.
-/

namespace Found

open Foundation CategoryTheory

/-- Generic witness type function for pathologies -/
def WitnessType (α : Type) : Foundation → Type
  | bish => Empty
  | zfc => PUnit

/-- Build functor for a pathology type -/
def pathologyFunctor (α : Type) : Foundation ⥤ Cat where
  obj F := Cat.of (Discrete (ULift (WitnessType α F)))
  map f := match f with
    | Interp.id_bish => 𝟭 _
    | Interp.id_zfc => 𝟭 _
    | Interp.forget => Discrete.functor (fun x => x.down.elim)
  map_id := by intro F; cases F <;> rfl
  map_comp := by
    intro F G H f g
    cases f <;> cases g <;> rfl

end Found