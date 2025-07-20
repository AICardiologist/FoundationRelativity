/-
Shared base groupoid definitions for all pathology functors.
Factors out the common Obj and fromEmpty definitions.
-/

import Found.InterpCore
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory Foundation

namespace FoundationRelativity

/-- Witness types for pathology functors -/
def Witness : Foundation → Type
  | bish => Empty
  | zfc  => PUnit

instance : Inhabited (Witness zfc) := ⟨PUnit.unit⟩

/-- Groupoid construction from witness types -/
def Groupoid (F : Foundation) : Cat :=
  Cat.of (Discrete (ULift (Witness F)))

/-- Object part shared by all pathology functors -/
def Obj : Foundation → Cat
| bish => Groupoid bish      -- ∅
| zfc  => Groupoid zfc       -- ★

/-- The unique functor ∅ ⥤ ★ shared by all pathology functors -/
def fromEmpty : Obj bish ⥤ Obj zfc :=
  Discrete.functor (fun x => x.down.elim)

end FoundationRelativity