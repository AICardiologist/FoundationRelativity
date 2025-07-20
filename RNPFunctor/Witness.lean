import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Functor.Basic
import Found.InterpCore

open CategoryTheory Foundation

namespace RNPFail

def Witness : Foundation → Type
  | bish => Empty
  | zfc  => PUnit

instance : Inhabited (Witness zfc) := ⟨PUnit.unit⟩

def Groupoid (F : Foundation) : Cat :=
  Cat.of (Discrete (ULift (Witness F)))


end RNPFail