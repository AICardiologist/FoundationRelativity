/-
  Placeholder witness set for the bidual‑gap pathology.

  * Empty in constructive foundations
  * Singleton in classical foundations
-/
import Found.InterpCore

open Foundation

namespace Gap

def Witness : Foundation → Type
  | bish => Empty
  | zfc  => PUnit

instance : Inhabited (Witness zfc) := ⟨PUnit.unit⟩

/-- Discrete groupoid on the witness type. -/
def Groupoid (F : Foundation) : Cat :=
  Cat.of (ULift (Witness F))

end Gap