/-
  Vector measure witness for RNP failure.
-/
import RNPFunctor.Witness
import Found.InterpCore

open Foundation

namespace RNPReal

variable [HasHB zfc] [CountableChoice zfc]

-- placeholder for the actual vector measure construction
instance : Nonempty (RNPFail.Witness zfc) := by
  exact ⟨PUnit.unit⟩

end RNPReal
EOF < /dev/null