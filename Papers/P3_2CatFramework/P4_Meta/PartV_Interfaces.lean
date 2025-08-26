/-
  Papers/P4_Meta/PartV_Interfaces.lean
  
  Interfaces for Part V collision theorems: HBL, RE, consistency predicates.
  These are abstract typeclasses that capture the key properties needed
  for the reflection → consistency → Gödel collision chain.
-/
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature

namespace Papers.P4Meta.PartV

open Papers.P4Meta

/-- Base "tags" for the schematic meta formulas. -/
@[simp] def Con (_ : Theory) : Formula := Formula.atom 200
@[simp] def RFN_Sigma1 (_ : Theory) : Formula := Formula.atom 201
@[simp] def GodelSentence (_ : Theory) : Formula := Formula.atom 202

/-- Derivability & rec. axiomatizability tags (schematic). -/
class HBL (T : Theory) : Prop
class RE (T : Theory) : Prop
class Consistent (T : Theory) : Prop

/-- HBL and RE are preserved by our schematic "Extend". -/
instance extend_preserves_HBL (T : Theory) [HBL T] (φ : Formula) :
  HBL (Extend T φ) := ⟨⟩

instance extend_preserves_RE (T : Theory) [RE T] (φ : Formula) :
  RE (Extend T φ) := ⟨⟩

end Papers.P4Meta.PartV