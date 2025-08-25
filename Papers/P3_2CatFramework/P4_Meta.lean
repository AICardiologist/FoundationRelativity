/-
  Papers/P3_2CatFramework/P4_Meta.lean
  Single import surface for the Paper 3 meta layer (P4_Meta).
-/
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature
import Papers.P3_2CatFramework.P4_Meta.Meta_Witnesses
import Papers.P3_2CatFramework.P4_Meta.Meta_Ladders
import Papers.P3_2CatFramework.P4_Meta.Meta_UpperBounds
import Papers.P3_2CatFramework.P4_Meta.Meta_LowerBounds_Axioms
import Papers.P3_2CatFramework.P4_Meta.PartIII_Certificates
import Papers.P3_2CatFramework.P4_Meta.PartIII_Ladders
import Papers.P3_2CatFramework.P4_Meta.PartIII_ProductSup
import Papers.P3_2CatFramework.P4_Meta.PartIII_MultiSup
import Papers.P3_2CatFramework.P4_Meta.PartIII_Concat
import Papers.P3_2CatFramework.P4_Meta.PartIII_NormalForm
import Papers.P3_2CatFramework.P4_Meta.PartIII_PosFam
import Papers.P3_2CatFramework.P4_Meta.PartIV_Limit
import Papers.P3_2CatFramework.P4_Meta.PartV_Interfaces
import Papers.P3_2CatFramework.P4_Meta.PartV_Reflection
import Papers.P3_2CatFramework.P4_Meta.PartV_Collision
import Papers.P3_2CatFramework.P4_Meta.PartV_Strictness
import Papers.P3_2CatFramework.P4_Meta.StoneWindow
import Papers.P3_2CatFramework.P4_Meta.PartVI_Calibrators
-- Note: P3_P4_Bridge is not imported here to avoid cycles
-- Paper 3 files import P4_Meta, then P3_P4_Bridge separately if needed