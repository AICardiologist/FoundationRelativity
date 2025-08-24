/-
  Papers/P3_2CatFramework/test/Phase3_test.lean
-/
import Papers.P3_2CatFramework.Phase3_Levels
import Papers.P3_2CatFramework.Phase3_Obstruction
import Papers.P3_2CatFramework.Phase3_StoneWindowMock

open Papers.P3.Phase1Simple
open Papers.P3.Phase2
open Papers.P3.Phase3

-- HeightAtNat computes 1 for the gap
#check gap_height_nat_is_one

-- Obstruction lemma recovers the Phase 2 negative result at level 0
#check gap_obstructs_at_zero

-- StoneWindowMock is uniformizable at 0
#check stone_uniformization_h0