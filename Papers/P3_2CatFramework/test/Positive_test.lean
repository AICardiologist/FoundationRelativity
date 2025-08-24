/-
  Papers/P3_2CatFramework/test/Positive_test.lean
  Tests for positive uniformization.
-/
import Papers.P3_2CatFramework.Phase2_Positive
import Papers.P3_2CatFramework.Phase3_Positive

open Papers.P3.Phase1Simple
open Papers.P3.Phase2
open Papers.P3.Phase2API
open Papers.P3.Phase2Positive
open Papers.P3.Phase3
open Papers.P3.Phase3Positive

/-! ## Gap: positive height = 1 -/

#check pos_uniformization_height1
#check pos_gap_height_eq_one

example : PosHeightAt GapFamily = some Level.one := pos_gap_height_eq_one

/-! ## Stone window mock: positive height = 0 (numeric) -/

#check pos_stone_height_nat_is_zero

/-! ## Bridges and equality on {0,1} -/

#check PosHeightAt_agrees_on_0_1

example :
  PosHeightAt GapFamily
    = (PosHeightAtNat GapFamily).bind ofNatLevel? := by
  simpa using PosHeightAt_agrees_on_0_1 GapFamily

example :
  PosHeightAt StoneWindowMock
    = (PosHeightAtNat StoneWindowMock).bind ofNatLevel? := by
  simpa using PosHeightAt_agrees_on_0_1 StoneWindowMock

/-! ## StoneWindowMock is positive at every level -/

#check stone_pos_uniform_all_k
example : PosUniformizableOnN 7 StoneWindowMock := stone_pos_uniform_all_k 7
example : PosUniformizableOnN 42 StoneWindowMock := stone_pos_uniform_all_k 42

#eval "Positive uniformization tests complete!"