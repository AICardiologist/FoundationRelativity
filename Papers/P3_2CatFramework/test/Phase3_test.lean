/-
  Papers/P3_2CatFramework/test/Phase3_test.lean
-/
import Papers.P3_2CatFramework.Phase3_Levels
-- import Papers.P3_2CatFramework.Phase3_Obstruction  -- Moved to archive
import Papers.P3_2CatFramework.Phase3_StoneWindowMock
import Papers.P3_2CatFramework.Phase2_API

open Papers.P3.Phase1Simple
open Papers.P3.Phase2
open Papers.P3.Phase3

-- HeightAtNat computes 1 for the gap
#check gap_height_nat_is_one

-- Obstruction lemma recovers the Phase 2 negative result at level 0
-- #check gap_obstructs_at_zero  -- From Phase3_Obstruction (now in archive)

-- StoneWindowMock is uniformizable at 0
#check stone_uniformization_h0

-- StoneWindowMock has numeric height 0
example : Papers.P3.Phase3.HeightAtNat Papers.P3.Phase3.StoneWindowMock = some 0 := by
  -- By definition: there is a level-0 uniformization and we ignore higher levels.
  unfold Papers.P3.Phase3.HeightAtNat
  -- We have stone_uniformization_h0 : UniformizableOn W_ge0 StoneWindowMock
  -- This gives us UniformizableOnN 0 via toN0
  have h0 : Nonempty (Papers.P3.Phase3.UniformizableOnN 0 Papers.P3.Phase3.StoneWindowMock) :=
    ⟨Papers.P3.Phase3.UniformizableOn.toN0 Papers.P3.Phase3.stone_uniformization_h0⟩
  simp [h0]

-- Height APIs also agree on the positive example at level 0, via the Phase 2 bridge.
example :
  Papers.P3.Phase2API.HeightAt_viaNat Papers.P3.Phase3.StoneWindowMock
    = some Papers.P3.Phase2API.Level.zero := by
  -- HeightAtNat StoneWindowMock = some 0 by construction (uniformizable at 0)
  -- so the Phase 2 view must pick Level.zero.
  unfold Papers.P3.Phase2API.HeightAt_viaNat Papers.P3.Phase3.HeightAtNat
  have h0 : Nonempty (Papers.P3.Phase3.UniformizableOnN 0 Papers.P3.Phase3.StoneWindowMock) :=
    ⟨Papers.P3.Phase3.UniformizableOn.toN0 Papers.P3.Phase3.stone_uniformization_h0⟩
  simp [h0, Papers.P3.Phase2API.ofNatLevel?]

-- StoneWindowMock shows up as level zero through the Phase 2 API (moved from Phase2_API_test)
example :
  Papers.P3.Phase2API.HeightAt Papers.P3.Phase3.StoneWindowMock 
    = some Papers.P3.Phase2API.Level.zero := by
  -- Use the HeightAt_viaNat bridge and the fact that HeightAtNat = some 0
  rw [Papers.P3.Phase2API.HeightAt_agrees_on_0_1]
  unfold Papers.P3.Phase2API.HeightAt_viaNat Papers.P3.Phase3.HeightAtNat
  have h0 : Nonempty (Papers.P3.Phase3.UniformizableOnN 0 Papers.P3.Phase3.StoneWindowMock) :=
    ⟨Papers.P3.Phase3.UniformizableOn.toN0 Papers.P3.Phase3.stone_uniformization_h0⟩
  simp [h0, Papers.P3.Phase2API.ofNatLevel?]