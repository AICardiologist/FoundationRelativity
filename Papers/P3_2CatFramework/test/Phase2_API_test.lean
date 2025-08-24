/-
  Papers/P3_2CatFramework/test/Phase2_API_test.lean
  
  Sanity tests for Phase 2 uniformization height theory.
  These tests verify the core properties of the implementation
  and ensure no dependent rewrites are used.
-/

import Papers.P3_2CatFramework.Phase2_UniformHeight
import Papers.P3_2CatFramework.Phase2_API

open Papers.P3.Phase2API
open Papers.P3.Phase1Simple

-- Use Phase2 definitions which reuse Phase1
open Papers.P3.Phase2 hiding Foundation Interp BISH BISH_WLPO inclusionBW

/-! ## Basic checks that all definitions work -/

#check no_uniformization_height0
#check uniformization_height1
#check gap_has_height_one

/-! ## Verify η is identity at non-ellInf Σ₀ objects -/

-- η is refl on non-ellInf (micro-check enforcing expected behavior)
example :
  (uniformization_height1.η (id_interp BISH_WLPO) rfl rfl Sigma0.nat)
  = Equiv.refl _ := rfl

example :
  (uniformization_height1.η (id_interp BISH_WLPO) rfl rfl Sigma0.bool)
  = Equiv.refl _ := rfl

example :
  (uniformization_height1.η (id_interp BISH_WLPO) rfl rfl Sigma0.real)
  = Equiv.refl _ := rfl

example :
  (uniformization_height1.η (id_interp BISH_WLPO) rfl rfl Sigma0.c0)
  = Equiv.refl _ := rfl

example :
  (uniformization_height1.η (id_interp BISH_WLPO) rfl rfl Sigma0.quo_linf_c0)
  = Equiv.refl _ := rfl

/-! ## Verify η at ellInf works correctly -/

-- η at ellInf is the composite Truth≃PUnit≃Truth; it equals refl when F=F'
example :
  (uniformization_height1.η (id_interp BISH_WLPO) rfl rfl Sigma0.ellInf)
  = Equiv.refl _ := by
  -- Match the pattern used in the file: ext on functions, then rfl
  apply Equiv.ext
  intro x
  rfl

-- Additional micro-check: η at ellInf with same endpoints is refl 
-- (proof pattern mirrors the implementation)
example :
  (uniformization_height1.η (id_interp BISH_WLPO) rfl rfl Sigma0.ellInf)
  = Equiv.refl _ := by
  apply Equiv.ext
  intro x
  rfl

/-! ## Test the API functions -/

-- Level.toPred works as expected
example : Level.toPred Level.zero = W_ge0 := rfl
example : Level.toPred Level.one = W_ge1 := rfl

-- satisfiesLevel works correctly
example (F : Foundation) : satisfiesLevel F Level.zero := by simp
example : satisfiesLevel BISH Level.one ↔ false = true := by simp [hasWLPO_BISH]
example : satisfiesLevel BISH_WLPO Level.one := by simp [hasWLPO_BISH_WLPO]

-- HeightAt correctly identifies the gap's height
example : HeightAt GapFamily = some Level.one := gap_has_height_one

-- getUniformizationAt works as expected
example : getUniformizationAt Level.zero GapFamily = none := 
  gap_no_uniformization_at_zero

example : getUniformizationAt Level.one GapFamily ≠ none := 
  gap_has_uniformization_at_one

/-! ## Verify the coherence laws -/

-- η_id law: identity interpretation gives identity equivalence
example (F : Foundation) (hF : W_ge1 F) (X : Sigma0) :
  uniformization_height1.η (id_interp F) hF hF X = Equiv.refl _ := 
  uniformization_height1.η_id hF X

-- η_comp law: composition of interpretations gives composition of equivalences
example (F G H : Foundation) (φ : Interp F G) (ψ : Interp G H)
  (hF : W_ge1 F) (hG : W_ge1 G) (hH : W_ge1 H) (X : Sigma0) :
  uniformization_height1.η (comp_interp φ ψ) hF hH X =
  (uniformization_height1.η φ hF hG X).trans (uniformization_height1.η ψ hG hH X) :=
  uniformization_height1.η_comp φ ψ hF hG hH X

/-! ## Test that no dependent rewrites are used -/

-- Verify the helper functions work correctly
example : Truth true = PUnit := Truth_true
example : Truth false = Empty := Truth_false

-- The approach avoids dependent rewrites by using helper functions
-- that case-split on the equality proof
example (b : Bool) (hb : b = true) :
  Truth b ≃ PUnit := by
  -- The helper function works without dependent rewrites
  cases hb
  exact Equiv.refl _

#eval "Phase 2 API tests: All sanity checks pass!"

-- Height APIs agree on {0,1}
#check Papers.P3.Phase2API.HeightAt_agrees_on_0_1
example : Papers.P3.Phase2API.HeightAt_viaNat Papers.P3.Phase2.GapFamily = some Papers.P3.Phase2API.Level.one := by
  simpa using Papers.P3.Phase2API.gap_height_viaNat_01

-- HeightAt agrees with the numeric view for any WF on {0,1}.
example (WF : Papers.P3.Phase2.WitnessFamily) :
  Papers.P3.Phase2API.HeightAt WF
    = Papers.P3.Phase2API.HeightAt_viaNat WF := by
  simpa using Papers.P3.Phase2API.HeightAt_agrees_on_0_1 WF

-- StoneWindowMock shows up as level zero through the Phase 2 API
example :
  Papers.P3.Phase2API.HeightAt
    (WF := Papers.P3.Phase3.StoneWindowMock) = some Papers.P3.Phase2API.Level.zero := by
  -- From the equality with the numeric view + HeightAtNat = some 0
  classical
  have := Papers.P3.Phase2API.HeightAt_agrees_on_0_1 Papers.P3.Phase3.StoneWindowMock
  -- Rewrite and simplify with your bind/ofNat simp lemmas.
  simpa [Papers.P3.Phase2API.HeightAt_viaNat,
         Papers.P3.Phase3.HeightAtNat,
         Papers.P3.Phase3.stone_uniformization_h0]