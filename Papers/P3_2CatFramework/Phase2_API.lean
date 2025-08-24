/-
  Papers/P3_2CatFramework/Phase2_API.lean
  
  Clean API for Phase 2: Uniformization height theory
  
  Based on Paul's guidance, this provides a clean interface to the
  uniformization height concepts without exposing the internal details.
-/

import Papers.P3_2CatFramework.Phase2_UniformHeight
import Papers.P3_2CatFramework.Phase3_Levels

namespace Papers.P3.Phase2API

open Papers.P3.Phase2
open Classical  -- Needed for choice

/-! ## Level definitions for uniformization height -/

/-- Level represents the height in the uniformization hierarchy -/
inductive Level
  | zero  -- All foundations (height ≥ 0)
  | one   -- Foundations with WLPO (height ≥ 1)
deriving DecidableEq, Repr

/-- Convert a Level to the corresponding foundation predicate -/
@[simp] def Level.toPred : Level → (Foundation → Prop)
  | Level.zero => W_ge0  -- Always true
  | Level.one  => W_ge1  -- hasWLPO F = true

/-! ## Height determination for witness families -/

/-- 
  HeightAt determines the uniformization height of a witness family.
  Returns the minimum level at which uniformization exists.
  
  Uses classical logic for decidability. This is intentionally non-decidable
  beyond level 1 for now; the if-chain is a placeholder for a real lattice 
  of levels that will be developed in Phase 3+.
-/
noncomputable def HeightAt (WF : WitnessFamily) : Option Level :=
  if h₀ : Nonempty (UniformizableOn W_ge0 WF) then
    some Level.zero
  else if h₁ : Nonempty (UniformizableOn W_ge1 WF) then
    some Level.one
  else
    none

/-! ## Main theorem: The bidual gap has height = 1 -/

/-- The bidual gap witness family has uniformization height exactly 1 -/
theorem gap_has_height_one : HeightAt GapFamily = some Level.one := by
  unfold HeightAt
  -- First branch: height 0 fails
  have neg_h0 := no_uniformization_height0
  simp only [dif_neg neg_h0]
  -- Second branch: height 1 succeeds
  have pos_h1 : Nonempty (UniformizableOn W_ge1 GapFamily) := 
    ⟨uniformization_height1⟩
  simp only [dif_pos pos_h1]

/-! ## Helper functions for working with uniformization -/

/-- Check if a foundation satisfies a given level requirement -/
def satisfiesLevel (F : Foundation) (l : Level) : Prop :=
  l.toPred F

/-- Get uniformization at a specific level (if it exists) -/
noncomputable def getUniformizationAt (l : Level) (WF : WitnessFamily) : 
    Option (UniformizableOn l.toPred WF) :=
  match l with
  | Level.zero => 
      if h : Nonempty (UniformizableOn W_ge0 WF) then 
        some (Classical.choice h)
      else none
  | Level.one => 
      if h : Nonempty (UniformizableOn W_ge1 WF) then
        some (Classical.choice h)  
      else none

/-! ## Properties and lemmas -/

@[simp] lemma satisfiesLevel_zero (F : Foundation) : 
  satisfiesLevel F Level.zero := by
  unfold satisfiesLevel Level.toPred W_ge0
  trivial

@[simp] lemma satisfiesLevel_one (F : Foundation) :
  satisfiesLevel F Level.one ↔ hasWLPO F = true := by
  unfold satisfiesLevel Level.toPred W_ge1
  rfl

lemma gap_no_uniformization_at_zero :
  getUniformizationAt Level.zero GapFamily = none := by
  simp only [getUniformizationAt]
  have neg := no_uniformization_height0
  simp only [dif_neg neg]

lemma gap_has_uniformization_at_one :
  getUniformizationAt Level.one GapFamily ≠ none := by
  simp only [getUniformizationAt]
  have pos : Nonempty (UniformizableOn W_ge1 GapFamily) := 
    ⟨uniformization_height1⟩
  simp only [dif_pos pos]
  intro h
  exact Option.some_ne_none _ h

/-! ## Summary -/

#check gap_has_height_one
#check HeightAt
#check Level

#eval "Phase 2 API: Clean interface for uniformization height theory complete!"

/-- Phase 3 numeric height, re-exposed through the Phase 2 API. -/
noncomputable def HeightAtNat_viaPhase2 (WF : Papers.P3.Phase2.WitnessFamily) : Option Nat :=
  Papers.P3.Phase3.HeightAtNat WF

@[simp] theorem gap_height_nat_viaPhase2 :
  HeightAtNat_viaPhase2 Papers.P3.Phase2.GapFamily = some 1 := by
  simp [HeightAtNat_viaPhase2, Papers.P3.Phase3.gap_height_nat_is_one]

end Papers.P3.Phase2API