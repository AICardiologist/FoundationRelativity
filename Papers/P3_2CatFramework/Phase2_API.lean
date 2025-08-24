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

/-- Map numeric levels to Phase 2's `Level` (only defined on {0,1}). -/
def ofNatLevel? : Nat → Option Level
  | 0 => some Level.zero
  | 1 => some Level.one
  | _ => none

/-- Re-express `HeightAt` via the numeric height (dropping ≥2 as `none`). -/
noncomputable def HeightAt_viaNat (WF : Papers.P3.Phase2.WitnessFamily) : Option Level :=
  (Papers.P3.Phase3.HeightAtNat WF).bind ofNatLevel?

@[simp] lemma ofNatLevel?_zero : ofNatLevel? 0 = some Level.zero := rfl
@[simp] lemma ofNatLevel?_one  : ofNatLevel? 1 = some Level.one  := rfl

@[simp] lemma bind_ofNatLevel?_none :
  (Option.bind (none : Option Nat) ofNatLevel?) = (none : Option Level) := rfl
@[simp] lemma bind_ofNatLevel?_some_zero :
  (Option.bind (some 0) ofNatLevel?) = some Level.zero := rfl
@[simp] lemma bind_ofNatLevel?_some_one :
  (Option.bind (some 1) ofNatLevel?) = some Level.one := rfl

/-- Bridges showing the `Nonempty` conditions coincide at 0 and 1. -/
lemma bridge0 (WF : Papers.P3.Phase2.WitnessFamily) :
  (Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge0 WF)) ↔ (Nonempty (Papers.P3.Phase3.UniformizableOnN 0 WF)) :=
⟨ (fun ⟨u⟩ => ⟨Papers.P3.Phase3.UniformizableOn.toN0 u⟩),
  (fun ⟨v⟩ => ⟨Papers.P3.Phase3.toW0 v⟩) ⟩

lemma bridge1 (WF : Papers.P3.Phase2.WitnessFamily) :
  (Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge1 WF)) ↔ (Nonempty (Papers.P3.Phase3.UniformizableOnN 1 WF)) :=
⟨ (fun ⟨u⟩ => ⟨Papers.P3.Phase3.UniformizableOn.toN1 u⟩),
  (fun ⟨v⟩ => ⟨Papers.P3.Phase3.toW1 v⟩) ⟩

/-- On {0,1}, the Phase 2 `HeightAt` equals the Phase 3 numeric height view. -/
theorem HeightAt_agrees_on_0_1 (WF : Papers.P3.Phase2.WitnessFamily) :
  HeightAt WF = HeightAt_viaNat WF := by
  classical
  -- Unfold both definitions into two if-branches.
  unfold HeightAt HeightAt_viaNat
  -- Case on existence at level 0; use the bridge lemmas to sync conditions.
  by_cases h0 : Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge0 WF)
  · simp [h0, bridge0 WF]
  · simp [h0, bridge0 WF]
    -- Now decide level 1, again via the bridge.
    by_cases h1 : Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge1 WF)
    · simp [h1, bridge1 WF]
    · simp [h1, bridge1 WF]

@[simp] theorem gap_height_viaNat_01 :
  HeightAt_viaNat Papers.P3.Phase2.GapFamily = some Level.one := by
  simp [HeightAt_viaNat, Papers.P3.Phase3.gap_height_nat_is_one]

end Papers.P3.Phase2API