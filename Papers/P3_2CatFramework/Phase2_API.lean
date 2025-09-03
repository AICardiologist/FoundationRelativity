import Papers.P3_2CatFramework.Phase2_UniformHeight
import Papers.P3_2CatFramework.Phase3_Levels

/-!
  # Phase 2 API: Uniformization Height Theory
  
  Clean API for the uniformization height framework.
  
  ## Overview
  This module provides the main interface for measuring logical strength
  via uniformizability of witness families. Based on Paul's guidance,
  it cleanly encapsulates the height computation without exposing internals.
  
  ## Key Concepts
  - **Level**: Discrete height values (0 = BISH, 1 = BISH+WLPO)
  - **HeightAt**: Computes minimum uniformization level for a witness family
  - **Gap Theorem**: The bidual gap has height exactly 1 (calibration point)
-/

namespace Papers.P3.Phase2API

open Papers.P3.Phase2
open Classical  -- Needed for choice

/-! ## Level definitions for uniformization height -/

/-- 
Level in the uniformization hierarchy.

- `zero`: Height 0, uniformizable in BISH (all foundations)
- `one`: Height 1, requires WLPO for uniformization

Future work will extend this to higher levels (DC_ω, etc.).
-/
inductive Level
  | zero  -- All foundations (height ≥ 0)
  | one   -- Foundations with WLPO (height ≥ 1)
deriving DecidableEq, Repr

/-- 
Convert a Level to its corresponding foundation predicate.

Maps discrete levels to the set of foundations at that height or above.
-/
@[simp] def Level.toPred : Level → (Foundation → Prop)
  | Level.zero => W_ge0  -- Always true
  | Level.one  => W_ge1  -- hasWLPO F = true

/-! ## Height determination for witness families -/

/-- 
Determines the uniformization height of a witness family.

## Returns
- `some Level.zero`: Uniformizable in BISH
- `some Level.one`: Requires WLPO for uniformization
- `none`: Not uniformizable at levels 0 or 1

## Implementation Note
Uses classical logic for decidability. The if-chain is a placeholder
for a proper lattice of levels to be developed in future phases.
-/
noncomputable def HeightAt (WF : WitnessFamily) : Option Level :=
  if h₀ : Nonempty (UniformizableOn W_ge0 WF) then
    some Level.zero
  else if h₁ : Nonempty (UniformizableOn W_ge1 WF) then
    some Level.one
  else
    none

/-! ## Main theorem: The bidual gap has height = 1 -/

/-- 
**Main Calibration Theorem**: The bidual gap has height exactly 1.

This is the key calibration point showing that the bidual gap:
- Cannot be uniformized in BISH (height > 0)
- Can be uniformized with WLPO (height = 1)

This theorem anchors the entire uniformization hierarchy.
-/
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

/-- 
Check if a foundation satisfies a given level requirement.

Returns true if foundation F is at height ≥ l in the hierarchy.
-/
@[simp]
def satisfiesLevel (F : Foundation) (l : Level) : Prop :=
  l.toPred F

/-- 
Extract the uniformization witness at a specific level (if it exists).

Returns the actual uniformization data when available.
-/
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

/-- 
Numeric height computation from Phase 3, exposed via Phase 2 API.

Provides natural number heights for future extensions beyond level 1.
-/
noncomputable def HeightAtNat_viaPhase2 (WF : Papers.P3.Phase2.WitnessFamily) : Option Nat :=
  Papers.P3.Phase3.HeightAtNat WF

@[simp] theorem gap_height_nat_viaPhase2 :
  HeightAtNat_viaPhase2 Papers.P3.Phase2.GapFamily = some 1 := by
  simp [HeightAtNat_viaPhase2, Papers.P3.Phase3.gap_height_nat_is_one]

/-- 
Convert natural number heights to Level type.

Currently only handles levels 0 and 1; returns none for higher levels
until the framework is extended.
-/
def ofNatLevel? : Nat → Option Level
  | 0 => some Level.zero
  | 1 => some Level.one
  | _ => none

/-- 
Alternative height computation via numeric levels.

Bridges between the discrete Level type and natural number heights.
-/
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
@[simp] lemma bridge0 (WF : Papers.P3.Phase2.WitnessFamily) :
  (Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge0 WF)) ↔ (Nonempty (Papers.P3.Phase3.UniformizableOnN 0 WF)) :=
⟨ (fun ⟨u⟩ => ⟨Papers.P3.Phase3.UniformizableOn.toN0 u⟩),
  (fun ⟨v⟩ => ⟨Papers.P3.Phase3.toW0 v⟩) ⟩

@[simp] lemma bridge1 (WF : Papers.P3.Phase2.WitnessFamily) :
  (Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge1 WF)) ↔ (Nonempty (Papers.P3.Phase3.UniformizableOnN 1 WF)) :=
⟨ (fun ⟨u⟩ => ⟨Papers.P3.Phase3.UniformizableOn.toN1 u⟩),
  (fun ⟨v⟩ => ⟨Papers.P3.Phase3.toW1 v⟩) ⟩

/-- 
**Consistency Theorem**: Phase 2 and Phase 3 height computations agree.

Shows that the Level-based and Nat-based height computations
are equivalent on levels 0 and 1.
-/
theorem HeightAt_agrees_on_0_1 (WF : Papers.P3.Phase2.WitnessFamily) :
  HeightAt WF = HeightAt_viaNat WF := by
  classical
  unfold HeightAt HeightAt_viaNat Papers.P3.Phase3.HeightAtNat
  -- Both sides compute height based on the same uniformization conditions
  by_cases h0 : Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge0 WF)
  · -- Case: uniformizable at level 0
    -- bridge0 tells us UniformizableOn W_ge0 ↔ UniformizableOnN 0
    rw [bridge0] at h0
    simp [h0, ofNatLevel?]
  · -- Case: not uniformizable at level 0
    rw [bridge0] at h0
    simp [h0]
    by_cases h1 : Nonempty (Papers.P3.Phase2.UniformizableOn Papers.P3.Phase2.W_ge1 WF)
    · -- Case: uniformizable at level 1
      rw [bridge1] at h1
      simp [h1, ofNatLevel?]
    · -- Case: not uniformizable at either level
      rw [bridge1] at h1
      simp [h1, ofNatLevel?]

@[simp] theorem gap_height_viaNat_01 :
  HeightAt_viaNat Papers.P3.Phase2.GapFamily = some Level.one := by
  simp [HeightAt_viaNat, Papers.P3.Phase3.gap_height_nat_is_one]

end Papers.P3.Phase2API