/-
  File: Papers/P3_2CatFramework/P4_Meta/FusedLadders.lean
  
  Purpose: WP-E Cross-axis Transfer via Fused Ladders
  - Fused ladder construction (lexicographic product)
  - Product height theorem: max law for orthogonal witnesses
  - Connects to Part II product/sup infrastructure
-/

import Papers.P3_2CatFramework.P4_Meta.Frontier_API
import Papers.P3_2CatFramework.P4_Meta.IndependenceRegistry

namespace Papers.P4Meta

section FusedLadders

/-! ### Abstract Height Framework -/

/-- Abstract "height at stage a on ladder L" as a predicate indexed by L and stage. -/
variable (HeightAt : (Ladder : Type*) → ℕ → (Prop → Prop))

/-- A ladder is a well-ordered sequence of theories/foundations. -/
structure Ladder where
  stages : ℕ → Type*  -- Theory at each stage
  order : ∀ n, stages n → stages (n+1)  -- Inclusions

/-- Fused ladder constructor: lexicographic product.
    A stage in the fused ladder dominates both coordinates. -/
def fuseLadders (L1 L2 : Ladder) : Ladder where
  stages := fun n => L1.stages n × L2.stages n
  order := fun n => fun ⟨t1, t2⟩ => ⟨L1.order n t1, L2.order n t2⟩

/-- Alternative: Simple type-level fused ladder for the interface. -/
def fuse (L1 L2 : Type*) : Type* := L1 × L2

/-! ### Product Height Theorems -/

/-- Product height over fused ladders: max law (interface lemma).
    
    Key theorem: If C has height a on L1 and D has height b on L2,
    then C × D has height max(a,b) on the fused ladder L1 ⊗ L2.
    
    This justifies taking max when combining orthogonal witnesses. -/
axiom height_product_on_fuse
    {L1 L2 : Type*} {a b : ℕ} {C D : Prop}
    (hC : HeightAt L1 a C) 
    (hD : HeightAt L2 b D) :
    HeightAt (fuse L1 L2) (max a b) (C ∧ D)

/-- Specialized version for standard axes. -/
theorem height_product_WLPO_FT
    {HeightAt : Type* → ℕ → (Prop → Prop)}
    {WLPO_ladder FT_ladder : Type*}
    {Gap UCT : Prop}
    (hGap : HeightAt WLPO_ladder 1 Gap)
    (hUCT : HeightAt FT_ladder 1 UCT) :
    HeightAt (fuse WLPO_ladder FT_ladder) 1 (Gap ∧ UCT) :=
  height_product_on_fuse HeightAt hGap hUCT

/-! ### Cross-Axis Composites -/

/-- Example application: UCT × Gap has profile (1,1) on fused ladder. -/
example (HeightAt : Type* → ℕ → (Prop → Prop))
    (WLPO_ladder FT_ladder : Type*)
    (Gap UCT : Prop)
    (gap_height : HeightAt WLPO_ladder 1 Gap)
    (uct_height : HeightAt FT_ladder 1 UCT)
    (_indep : Independent WLPO FT) :
    HeightAt (fuse WLPO_ladder FT_ladder) 1 (Gap ∧ UCT) := by
  -- Both at height 1, so max{1,1} = 1
  exact height_product_WLPO_FT HeightAt gap_height uct_height

/-- For witnesses at different heights, we get the maximum. -/
theorem height_product_asymmetric
    {HeightAt : Type* → ℕ → (Prop → Prop)}
    {L1 L2 : Type*}
    {C D : Prop}
    (hC : HeightAt L1 0 C)  -- C at height 0
    (hD : HeightAt L2 2 D)  -- D at height 2
    : HeightAt (fuse L1 L2) 2 (C ∧ D) :=
  height_product_on_fuse HeightAt hC hD

end FusedLadders

/-! ### Integration Notes

This interface file provides the cross-axis transfer lemma (Proposition VI.6 from the paper).
To complete the implementation:

1. Replace the abstract HeightAt with your concrete height certificate type
2. Connect height_product_on_fuse to your Part II product/sup law
3. Use these lemmas when computing heights for composite witnesses

The key insight: orthogonal axes contribute independently to the total height,
justifying the max operation in the fused ladder.
-/

end Papers.P4Meta