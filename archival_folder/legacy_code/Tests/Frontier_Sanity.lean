/-
  File: Tests/Frontier_Sanity.lean
  
  Purpose:
  - Micro-tests for the Frontier API surface
  - Property sanity checks for reduction composition
  - No heavy dependencies, just API protection during refactors
-/
import Papers.P3_2CatFramework.P4_Meta.Frontier_API

open Papers.P4Meta
open scoped Papers.P4Meta

section BasicComposition
  variable {P Q R WLPO Gap : Prop}
  variable (portal : Gap ↔ WLPO)

  -- Test that reductions compose properly
  example (f : P → Q) (g : Q → R) :
      (reduces f).trans (reduces g) = (reduces f).trans (reduces g) := by
    rfl

  -- Test that equivalences are preserved
  example (e : WLPO ↔ Gap) : WLPO ↔ Gap := e

  -- Test the portal shuttling
  example (h : P → WLPO) : P → Gap :=
    toGap_of_toWLPO' portal h
    
  -- Test reduction from equivalence
  example (e : P ↔ Q) : P ⟶ Q :=
    reduces_of_iff_mp e
    
  -- Test reverse reduction from equivalence
  example (e : P ↔ Q) : Q ⟶ P :=
    reduces_of_iff_mpr e
end BasicComposition

section CalcChains
  variable {P Q R S : Prop}
  
  -- Test that Trans instance enables calc
  example (f : P ⟶ Q) (g : Q ⟶ R) (h : R ⟶ S) : P ⟶ S := by
    calc P ⟶ Q := f
         _ ⟶ R := g
         _ ⟶ S := h
end CalcChains

section PortalPattern
  variable {WLPO Gap Stone : Prop}
  variable (portal : Gap ↔ WLPO)
  
  -- Standard portal pattern: Stone → WLPO gives Stone → Gap
  example (h : Stone → WLPO) : Stone → Gap :=
    toGap_of_toWLPO' portal h
  
  -- Equivalence pattern: Stone ↔ WLPO gives Stone ↔ Gap
  example (toW : Stone → WLPO) (fromW : WLPO → Stone) : Stone ↔ Gap :=
    equiv_with_Gap_via_WLPO' portal toW fromW
    
  -- Using reduction structures
  example (r : Stone ⟶ WLPO) : Stone ⟶ Gap :=
    toGap_of_toWLPO portal r
end PortalPattern

section HeightTemplate
  variable {HeightCert : Prop → Prop}
  variable {WLPO Gap P : Prop}
  variable (height_mono : ∀ {P Q}, (P → Q) → HeightCert P → HeightCert Q)
  variable (portal : Gap ↔ WLPO)
  variable (gap_h1 : HeightCert Gap)
  
  -- Height transport through portal
  example (fromW : WLPO → P) : HeightCert P :=
    height_of_from_WLPO height_mono portal gap_h1 fromW
    
  -- Height from equivalence
  example (height_equiv : ∀ {P Q}, (P ↔ Q) → HeightCert Q → HeightCert P)
          (e : P ↔ Gap) : HeightCert P :=
    height_of_equiv_with_Gap height_equiv gap_h1 e
end HeightTemplate

-- Sanity check that run extraction works
section RunExtraction
  variable {P Q R : Prop}
  
  example (f : P ⟶ Q) (g : Q ⟶ R) (p : P) : R :=
    (f.trans g).run p
    
  example : ∀ (f : P ⟶ Q) (g : Q ⟶ R), 
      (f.trans g).run = fun p => g.run (f.run p) := by
    intros; rfl
end RunExtraction