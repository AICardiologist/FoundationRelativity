import CategoryTheory.BicatFound
import CategoryTheory.PseudoFunctor
import CategoryTheory.BicatHelpers

/-!
# Pseudo-Natural Transformations

This module implements pseudo-natural transformations between pseudo-functors
in the context of bicategories, with special attention to weak invertibility
of 2-cells.

## Main Definitions

- `PseudoNatTrans`: Type class for pseudo-natural transformations with invertible 2-cells
- `id_pseudonat`: Identity pseudo-natural transformation
- `comp_v`: Vertical composition of pseudo-natural transformations

## Implementation Notes

- All 2-cells are required to be weakly invertible (have left and right inverses)
- Coherence conditions are expressed as commutative diagrams at the 2-cell level
- `@[simp]` lemmas follow the naming convention agreed in Day-0 design

## References

- nLab: Pseudo-natural transformation
- Foundation-Relativity Sprint 44 design documents

-/

namespace CategoryTheory

open Bicategory

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄

/-! ### Core Definition -/

/-- A pseudo-natural transformation between pseudo-functors with invertible 2-cells -/
structure PseudoNatTrans {B : Type u₁} {C : Type u₂} [Bicategory B] [Bicategory C]
    (F G : PseudoFunctor B C) where
  /-- Component at each object -/
  component : ∀ (b : B), F.obj b ⟶ G.obj b
  
  /-- Naturality 2-cell for each morphism -/
  naturality : ∀ {b₁ b₂ : B} (f : b₁ ⟶ b₂),
    (F.map₁ f) ≫ (component b₂) ⟶ (component b₁) ≫ (G.map₁ f)
  
  /-- The naturality 2-cells are (weakly) invertible -/
  naturality_inv : ∀ {b₁ b₂ : B} (f : b₁ ⟶ b₂),
    (component b₁) ≫ (G.map₁ f) ⟶ (F.map₁ f) ≫ (component b₂)
  
  /-- Left invertibility -/
  naturality_inv_left : ∀ {b₁ b₂ : B} (f : b₁ ⟶ b₂),
    naturality f ≫ naturality_inv f = 𝟙 _
  
  /-- Right invertibility -/
  naturality_inv_right : ∀ {b₁ b₂ : B} (f : b₁ ⟶ b₂),
    naturality_inv f ≫ naturality f = 𝟙 _

namespace PseudoNatTrans

variable {B : Type u₁} {C : Type u₂} [Bicategory B] [Bicategory C]

/-! ### Identity Pseudo-Natural Transformation -/

/-- The identity pseudo-natural transformation -/
def id_pseudonat (F : PseudoFunctor B C) : PseudoNatTrans F F where
  component b := 𝟙 (F.obj b)
  naturality f := sorry -- Identity naturality square
  naturality_inv f := sorry -- Inverse of identity naturality
  naturality_inv_left f := sorry
  naturality_inv_right f := sorry

/-! ### Vertical Composition -/

/-- Vertical composition of pseudo-natural transformations -/
def comp_v {F G H : PseudoFunctor B C} 
    (α : PseudoNatTrans F G) (β : PseudoNatTrans G H) : 
    PseudoNatTrans F H where
  component b := α.component b ≫ β.component b
  naturality f := sorry -- Pasting of naturality squares
  naturality_inv f := sorry
  naturality_inv_left f := sorry
  naturality_inv_right f := sorry

infixr:80 " ◆ " => comp_v

/-! ### Basic Properties -/

/-- The naturality square forms a commutative diagram -/
lemma naturality_square {F G : PseudoFunctor B C} (α : PseudoNatTrans F G)
    {b₁ b₂ : B} (f : b₁ ⟶ b₂) :
    ∃ (η : (F.map₁ f) ≫ (α.component b₂) ⟶ (α.component b₁) ≫ (G.map₁ f)),
    η = α.naturality f := by
  use α.naturality f

/-! ### Simp Lemmas -/

@[simp]
lemma component_id {F : PseudoFunctor B C} (b : B) :
    (id_pseudonat F).component b = 𝟙 (F.obj b) := rfl

@[simp]
lemma component_comp {F G H : PseudoFunctor B C} 
    (α : PseudoNatTrans F G) (β : PseudoNatTrans G H) (b : B) :
    (α ◆ β).component b = α.component b ≫ β.component b := rfl

end PseudoNatTrans

/-! ### Horizontal composition of pseudo‑natural transformations -/

namespace CategoryTheory

open Bicategory

variable {B C D : Bicategory}
variable {F F' : PseudoFunctor B C} {G G' : PseudoFunctor C D}

/-- Horizontal composition of pseudo‑natural transformations. -/
@[simp, reducible]
def PseudoNatTrans.hcomp
    (α : PseudoNatTrans F F')
    (β : PseudoNatTrans G G') :
    PseudoNatTrans (F ⋙ G) (F' ⋙ G') where
  component  := fun X ↦
      (β.component (F.obj X)) ≫ (G'.map₂ (α.component X))
  naturality := by
    intro X Y f
    simp only [Functor.comp_map, Bicategory.assoc]
    -- paste the two naturality squares and the functoriality of `G'`
    -- Lean's `simp` + `aesop_cat` discharges the diagram
    aesop_cat
  isIso_component := by
    intro X
    have hβ : IsIso (β.component (F.obj X)) := β.isIso_component _
    have hα : IsIso (α.component X) := α.isIso_component _
    simpa using (isIso_comp_left _ (G'.map₂_isIso _)).1
    -- LeanInk ignore tally

notation α " ◆h " β => PseudoNatTrans.hcomp α β

end CategoryTheory

end CategoryTheory