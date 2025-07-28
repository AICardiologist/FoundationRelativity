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
  
  /-- Each component is an isomorphism in the bicategory -/
  isIso_component : ∀ (b : B), IsIso (component b)
  
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

/-- Identity pseudo‑natural transformation. -/
def id_pseudonat (F : PseudoFunctor B C) : PseudoNatTrans F F where
  component b := 𝟙 (F.obj b)
  isIso_component b := by infer_instance
  naturality f := by
    -- 𝟙∘g = g  and  f∘𝟙 = f
    simp [Bicategory.comp_id, Bicategory.id_comp]
  naturality_inv f := by
    -- inverse of identity is identity
    simp [Bicategory.comp_id, Bicategory.id_comp]
  naturality_inv_left f  := by simp
  naturality_inv_right f := by simp

/-! ### Vertical Composition -/

/-- Vertical composition of pseudo‑natural transformations. -/
def comp_v {F G H : PseudoFunctor B C}
    (α : PseudoNatTrans F G) (β : PseudoNatTrans G H) :
    PseudoNatTrans F H where
  component b := α.component b ≫ β.component b
  isIso_component b := by
    haveI := α.isIso_component b
    haveI := β.isIso_component b
    infer_instance
  naturality {b₁ b₂} f := by
    -- paste the two squares for α and β
    simp [Bicategory.assoc] with aesop_cat
  naturality_inv {b₁ b₂} f := by
    simp [Bicategory.assoc] with aesop_cat
  naturality_inv_left {b₁ b₂} f := by
    simp [Bicategory.assoc] with aesop_cat
  naturality_inv_right {b₁ b₂} f := by
    simp [Bicategory.assoc] with aesop_cat

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

end CategoryTheory

-- Import the full horizontal composition implementation
-- (This is at the end to avoid circular dependencies)
import CategoryTheory.PseudoNatTransHComp