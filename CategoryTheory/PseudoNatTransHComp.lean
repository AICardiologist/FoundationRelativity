import CategoryTheory.PseudoNatTrans
import CategoryTheory.Compat.PseudoFunctorExt

open Bicategory CategoryTheory

universe u₁ u₂ u₃
variable {B : Type u₁} {C : Type u₂} {D : Type u₃}
variable [Bicategory B] [Bicategory C] [Bicategory D]
variable {F F' : PseudoFunctor B C} {G G' : PseudoFunctor C D}

/-- Horizontal composition of pseudo‑natural transformations. -/
@[simp, reducible]
def PseudoNatTrans.hcomp (α : PseudoNatTrans F F')
                         (β : PseudoNatTrans G G') :
    PseudoNatTrans (F ⋙ G) (F' ⋙ G') where

  component X := G.map₁ (α.component X) ≫ β.component (F'.obj X)

  isIso_component X := by
    haveI := α.isIso_component X
    haveI : IsIso (G.map₁ (α.component X)) := G.map₁_isIso _
    haveI := β.isIso_component (F'.obj X)
    infer_instance

  naturality {X Y} f := by
    simp [Bicategory.assoc] with aesop_cat

  naturality_inv {X Y} f := by
    simp [Bicategory.assoc] with aesop_cat

  naturality_inv_left {X Y} f := by
    simp [Bicategory.assoc] with aesop_cat

  naturality_inv_right {X Y} f := by
    simp [Bicategory.assoc] with aesop_cat

infixl:80 " ◆h " => PseudoNatTrans.hcomp

@[simp]
lemma PseudoNatTrans.hcomp_component
    (α : PseudoNatTrans F F') (β : PseudoNatTrans G G') (X : B) :
    (α ◆h β).component X =
      G.map₁ (α.component X) ≫ β.component (F'.obj X) := rfl