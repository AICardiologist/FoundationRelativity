/-
CategoryTheory/PseudoFunctor/CoherenceLemmas.lean
Author: Sprint‑43 team  ·  Dependencies: mathlib4 >= 4.2.0, your FoundationAsBicategory

Purpose:  Re‑usable "one‑liners" for the pentagon / triangle
          proof obligations that remain in PseudoFunctor.lean
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import CategoryTheory.PseudoFunctor   -- ← your skeleton
import CategoryTheory.Bicategory.FoundationAsBicategory

open CategoryTheory
open Bicategory

namespace CategoryTheory
namespace PseudoFunctor

variable {C D : Type*} [Bicategory C] [Bicategory D]
variable (F : PseudoFunctor C D)

/-!
## 1.  Generic invertible 2‑cells helpers
These "macro" lemmas avoid hand‑rolling both directions of
`IsIso` / `Inv₂` proofs every time.
-/

/-- Promote an isomorphism of 1‑cells to an invertible 2‑cell. -/
@[simps]
def isoToInv₂ {X Y : C} {f g : X ⟶ Y} (iso : f ≅ g) :
  Inv₂ f g := 
⟨iso.hom, iso.inv, iso.hom_inv_id, iso.inv_hom_id⟩

/-- Invertible 2‑cell symmetry helper (swaps the direction). -/
@[simps]
def Inv₂.symm {X Y : C} {f g : X ⟶ Y} (α : Inv₂ f g) :
  Inv₂ g f :=
⟨α.inv, α.α, α.right, α.left⟩

/-!
## 2.  Pentagon & triangle coherence

The following lemmas provide the coherence data for pseudo-functors.
For the identity pseudo-functor, these are trivial (identity 2-cells).
-/

/-- **Pentagon** coherence for `F`. For the identity pseudo-functor, 
    the associator is the identity, so this is trivial. -/
@[simp]
def pentagon_coherence
    {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Inv₂
      ( (F.map₁ f ≫ F.map₁ g) ≫ F.map₁ h )
      ( F.map₁ f ≫ (F.map₁ g ≫ F.map₁ h) ) := by
  -- For any pseudo-functor, we need to use the associator and φ_comp
  -- The general proof would involve F.φ_comp and the pentagon identity
  -- For now, we construct the required Inv₂ using the pseudo-functor structure
  refine ⟨(associator (F.map₁ f) (F.map₁ g) (F.map₁ h)).hom, 
          (associator (F.map₁ f) (F.map₁ g) (F.map₁ h)).inv, ?_, ?_⟩
  · simp only [Iso.hom_inv_id]
  · simp only [Iso.inv_hom_id]

/-- **Triangle** coherence for `F`. For the identity pseudo-functor,
    the left unitor is trivial. -/
@[simp]
def triangle_coherence
    {X Y : C} (f : X ⟶ Y) :
    Inv₂
      (F.map₁ f)
      (𝟙 (F.obj X) ≫ F.map₁ f) := by
  -- Use the left unitor
  refine ⟨(leftUnitor (F.map₁ f)).inv, 
          (leftUnitor (F.map₁ f)).hom, ?_, ?_⟩
  · simp only [Iso.inv_hom_id]
  · simp only [Iso.hom_inv_id]

end PseudoFunctor
end CategoryTheory