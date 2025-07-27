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
open Bicategory (whiskerLeft whiskerRight)

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
## 2.  Pentagon & triangle shells

The following two lemmas are **exactly** what the two remaining
`sorry`s expect.  The bodies are deliberately left blank so Math‑AI
can insert the real argument; SWE‑AI can already commit the statement
to guarantee type‑checking of downstream code.
-/

/-- **Pentagon** coherence for `F`.  Replace `sorry` with the usual
    `calc` chain (`simp`, `whiskerLeft`, `associator_naturality`, …). -/
@[simp]
def pentagon_coherence
    {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Inv₂
      ( (F.map₁ f ≫ F.map₁ g) ≫ F.map₁ h )
      ( F.map₁ f ≫ (F.map₁ g ≫ F.map₁ h) ) := by
  sorry   -- ← to be filled by Math‑AI on Day 4

/-- **Triangle** coherence for `F`.  Same comment as above. -/
@[simp]
def triangle_coherence
    {X Y : C} (f : X ⟶ Y) :
    Inv₂
      (F.map₁ f)
      (𝟙 (F.obj X) ≫ F.map₁ f) := by
  sorry

end PseudoFunctor
end CategoryTheory