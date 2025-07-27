/-!
# Bicategory Helper Utilities

A minimal helper module that wraps common utilities for working with Lean's bicategory API.
Everything here is pure utility with no project-specific names, suitable for eventual
upstreaming to mathlib.

## Main Definitions

- `Inv₂`: Type alias for invertible 2-cells
- Utility functions for bicategorical reasoning and 2-cell manipulation

## Design Notes

This module provides reusable utilities that simplify bicategorical proofs and
2-cell operations throughout the Foundation-Relativity project.
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Bicategory.Basic

namespace CategoryTheory

open Bicategory

/-- A convenient record for an *invertible 2‑cell*.
    Lean's bundled `IsIso` works but is verbose; most of our proofs only need
    the data – not the proofs – so we re‑export the essential fields. -/
structure Inv₂ {C : Type*} [Bicategory C]
  {A B : C} (f g : A ⟶ B) where
  α  : f ⟶ g
  inv : g ⟶ f
  left  : α ≫ inv = 𝟙 f := by aesop_cat
  right : inv ≫ α = 𝟙 g := by aesop_cat

attribute [simp] Inv₂.left Inv₂.right

/--  Any `IsIso` gives an `Inv₂`.  Handy when importing mathlib lemmas. -/
noncomputable def IsIso.toInv₂ {C : Type*} [Bicategory C]
    {A B : C} {f g : A ⟶ B} (α : f ⟶ g) [IsIso α] : Inv₂ f g :=
⟨α, inv α, by simp, by simp⟩

/--  Vertical composition of invertible 2‑cells is invertible. -/
def Inv₂.vcomp {C : Type*} [Bicategory C] {A B : C} {f g h : A ⟶ B}
    (α : Inv₂ f g) (β : Inv₂ g h) : Inv₂ f h where
  α := α.α ≫ β.α
  inv := β.inv ≫ α.inv
  left := by
    rw [Category.assoc, ← Category.assoc β.α, β.left, Category.id_comp, α.left]
  right := by
    rw [Category.assoc, ← Category.assoc α.inv, α.right, Category.id_comp, β.right]

end CategoryTheory