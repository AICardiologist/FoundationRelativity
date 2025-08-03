import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Foundation Category Theory Infrastructure

Basic Foundation category definitions and structures. This module provides
the categorical foundation for the Foundation-Relativity project.

## Main Definitions

- Core Foundation category structure
- Category theory infrastructure for foundation-relative mathematics

## Implementation Notes

This module establishes the categorical foundation that underlies the
bicategorical and pseudo-functor infrastructure developed in later sprints.
-/

namespace CategoryTheory.Found

open CategoryTheory

/-- A foundation with universe category. -/
structure Foundation where
  Univ    : Type*
  UnivCat : Category Univ

attribute [instance] Foundation.UnivCat

/-- Interpretations between foundations. -/
structure Interp (A B : Foundation) where
  toFun : CategoryTheory.Functor A.Univ B.Univ
  -- TODO(S41): add preservesLimits, preservesColimits, idOnSigma0

namespace Interp

/-- Identity interpretation. -/
def id (A : Foundation) : Interp A A :=
  { toFun := CategoryTheory.Functor.id _ }

/-- Composition of interpretations. -/
def comp {A B C : Foundation} (f : Interp A B) (g : Interp B C) : Interp A C :=
  { toFun := CategoryTheory.Functor.comp f.toFun g.toFun }

end Interp

instance : Category Foundation where
  Hom := Interp
  id := Interp.id
  comp := Interp.comp
  id_comp := by
    intro A B f
    cases f
    rfl
  comp_id := by
    intro A B f
    cases f
    rfl
  assoc := by
    intro A B C D f g h
    cases f; cases g; cases h
    rfl

/-! ### Standard Foundation Instances -/

/-- Trivial category instance for Type (used as placeholder) -/
instance : Category.{0} Unit where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

/-- Bishop's constructive mathematics foundation (BISH) -/
def Foundation.bish : Foundation where
  Univ := Unit
  UnivCat := inferInstance

/-- Zermelo-Fraenkel with Choice foundation (ZFC) -/
def Foundation.zfc : Foundation where
  Univ := Unit
  UnivCat := inferInstance

/-- Homotopy Type Theory foundation (HoTT) -/
def Foundation.hott : Foundation where
  Univ := Unit
  UnivCat := inferInstance

end CategoryTheory.Found