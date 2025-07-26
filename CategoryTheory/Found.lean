import Mathlib.CategoryTheory.Category.Basic

-- Sprint 40 Day 3: Basic Foundation category skeleton
-- TODO(S41): Add full 2-categorical structure

namespace CategoryTheory.Found

open CategoryTheory

/-- A foundation with universe category. -/
structure Foundation where
  Univ    : Type
  UnivCat : Category Univ

attribute [instance] Foundation.UnivCat

/-- Interpretations between foundations. -/
structure Interp (A B : Foundation) where
  toFun : A.Univ ⥤ B.Univ

namespace Interp

/-- Identity interpretation. -/
def id (A : Foundation) : Interp A A :=
  ⟨𝟭 A.Univ⟩

/-- Composition of interpretations. -/
def comp {A B C : Foundation} (f : Interp A B) (g : Interp B C) : Interp A C :=
  ⟨f.toFun ⋙ g.toFun⟩

end Interp

instance : Category Foundation where
  Hom := Interp
  id := Interp.id
  comp := Interp.comp
  id_comp := by
    intro A B f
    -- TODO(S41): Prove category laws
    sorry
  comp_id := by
    intro A B f
    -- TODO(S41): Prove category laws
    sorry  
  assoc := by
    intro A B C D f g h
    -- TODO(S41): Prove category laws
    sorry

end CategoryTheory.Found