import Mathlib.CategoryTheory.Simplicial
import Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory

universe u

abbrev SetCat : Type (u+1) := Type u
abbrev SSet   := SimplicialObject SetCat

/--
π₀ functor: take 0-simplices of a simplicial set.
This is enough to embed `Set ⥤ SSet` compositions back into `SSet ⥤ SSet`
via constant simplicial sets.
-- Reflects 0-truncation; preserves on-the-nose equalities.
-/
def pi0 : SSet ⥤ SetCat where
  obj X := X.obj (SimplexCategory.mk 0)
  map {X Y} f := f.app (SimplexCategory.mk 0)
  map_id := by
    intro X; rfl
  map_comp := by
    intro X Y Z f g; rfl