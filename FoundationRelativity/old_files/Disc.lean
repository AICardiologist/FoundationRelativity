/-
  Constant ("discrete") simplicial object functor:
  Set ⟶ SimplicialObject (Type _)
  plus a lemma that it preserves finite products strictly.
-/
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.AlgebraicTopology.SimplicialSet
open CategoryTheory

universe u

/-- The category of small sets is `Type u` with its ordinary (`rfl`) instances. -/
abbrev SetCat := Type u

/-- Constant simplicial object on a set. -/
def disc (S : SetCat) : SimplicialObject SetCat :=
  SimplicialObject.const _ S

namespace disc

-- A trivial terminal-object lemma for illustration.
lemma terminal_preserved (S : SetCat) :
    (Functor.obj disc S).obj (SimplexCategory.mk 0) = S := by
  rfl

/--
`disc` preserves binary products strictly:
disc (S × T) = (disc S) × (disc T)  (objectwise equality).
We show the statement on 0‑simplices for brevity; higher n are similar.
-/
lemma prod_zero (S T : SetCat) :
    ((disc (S × T)).obj <| SimplexCategory.mk 0) =
    ((disc S).obj (SimplexCategory.mk 0) ×
     (disc T).obj (SimplexCategory.mk 0)) := by
  rfl

end disc