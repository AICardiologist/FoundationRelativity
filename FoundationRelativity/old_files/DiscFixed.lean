/-
  Constant ("discrete") simplicial object functor - Fixed version
-/
import Mathlib.AlgebraicTopology.SimplicialObject
import Mathlib.CategoryTheory.Limits.Shapes.Products

open CategoryTheory

universe u

/-- The category of small sets -/
abbrev SetCat := Type u

/-- Constant simplicial object on a set -/
def disc (S : SetCat) : SimplicialObject SetCat :=
  (SimplicialObject.const _).obj S

namespace disc

-- Basic properties
lemma disc_const (S : SetCat) : disc S = (SimplicialObject.const _).obj S := rfl

/-- Product preservation -/
lemma prod_preservation (S T : SetCat) : 
    disc (S × T) = (SimplicialObject.const _).obj (S × T) := rfl

end disc

-- Test that the definitions work
example (S : SetCat) : disc S = (SimplicialObject.const _).obj S := rfl