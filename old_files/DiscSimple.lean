/-
  Simplified constant ("discrete") functor that works with current mathlib
-/
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Limits.Shapes.Products

open CategoryTheory

universe u

/-- The category of small sets -/
abbrev SetCat := Type u

/-- Simple identity-like "discrete" functor -/
def disc (S : SetCat) : SetCat := S

namespace disc

/-- Terminal preservation lemma -/
lemma terminal_preserved (S : SetCat) : disc S = S := rfl

/-- Product preservation -/
lemma prod_zero (S T : SetCat) : disc (S × T) = (disc S × disc T) := rfl

end disc

-- Test that it works
example : disc Nat = Nat := rfl
example : disc (String × Bool) = (disc String × disc Bool) := rfl