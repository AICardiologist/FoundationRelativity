/-
Unified witness API for pathology functors.
Replaces hand-rolled Empty/PUnit patterns with type-class abstraction.
-/

import Found.InterpCore
import Mathlib.CategoryTheory.Limits.Shapes.Types

open CategoryTheory Foundation

/-- Type class for pathology witnesses in each foundation -/
class PathologyWitness (pathology : Type) where
  witness : Foundation → Type
  witness_bish_empty : IsEmpty (witness bish)
  witness_zfc_inhabited : Inhabited (witness zfc)

/-- Generic witness transport along interpretations -/
def transportWitness {pathology : Type} [PathologyWitness pathology] :
  ∀ {F G : Foundation}, (F ⟶ G) → PathologyWitness.witness pathology F → PathologyWitness.witness pathology G
  | bish, zfc, _ => fun w => (PathologyWitness.witness_bish_empty pathology).elim w
  | F, _, _ => fun w => by
    cases F <;> exact w  -- identity morphisms

-- TODO: Prove transport preserves functor laws
-- TODO: Add convenience notation for witness access