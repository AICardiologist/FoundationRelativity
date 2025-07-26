import CategoryTheory.Found
import Mathlib.CategoryTheory.Types

open CategoryTheory

/-- **Stub**: contravariant functor that will collect gap-witness
    groupoids once `Found` is fully implemented (Sprint 41). -/
def CategoryTheory.GapFunctor : Foundation.{0,0}ᵒᵖ ⥤ Type := by
  -- TODO(S41): implement proper 2-functor once witness groupoids are formalised.
  sorry

/- Keeping this file separate means downstream imports already compile. -/