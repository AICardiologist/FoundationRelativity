/-
  Simplified π₀ functor for testing
-/
import Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory

universe u

-- Simplified types  
abbrev SetCat : Type (u+1) := Type u
abbrev SSet := SetCat  -- Simplified: no simplicial structure

-- Simple π₀ functor (identity in this simplified version)
def pi0 : SSet → SetCat := id

-- Test properties
example (X : SSet) : pi0 X = X := rfl

-- Functoriality (trivial since pi0 = id)
lemma pi0_functorial (f : α → β) : pi0 β = β := rfl