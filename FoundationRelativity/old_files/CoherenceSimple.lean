/-
  Simplified coherence layer for testing - works with current mathlib
-/
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans

open CategoryTheory

universe u

/-- Simple functor type for interpretations -/
structure Interp where
  F : Type u → Type u

namespace Interp

/-- Composition of interpretations -/
def comp (Ψ Φ : Interp) : Interp := ⟨fun X => Ψ.F (Φ.F X)⟩

/-- Identity interpretation -/
def id : Interp := ⟨fun X => X⟩

/-- Associativity holds definitionally -/
lemma assoc (Θ Ψ Φ : Interp) : (Θ.comp Ψ).comp Φ = Θ.comp (Ψ.comp Φ) := rfl

/-- Left and right unit laws -/
lemma left_id (Φ : Interp) : id.comp Φ = Φ := rfl
lemma right_id (Φ : Interp) : Φ.comp id = Φ := rfl

end Interp

-- Test the definitions
example : Interp.id.comp Interp.id = Interp.id := rfl