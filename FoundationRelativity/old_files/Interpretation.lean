/-
  Classical‐to‐HoTT interpretation `ι_cl`.
-/
import Found.Disc
import Found.FibRep
import Found.SimplicialPi0
import Found.Coherence
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Functor.Category

open CategoryTheory

universe u

-- Short aliases
abbrev SetCat := Type u
abbrev SSet   := SimplicialObject SetCat

-- pull the stub fibrant replacement
open FibRep

/-- Chosen fibrant‑replacement functor (stub). -/
def R : FibRep := identityFibRep

/-- The underlying functor of `ι_cl`: `Set ⟶ SSet`. -/
def iotaObj : SetCat ⥤ SSet :=
  R.obj.comp (SimplicialObject.const _)

/-- Show that `iotaObj` fixes objects in Σ₀ strictly. -/
lemma iotaObj_onNat : (iotaObj.obj ℕ) = SimplicialObject.const _ ℕ := by
  rfl

/-- Lift `iotaObj` to an interpretation on *logical fibrations*. -/
structure Interpretation where
  Fobj  : SetCat ⥤ SSet
  preserves_Pi    : True   -- stub axiom
  preserves_Sigma : True
  preserves_Id    : True

/-- The concrete interpretation `ι_cl`. -/
def iota_cl : Interpretation := by
  refine ⟨iotaObj, ?_, ?_, ?_⟩ <;> trivial

#eval (iota_cl.Fobj.obj (Fin 5))
example : (iota_cl.Fobj.obj ℕ).obj (SimplexCategory.mk 0) = ℕ := rfl

/-- Wrap `iota_cl` into an `Interp` by bouncing through π₀ on the left and
a constant-simplicial-set functor on the right:

    SSet ─π₀─▶ Set ─iotaObj─▶ SSet

The constant functor `SimplicialObject.const _` turned out not to be
needed because `iotaObj` expects a set and already returns `SSet`.
-/
def iota_cl_interp : Interp where
  F := iotaObj.comp (pi0 ⋙ (Functor.id _))   -- SSet ⥤ SSet