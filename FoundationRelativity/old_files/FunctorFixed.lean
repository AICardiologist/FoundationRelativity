/-
  Gap2.Functor - Fixed version with working imports
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import Gap2.Witness

open CategoryTheory

/-- Using the Foundation and GapFunctor from Witness -/
open Foundation GapFunctor

/-- Interpretations between foundations -/
inductive Interp : Foundation → Foundation → Type
  | id_zfc  : Interp zfc  zfc
  | id_bish : Interp bish bish
  | incl    : Interp zfc  bish   -- forgetful direction

namespace GapFunctor

/-- Object assignment for the Gap functor -/
def Gap2_obj (F : Foundation) : Type* := GapGroupoid F

/-- Action on 1-cells (contravariant) -/
def Gap2_map {F F' : Foundation} (φ : Interp F F') : 
    GapGroupoid F' → GapGroupoid F :=
  match φ with
  | .id_zfc  => id
  | .id_bish => id  
  | .incl    => fun x => nomatch x.down  -- empty domain

-- Functoriality properties
lemma Gap2_map_id (F : Foundation) : 
    Gap2_map (show Interp F F from match F with | .zfc => .id_zfc | .bish => .id_bish) = id := by
  cases F <;> rfl

lemma Gap2_map_comp {F₁ F₂ F₃ : Foundation} (φ : Interp F₂ F₃) (ψ : Interp F₁ F₂) :
    Gap2_map (match φ, ψ with 
              | .id_zfc, .id_zfc => .id_zfc
              | .id_bish, .id_bish => .id_bish  
              | .incl, .id_bish => .incl
              | .id_zfc, .incl => .incl) = 
    Gap2_map ψ ∘ Gap2_map φ := by
  cases φ <;> cases ψ <;> rfl

end GapFunctor