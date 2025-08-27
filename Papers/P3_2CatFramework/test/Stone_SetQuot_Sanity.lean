/-
  Sanity: Powerset quotient modulo a Boolean ideal
-/
import Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals

open Papers.P4Meta.StoneSupport
open Set

noncomputable section

-- Use the finite-sets ideal as a concrete example
def 𝓘 : BoolIdeal := FinIdeal

example (A : Set ℕ) : Quot.mk (sdiffSetoid 𝓘) A = Quot.mk (sdiffSetoid 𝓘) A := rfl

-- If A and B differ by a finite symmetric-difference, they are equal in the quotient.
example (A B : Set ℕ) (hfin : (A △ B).Finite) :
    Quot.mk (sdiffSetoid 𝓘) A = Quot.mk (sdiffSetoid 𝓘) B :=
  quot_mk_eq_of_rel 𝓘 (A := A) (B := B) (by simpa using hfin)