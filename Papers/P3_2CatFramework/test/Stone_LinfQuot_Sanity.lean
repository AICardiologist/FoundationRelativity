/-
  Sanity: function quotient modulo a Boolean ideal
-/
import Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals

open Papers.P4Meta.StoneSupport
open Classical

noncomputable section

def 𝓘 : BoolIdeal := FinIdeal

-- Choose an `R` with decidable equality and zero:
variable {R : Type} [DecidableEq R] [Zero R]

-- Trivial sanity: reflexivity, and "support in 𝓘 ⇒ class = 0"
example (x : Linf R) :
    Quot.mk (linfEqMod (R := R) 𝓘) x
      = Quot.mk (linfEqMod (R := R) 𝓘) x := rfl

example (x : Linf R) (hx : supp (R := R) x ∈ 𝓘.mem) :
    Quot.mk (linfEqMod (R := R) 𝓘) x
      = Quot.mk (linfEqMod (R := R) 𝓘) (linfZero (R := R)) :=
  class_eq_zero_of_supp_mem (R := R) 𝓘 hx