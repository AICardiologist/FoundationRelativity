/-
  Sanity: the set→function quotient lift is well-defined and behaves as expected.
-/
import Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals

open Papers.P4Meta.StoneSupport
open Classical

noncomputable section

def 𝓘 : BoolIdeal := FinIdeal

-- Use ℤ for a concrete codomain (DecidableEq, Zero, One available).
example : PowQuot 𝓘 → LinfQuot 𝓘 ℤ := PhiSetToLinfQuot (R := ℤ) 𝓘

example (A B : Set ℕ) (h : (A △ B) ∈ 𝓘.mem) :
  PhiSetToLinfQuot (R := ℤ) 𝓘 (Quot.mk _ A)
  =
  PhiSetToLinfQuot (R := ℤ) 𝓘 (Quot.mk _ B) := by
  -- follows from the well-definedness proof of PhiSetToLinfQuot
  change
    Quot.mk (linfEqMod (R := ℤ) 𝓘) (chi (R := ℤ) A)
    =
    Quot.mk (linfEqMod (R := ℤ) 𝓘) (chi (R := ℤ) B)
  -- `Quot.sound` with downward closure of `diffSet_chi_subset_sdiff`.
  apply Quot.sound
  exact 𝓘.downward (diffSet_chi_subset_sdiff (R := ℤ) A B) h