/-
  Sanity: Idempotents modulo the ideal
-/
import Papers.P3_2CatFramework.P4_Meta.StoneWindow_SupportIdeals

open Papers.P4Meta.StoneSupport
open Classical

noncomputable section

def 𝓘 : BoolIdeal := FinIdeal

-- Example: chi is idempotent modulo any ideal
example (A : Set ℕ) : IsIdemMod (R := ℤ) 𝓘 (chi A) := chi_IsIdemMod 𝓘 A

-- Example: The map from PowQuot to IdemClass is well-defined
example : PowQuot 𝓘 → IdemClass (R := ℤ) 𝓘 := PhiIdemMod 𝓘

-- Example: Two sets with finite symmetric difference map to the same idempotent class
example (A B : Set ℕ) (h : (A △ B).Finite) :
    PhiIdemMod (R := ℤ) 𝓘 (Quot.mk _ A) = PhiIdemMod (R := ℤ) 𝓘 (Quot.mk _ B) := by
  -- This follows from the well-definedness of PhiIdemMod
  -- Since A and B have finite symmetric difference, they are equivalent under sdiffSetoid 𝓘
  -- and thus map to the same element under PhiIdemMod
  have : Quot.mk (sdiffSetoid 𝓘) A = Quot.mk (sdiffSetoid 𝓘) B := by
    apply Quot.sound
    simpa using h
  rw [this]