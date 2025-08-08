/-
  Papers/P3_2CatFramework/test/Interp_simp_test.lean
  
  Micro test ensuring structure-level simp lemmas keep working when plumbing changes.
  This file validates that both explicit and scoped notation work correctly.
-/

import Papers.P3_2CatFramework.Core.Prelude

namespace Papers.P3.Test

open Papers.P3

section ExplicitNotation
  variable (F G H I : Foundation)
  variable (φ : Interp F G) (ψ : Interp G H) (χ : Interp H I)

  -- Test structure-level simp lemmas with explicit notation
  example : Interp.vcomp (Interp.vcomp φ ψ) χ = Interp.vcomp φ (Interp.vcomp ψ χ) := by simp
  example : Interp.vcomp (Interp.id F) φ = φ := by simp
  example : Interp.vcomp φ (Interp.id G) = φ := by simp
  
  -- Test complex chain simplification
  example : Interp.vcomp (Interp.id F) (Interp.vcomp φ (Interp.id G)) = φ := by simp
end ExplicitNotation

section ScopedNotation
  open scoped Papers.P3
  
  variable (F G H I : Foundation)
  variable (φ : Interp F G) (ψ : Interp G H) (χ : Interp H I)

  -- Test structure-level simp lemmas with scoped notation
  example : (φ ≫ᵢ ψ) ≫ᵢ χ = φ ≫ᵢ (ψ ≫ᵢ χ) := by simp
  example : (𝟙ᵢ F) ≫ᵢ φ = φ := by simp
  example : φ ≫ᵢ (𝟙ᵢ G) = φ := by simp
  
  -- Test complex chain simplification with notation
  example : (𝟙ᵢ F) ≫ᵢ φ ≫ᵢ (𝟙ᵢ G) = φ := by simp
end ScopedNotation

-- Integration test: Both notations should coexist
section MixedNotation
  open scoped Papers.P3
  
  variable (F G H : Foundation)
  variable (φ : Interp F G) (ψ : Interp G H)

  -- Mixed notation should work seamlessly
  example : φ ≫ᵢ ψ = Interp.vcomp φ ψ := rfl
  example : (𝟙ᵢ F) = Interp.id F := rfl
end MixedNotation

end Papers.P3.Test

#check "✓ Interp simp lemmas validation complete"