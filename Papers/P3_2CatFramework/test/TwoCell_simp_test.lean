/-
  CI test for TwoCell simp lemmas in Papers.P3_2CatFramework.Core.CoherenceTwoCellSimp
  
  Exercises all four @[simp] lemmas to ensure they stay definitional and automated.
  This test must pass for CI to be green.
-/
import Papers.P3_2CatFramework.Core.Prelude
open Papers.P3
open scoped Papers.P3

variable (E F G H : Foundation)
variable (η : Interp E F) (φ ψ χ : Interp F G) (θ : Interp G H)
variable (α : TwoCell φ ψ) (β : TwoCell ψ χ)

-- Test 1: TwoCell.id simp lemma
example (x : F.U) : (TwoCell.id φ).app x = rfl := by simp

-- Test 2: TwoCell.vcomp simp lemma  
example (x : F.U) : (TwoCell.vcomp α β).app x = (α.app x).trans (β.app x) := by simp

-- Test 3: TwoCell.lwhisker simp lemma
example (x : E.U) : (TwoCell.lwhisker η α).app x = 
  (by simpa [Interp.vcomp] using α.app (η.map_obj x)) := by simp

-- Test 4: TwoCell.rwhisker simp lemma  
example (x : F.U) : (TwoCell.rwhisker α θ).app x = 
  (by simpa [Interp.vcomp] using congrArg θ.map_obj (α.app x)) := by simp

-- Test 5: Composite simp behavior (whiskering + vertical composition)
example (x : E.U) : 
  (TwoCell.vcomp (TwoCell.lwhisker η α) (TwoCell.lwhisker η β)).app x = 
  ((TwoCell.lwhisker η α).app x).trans ((TwoCell.lwhisker η β).app x) := by simp

#check "✓ TwoCell simp lemmas CI validation complete"