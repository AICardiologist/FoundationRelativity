/-
  Papers/P3_2CatFramework/test/FT_UCT_Sanity.lean
  
  Sanity tests for the FT/UCT minimal infrastructure.
  Verifies that the FT axis placement and UCT calibration
  can be referenced correctly in Paper 3A.
-/

import Papers.P3_2CatFramework.P4_Meta.FT_UCT_MinimalSurface

namespace Papers.P4Meta.FTUCTTests

open Papers.P4Meta

/-! ## Test FT/UCT Axis References -/

/-- Check that FT and UCT formulas are distinct -/
example : FT ≠ UCT := by
  simp [FT, UCT, Formula.atom]
  norm_num

/-- Check that WLPO is different from both FT and UCT -/
example : WLPO ≠ FT ∧ WLPO ≠ UCT := by
  simp [WLPO, FT, UCT, Formula.atom]
  norm_num

/-- Verify UCT height certificate exists -/
example : ∃ (T0 : Theory), (uct_height1_cert T0).n = 1 := by
  use EmptyTheory
  rfl

/-- Test profile access -/
example : UCT_profile.ftHeight = 1 := rfl
example : UCT_profile.wlpoHeightIsOmega = true := rfl
example : UCT_profile.theAxiom = UCT := rfl

/-- Test that ftSteps produces FT at step 0 -/
example (T0 : Theory) : ftSteps T0 0 = FT := rfl

/-- Test that ftSteps produces filler at step 1 -/
example (T0 : Theory) : ftSteps T0 1 = Formula.atom 499 := rfl

/-- Verify orthogonality axioms are accessible -/
#check FT_not_implies_WLPO
#check WLPO_not_implies_FT

/-- Test empty theory definition -/
example (φ : Formula) : ¬(EmptyTheory.Provable φ) := by
  simp [EmptyTheory]

/-! ## Success Message -/

#eval IO.println "✅ FT/UCT minimal infrastructure sanity tests compile!"

end Papers.P4Meta.FTUCTTests