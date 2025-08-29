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

section BasicTests

/-- Check that FT and UCT formulas are distinct -/
example : FT ≠ UCT := by
  intro h
  simp only [FT, UCT] at h
  -- h : Formula.atom 400 = Formula.atom 401
  cases h

/-- Check that WLPO is different from both FT and UCT -/
example : WLPO ≠ FT ∧ WLPO ≠ UCT := by
  constructor
  · intro h
    simp only [WLPO, FT] at h
    -- h : Formula.atom 311 = Formula.atom 400
    cases h
  · intro h  
    simp only [WLPO, UCT] at h
    -- h : Formula.atom 311 = Formula.atom 401
    cases h

end BasicTests

section ProfileTests

/-- Test profile access -/
example : UCT_profile.ftHeight = 1 := rfl
example : UCT_profile.wlpoHeightIsOmega = true := rfl
example : UCT_profile.theAxiom = UCT := rfl

/-- Test that ftSteps produces FT at step 0 -/
example (T0 : Theory) : ftSteps T0 0 = FT := rfl

/-- Test that ftSteps produces filler at step 1 -/
example (T0 : Theory) : ftSteps T0 1 = Formula.atom 499 := rfl

end ProfileTests

section AxiomTests

/-- Test empty theory definition -/
example (φ : Formula) : ¬(EmptyTheory.Provable φ) := by
  simp only [EmptyTheory]
  intro h
  exact h

/-- Verify orthogonality axioms compile -/
example : ¬((Extend EmptyTheory FT).Provable WLPO) := FT_not_implies_WLPO
example : ¬((Extend EmptyTheory WLPO).Provable FT) := WLPO_not_implies_FT

end AxiomTests

/-! ## Success Message -/

#eval IO.println "✅ FT/UCT minimal infrastructure sanity tests compile!"

end Papers.P4Meta.FTUCTTests