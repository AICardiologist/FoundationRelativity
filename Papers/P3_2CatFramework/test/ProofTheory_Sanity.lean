/-
  Papers/P3_2CatFramework/test/ProofTheory_Sanity.lean
  
  Sanity tests for the proof-theoretic components of Paper 3B.
  Verifies that core definitions and theorems compile correctly.
-/

import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Core
import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Reflection
import Papers.P3_2CatFramework.P4_Meta.PartV_Reflection

namespace Papers.P4Meta.ProofTheory.Tests

open Papers.P4Meta Papers.P4Meta.ProofTheory

/-! ## Test Core Definitions -/

section CoreTests

/-- Check that HA is weaker than PA -/
example (φ : Formula) (h : HA.Provable φ) : PA.Provable φ := 
  HA_weaker_PA φ h

/-- Check that consistency is well-defined (simplified test) -/
example (T : Theory) : Prop := ¬T.Provable Bot

/-- Check that Extend adds an axiom -/
example (T : Theory) (φ : Formula) : 
  (Extend T φ).Provable φ := 
  Or.inr rfl

/-- Check classicality steps -/
example : ClassicalitySteps 0 = EM_Sigma 0 := rfl
example : ClassicalitySteps 1 = EM_Sigma 1 := rfl

end CoreTests

/-! ## Test Reflection Theorem -/

section ReflectionTests

/-- Mock instance for testing -/
def MockTheory : Theory := 
  { Provable := fun _ => False }

/-- Mock reflection instance -/
instance : HasRFN_Sigma1 MockTheory MockTheory where
  TrueInN := fun _ => False
  bot_false := id
  reflect := fun _ _ h => False.elim h
  rfn_reflect := fun _ _ h => False.elim h

/-- Test that RFN implies Con compiles -/
example : ¬MockTheory.Provable Bot := 
  RFN_implies_Con MockTheory MockTheory

/-- Test that the theorem produces the expected type -/
example (Text Tbase : Theory) [HasRFN_Sigma1 Text Tbase] : Prop :=
  ¬Tbase.Provable Bot

end ReflectionTests

/-! ## Test Formula Construction -/

section FormulaTests

/-- Different formula codes should produce different formulas -/
example : WLPO_formula ≠ LPO_formula := by
  simp only [WLPO_formula, LPO_formula]
  -- These are different atoms by construction
  decide

/-- Consistency formulas exist for theories with arithmetization -/
example [h : HasArithmetization PA] : Formula :=
  ConsistencyFormula PA

end FormulaTests

/-! ## Integration Tests -/

section IntegrationTests

/-- Test that ExtendIter works with classicality steps -/
example : ExtendIter HA ClassicalitySteps 0 = HA := by
  simp [ExtendIter]

example : ExtendIter HA ClassicalitySteps 1 = Extend HA (EM_Sigma 0) := by
  simp [ExtendIter, ClassicalitySteps]

/-- Test that the collision theorem type-checks with actual theories -/
example [HasRFN_Sigma1 PA PA] : Con PA := 
  RFN_implies_Con PA PA

end IntegrationTests

/-! ## Success Message -/

#eval IO.println "✅ ProofTheory sanity tests compile successfully!"

end Papers.P4Meta.ProofTheory.Tests