/-
  Papers/P3_2CatFramework/P4_Meta/NormalForm_test.lean
  
  Comprehensive tests for step program normal forms and canonicalization.
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_NormalForm
import Papers.P3_2CatFramework.P4_Meta.PartIV_Limit

namespace Papers.P4Meta.NormalFormTests

open Papers.P4Meta

-- Test step functions for composition
def stepA : Nat → Formula := Formula.atom ∘ (· + 100)
def stepB : Nat → Formula := Formula.atom ∘ (· + 200)  
def stepC : Nat → Formula := Formula.atom ∘ (· + 300)
def stepD : Nat → Formula := Formula.atom ∘ (· + 400)

section BasicNormalForms
  -- Test basic normal form construction
  def nf1 := StepNF.base stepA
  def nf2 := StepNF.concat 3 stepA (StepNF.base stepB)
  def nf3 := concat3NF 2 3 stepA stepB stepC
  def nf4 := concat4NF 1 2 3 stepA stepB stepC stepD
  
  -- Verify conversion back to steps
  #eval (nf1.toSteps 0)  -- atom 100
  #eval (nf2.toSteps 2)  -- atom 102 (from A)
  #eval (nf2.toSteps 3)  -- atom 200 (from B at index 0)
  #eval (nf3.toSteps 5)  -- atom 300 (from C)
  
  -- Test prefix lengths
  #eval nf1.prefixLen  -- 0
  #eval nf2.prefixLen  -- 3
  #eval nf3.prefixLen  -- 5
  #eval nf4.prefixLen  -- 6
end BasicNormalForms

section EquivalenceTests
  -- Test that different representations are equivalent
  def step_direct := concatSteps 2 stepA (concatSteps 3 stepB stepC)
  def step_nf := (concat3NF 2 3 stepA stepB stepC).toSteps
  
  example : ∀ i, step_direct i = step_nf i := by
    intro i
    rfl  -- They're definitionally equal
  
  -- Test normal form equivalence
  def nf_a := concat3NF 2 3 stepA stepB stepC
  def nf_b := StepNF.concat 2 stepA (StepNF.concat 3 stepB (StepNF.base stepC))
  
  example : StepNF.equiv nf_a nf_b := by
    intro i
    rfl  -- Also definitionally equal
  
  -- Verify equivalence properties
  example : StepNF.equiv nf_a nf_a := StepNF.equiv_refl nf_a
  example : StepNF.equiv nf_a nf_b → StepNF.equiv nf_b nf_a := 
    fun h => StepNF.equiv_symm h
end EquivalenceTests

section SimplificationTests
  -- Test that @[simp] lemmas work correctly
  
  -- concat at 0 simplifies to identity
  example : concatSteps 0 stepA stepB = stepB := by 
    ext i
    simp [concatSteps]
  
  -- Triple concat equals normal form
  example : 
    concatSteps 2 stepA (concatSteps 3 stepB stepC) = 
    (concat3NF 2 3 stepA stepB stepC).toSteps := by 
    simp only [concat3NF, StepNF.toSteps]
  
  -- Associativity normalization
  example :
    concatSteps 2 stepA (concatSteps 3 stepB (StepNF.base stepC).toSteps) =
    (StepNF.concat 2 stepA (StepNF.concat 3 stepB (StepNF.base stepC))).toSteps := by
    rfl  -- Definitionally equal
end SimplificationTests

section TheoryExtensionTests
  -- Test that normal forms work with ExtendIter
  
  def testTheory : Theory := Paper3Theory
  def testNF := concat3NF 2 3 stepA stepB stepC
  
  -- Verify theory extension with normal form
  example : 
    ExtendIter testTheory testNF.toSteps 5 = 
    ExtendIter testTheory (concatSteps 2 stepA (concatSteps 3 stepB stepC)) 5 := 
    rfl  -- testNF.toSteps is definitionally equal
  
  -- Test lifting to ω with normal forms
  def testCert1 : HeightCertificate testTheory stepA (Formula.atom 100) :=
  { n := 1
  , upper := by simp [ExtendIter_succ, ExtendIter_zero, stepA, Extend]
  , note := "Test cert for stepA"
  }
  
  def testCert2 : HeightCertificate (ExtendIter testTheory stepA 2) stepB (Formula.atom 200) :=
  { n := 1
  , upper := by simp [ExtendIter_succ, ExtendIter_zero, stepB, Extend]
  , note := "Test cert for stepB"
  }
  
  -- Compose certificates using normal form
  def composed_nf := StepNF.concat 2 stepA (StepNF.base stepB)
  
  example :
    (Extendω testTheory composed_nf.toSteps).Provable (Formula.atom 100) := by
    apply omega_of_prefixCert (A := stepA) (B := stepB) 2 testCert1
    decide
    
  example :
    (Extendω testTheory composed_nf.toSteps).Provable (Formula.atom 200) := by
    apply omega_of_tailCert (A := stepA) (B := stepB) 2 testCert2
end TheoryExtensionTests

section PrefixTailOperations
  -- Test prefix/tail extraction
  def testNF2 := concat3NF 3 2 stepA stepB stepC
  
  -- Extract prefix
  def prefix3 := testNF2.takePrefix 3
  
  example : ∀ i < 3, prefix3 i = stepA i := by
    intro i hi
    simp only [prefix3, StepNF.takePrefix, testNF2, concat3NF, StepNF.toSteps, concatSteps, hi, if_true]
  
  -- Extract tail  
  def tail3 := testNF2.dropPrefix 3
  
  example : tail3 0 = stepB 0 := by
    simp only [tail3, StepNF.dropPrefix, testNF2, concat3NF, StepNF.toSteps, concatSteps]
    decide
  
  -- Verify reconstruction
  example : concatSteps 3 prefix3 tail3 = testNF2.toSteps := 
    take_drop_eq testNF2 3
end PrefixTailOperations

section ComplexCompositions
  -- Test deeply nested compositions
  
  def complex1 := 
    concatSteps 1 stepA $
    concatSteps 2 stepB $
    concatSteps 3 stepC stepD
  
  def complex1_nf := 
    StepNF.concat 1 stepA $
    StepNF.concat 2 stepB $
    StepNF.concat 3 stepC $
    StepNF.base stepD
  
  example : ∀ i, complex1 i = complex1_nf.toSteps i := by
    intro i
    rfl  -- Definitionally equal
  
  -- Test evaluation at specific indices
  #eval complex1 0   -- atom 100 (A)
  #eval complex1 1   -- atom 200 (B at 0)
  #eval complex1 3   -- atom 300 (C at 0)
  #eval complex1 6   -- atom 400 (D at 0)
  
  -- Five-level composition
  def five_level := 
    StepNF.concat 1 stepA $
    StepNF.concat 1 stepB $
    StepNF.concat 1 stepC $
    StepNF.concat 1 stepD $
    StepNF.base stepA  -- Loop back to A
  
  #eval five_level.prefixLen  -- 4
  #eval five_level.toSteps 0  -- atom 100
  #eval five_level.toSteps 4  -- atom 100 (back to A)
end ComplexCompositions

section TransportTests
  -- Test transporting certificates between equivalent normal forms
  
  def nf_orig := concat3NF 2 3 stepA stepB stepC
  def nf_alt := StepNF.concat 2 stepA (StepNF.concat 3 stepB (StepNF.base stepC))
  
  -- Create a certificate on the original
  def cert_orig : HeightCertificate Paper3Theory nf_orig.toSteps (Formula.atom 100) :=
  { n := 1
  , upper := by 
      simp only [ExtendIter_succ, ExtendIter_zero, nf_orig, concat3NF, StepNF.toSteps, concatSteps, Extend]
      -- At stage 1, we extend with stepA 0 = atom 100
      simp only [stepA]
      exact Extend_Proves
  , note := "Original cert"
  }
  
  -- Transport to alternative form (they're definitionally equal)
  def cert_alt := cert_orig.transport (A := nf_orig.toSteps) (B := nf_alt.toSteps)
    (fun _ _ => rfl)
  
  example : cert_alt.n = cert_orig.n := rfl
end TransportTests

#eval "Normal form tests completed successfully!"

end Papers.P4Meta.NormalFormTests