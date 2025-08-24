/-
  Papers/P4_Meta/Meta_Smoke_test.lean
  
  Smoke test verifying the meta-theoretic framework compiles.
-/
import Papers.P3_2CatFramework.P4_Meta

namespace Papers.P4Meta.Tests

open Papers.P4Meta

-- Test basic formula construction
def testFormula : Formula := 
  Formula.atom 1

-- Test theory extension
def extendedTheory : Theory :=
  Extend ClassicalLogic testFormula

-- Verify extension works
example : extendedTheory.Provable testFormula :=
  Extend_Proves

-- Test provenance assignment
def checkProvenance : Option Provenance :=
  getProvenance testFormula

-- Test height reasoning (when infrastructure complete)
example : ∃ n, ProofHeight Paper3Theory (Formula.atom 0) n := by
  refine ⟨0, ?_⟩
  apply ProofHeight.base
  simp [Paper3Theory]

-- Verify classical axioms are accessible
example : Paper3Theory.Provable (Formula.atom 10) :=
  functor_composition_gap

-- Test provenance tagging
#eval provenanceTag Provenance.lean
#eval provenanceTag Provenance.classical

#eval "P4_Meta smoke test: OK!"

-- Test height certificate structure is well-formed
section HeightCertTest
  open Papers.P4Meta
  
  -- Just verify the structure compiles and can be used
  def testStep : Nat → Formula
  | 0 => Formula.atom 300
  | _ => Formula.atom 301
  
  def testCert : HeightCertificate Paper3Theory testStep (Formula.atom 300) :=
  { n     := 1
  , upper := by simp [ExtendIter, testStep, Extend]
  , note  := "Test certificate"
  }
  
  -- Verify the structure fields are accessible
  #check testCert.n
  #check testCert.upper
  #check testCert.note
end HeightCertTest

-- Part III ladders: quick sanity checks
section LadderTests
  open Papers.P4Meta

  #check lpo_height1_cert Paper3Theory
  #eval (lpo_height1_cert Paper3Theory).n      -- should print 1

  #check con_height_cert Paper3Theory 0
  #eval (con_height_cert Paper3Theory 0).n     -- should print 1

  -- Demonstrate lifting a certificate to a later stage
  def lpo_cert_stage1 := lpo_height1_cert Paper3Theory
  def lpo_cert_stage1_again :=
    HeightCertificate.lift lpo_cert_stage1 1 (Nat.le_refl _)
  #check lpo_cert_stage1_again.upper
end LadderTests

-- Product/sup tests on the same ladder
section ProductSupTests
  open Papers.P4Meta

  -- Two certificates on the same LPO ladder:
  --   - LPO at stage 1
  --   - filler at stage 2
  def lpo_cert := lpo_height1_cert Paper3Theory
  def filler_cert := lpo_filler_height2_cert Paper3Theory

  -- Combine them to a pair at stage max(1,2) = 2
  def pairCert :=
    combineCertificates (T := Paper3Theory)
      (step := lArithSteps Paper3Theory)
      (φ := LPO) (ψ := lpoFiller)
      lpo_cert filler_cert

  #check pairCert.n
  #eval  pairCert.n                       -- should print 2
  #check pairCert.upper_left              -- LPO holds at stage 2
  #check pairCert.upper_right             -- filler holds at stage 2
end ProductSupTests

-- N-ary product/sup aggregator tests
section MultiSupTests
  open Papers.P4Meta

  -- Build a list of single-goal certs on the same ladder.
  def lpoNamed : Σ φ, HeightCertificate Paper3Theory (lArithSteps Paper3Theory) φ :=
    ⟨LPO, lpo_height1_cert Paper3Theory⟩
  def fillerNamed : Σ φ, HeightCertificate Paper3Theory (lArithSteps Paper3Theory) φ :=
    ⟨lpoFiller, lpo_filler_height2_cert Paper3Theory⟩

  def bag := HeightCertificateBag.fromList
    (T := Paper3Theory) (step := lArithSteps Paper3Theory)
    [lpoNamed, fillerNamed]

  #eval bag.n                             -- expect 2
  #eval maxStageOfCerts [lpoNamed, fillerNamed]  -- expect 2
  
  -- Simple combination test
  def simplePair := combineCertsSimple 
    (lpo_height1_cert Paper3Theory)
    (lpo_filler_height2_cert Paper3Theory)
  
  #check simplePair
end MultiSupTests

end Papers.P4Meta.Tests