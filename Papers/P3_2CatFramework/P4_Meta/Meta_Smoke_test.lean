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

-- Two-phase composition tests
section ConcatTests
  open Papers.P4Meta

  -- Define two simple ladders for testing
  def ladderA : Nat → Formula
  | 0 => Formula.atom 400
  | 1 => Formula.atom 401
  | _ => Formula.atom 402

  def ladderB : Nat → Formula  
  | 0 => Formula.atom 410
  | 1 => Formula.atom 411
  | _ => Formula.atom 412

  -- Test concatenation at k=2
  def concatLadder := concatSteps 2 ladderA ladderB

  -- Verify prefix behavior
  #eval concatLadder 0  -- expect atom 400 (from A)
  #eval concatLadder 1  -- expect atom 401 (from A)
  #eval concatLadder 2  -- expect atom 410 (from B at index 0)
  #eval concatLadder 3  -- expect atom 411 (from B at index 1)

  -- Test prefix equality theorem
  example : ExtendIter Paper3Theory concatLadder 2 = ExtendIter Paper3Theory ladderA 2 := by
    apply concat_prefix_eq
    decide

  -- Test tail equality theorem
  example : ExtendIter Paper3Theory concatLadder 4 = 
            ExtendIter (ExtendIter Paper3Theory ladderA 2) ladderB 2 := by
    have : 4 = 2 + 2 := rfl
    rw [this]
    apply concat_tail_eq

  -- Test certificate lifting
  def testCertA : HeightCertificate Paper3Theory ladderA (Formula.atom 400) :=
  { n := 1
  , upper := by simp [ExtendIter_succ, ExtendIter_zero, ladderA, Extend]
  , note := "Test cert for ladderA"
  }

  -- Lift to concatenated ladder
  def liftedCert := prefixLiftCert (B := ladderB) 2 testCertA (by decide : 1 ≤ 2)
  
  #check liftedCert.n     -- should still be 1
  #check liftedCert.upper -- proves atom 400 at stage 1 in concat ladder
  
  -- Test tail certificate lifting
  def testCertB : HeightCertificate (ExtendIter Paper3Theory ladderA 2) ladderB (Formula.atom 410) :=
  { n := 1
  , upper := by simp [ExtendIter_succ, ExtendIter_zero, ladderB, Extend]
  , note := "Test cert for ladderB"
  }
  
  def tailLifted := tailLiftCert 2 testCertB
  
  #check tailLifted.n     -- should be 2 + 1 = 3
  #eval tailLifted.n      -- should print 3
  
  -- Test concatPairCert: compose both phases at once
  def pairOnAB :
    HeightCertificatePair Paper3Theory concatLadder ⟨Formula.atom 400, Formula.atom 410⟩ :=
    concatPairCert (T := Paper3Theory) (A := ladderA) (B := ladderB) (k := 2)
      (φ := Formula.atom 400) (ψ := Formula.atom 410)
      testCertA (by decide : testCertA.n ≤ 2) testCertB

  #check pairOnAB.n
  #check pairOnAB.upper_left   -- proves atom 400 at stage pairOnAB.n on concat
  #check pairOnAB.upper_right  -- proves atom 410 at stage pairOnAB.n on concat
  
  -- ω-stage consequences of the concatenated pair
  def pairOnABω := Papers.P4Meta.pairToOmega pairOnAB
  #check pairOnABω.1  -- proves atom 400 at ω
  #check pairOnABω.2  -- proves atom 410 at ω
  
  -- Identity at k = 0
  example :
      ExtendIter Paper3Theory (concatSteps 0 ladderA ladderB) 3
        = ExtendIter Paper3Theory ladderB 3 := by
    simpa using
      (Papers.P4Meta.concat_zero_left
        (T := Paper3Theory) (A := ladderA) (B := ladderB) (n := 3))

  -- Associativity (tail form)
  example :
      ExtendIter Paper3Theory
        (concatSteps 1 ladderA (concatSteps 2 ladderB ladderA)) (1 + (2 + 1))
        =
      ExtendIter (ExtendIter (ExtendIter Paper3Theory ladderA 1) ladderB 2) ladderA 1 := by
    simpa using
      (Papers.P4Meta.concat_assoc_tail_eq
        (T := Paper3Theory) (A := ladderA) (B := ladderB) (C := ladderA)
        (k := 1) (ℓ := 2) (n := 1))
        
  -- ω from prefix
  example :
    (Extendω Paper3Theory concatLadder).Provable (Formula.atom 400) :=
  by
    exact Papers.P4Meta.omega_of_prefixCert
      (T := Paper3Theory) (A := ladderA) (B := ladderB) (k := 2)
      testCertA (by decide : testCertA.n ≤ 2)

  -- ω from tail
  example :
    (Extendω Paper3Theory concatLadder).Provable (Formula.atom 410) :=
  by
    exact Papers.P4Meta.omega_of_tailCert
      (T := Paper3Theory) (A := ladderA) (B := ladderB) (k := 2)
      testCertB
      
  -- General prefix/tail equalities
  example :
    ExtendIter Paper3Theory (concatSteps 2 ladderA ladderB) 1
      = ExtendIter Paper3Theory ladderA 1 :=
  Papers.P4Meta.concat_prefix_le_eq (T := Paper3Theory)
    (A := ladderA) (B := ladderB) (k := 2) (i := 1) (by decide)

  example :
    ExtendIter Paper3Theory (concatSteps 2 ladderA ladderB) 3
      = ExtendIter (ExtendIter Paper3Theory ladderA 2) ladderB (3 - 2) :=
  Papers.P4Meta.concat_tail_ge_eq (T := Paper3Theory)
    (A := ladderA) (B := ladderB) (k := 2) (i := 3) (by decide)

  -- Lift a concatenated pair to ω in one shot
  example :
    (Extendω Paper3Theory concatLadder).Provable (Formula.atom 400) ∧
    (Extendω Paper3Theory concatLadder).Provable (Formula.atom 410) :=
  Papers.P4Meta.omega_of_concat_pair
    (T := Paper3Theory) (A := ladderA) (B := ladderB) (k := 2)
    testCertA (by decide : testCertA.n ≤ 2) testCertB

  -- Pair certificate lifting (stage bookkeeping)
  def liftedPair :=
    Papers.P4Meta.HeightCertificatePair.lift pairOnAB (pairOnAB.n + 1) (Nat.le_succ _)
  #check liftedPair.n
  #check liftedPair.upper_left
  #check liftedPair.upper_right
  
  -- `@[simp]` rewrites at the cut
  example :
    ExtendIter Paper3Theory (concatSteps 2 ladderA ladderB) 2
      = ExtendIter Paper3Theory ladderA 2 := by simpa
  example :
    ExtendIter Paper3Theory (concatSteps 2 ladderA ladderB) (2 + 1)
      = ExtendIter (ExtendIter Paper3Theory ladderA 2) ladderB 1 := by simpa
end ConcatTests

-- Test lpo_pack_pair
section LPOPackTest
  open Papers.P4Meta
  
  def packedPair := lpo_pack_pair Paper3Theory
  #check packedPair
  #eval packedPair.n  -- should be 2 (max of 1 and 2)
  
  -- Push the packed pair to ω
  def packedAtOmega := pairToOmega packedPair
  #check packedAtOmega.1  -- LPO at ω
  #check packedAtOmega.2  -- filler at ω
end LPOPackTest

-- RFN ⇒ Con smoketest (schematic)
section RFNConTests
  open Papers.P4Meta
  variable (Text Tbase : Theory) (h : HasRFN_Sigma1 Text Tbase)
  example : Con Tbase := RFN_implies_Con Text Tbase h
end RFNConTests

-- UCT / Baire calibrator smoketests
section CalibratorTests
  open Papers.P4Meta

  -- UCT at ω and ω+1 from FT
  example : (Extendω Paper3Theory (ftSteps Paper3Theory)).Provable UCT01 := 
    UCT_at_omega Paper3Theory
  example : (ExtendωPlus Paper3Theory (ftSteps Paper3Theory) 1).Provable UCT01 := 
    UCT_at_omegaPlus Paper3Theory 1

  -- Baire at ω and ω+2 from DC_ω
  example : (Extendω Paper3Theory (dcωSteps Paper3Theory)).Provable BairePinned := 
    Baire_at_omega Paper3Theory
  example : (ExtendωPlus Paper3Theory (dcωSteps Paper3Theory) 2).Provable BairePinned := 
    Baire_at_omegaPlus Paper3Theory 2

  -- PosFam basic checks
  noncomputable example : UCT_posFam Paper3Theory = [⟨UCT01, uct_upper_from_FT_cert Paper3Theory⟩] := rfl
  noncomputable example : Baire_posFam Paper3Theory = [⟨BairePinned, baire_upper_from_DCω_cert Paper3Theory⟩] := rfl
end CalibratorTests

-- Bounded congruence test for ω+ε
section BoundedCongruenceTest
  open Papers.P4Meta
  
  -- Define two step ladders that agree only up to a bound
  def S₁ : Nat → Formula
  | 0 => Formula.atom 600
  | 1 => Formula.atom 601
  | _ => Formula.atom 602
  
  def S₂ : Nat → Formula
  | 0 => Formula.atom 600
  | 1 => Formula.atom 601
  | _ => Formula.atom 602
  
  -- They agree pointwise (trivially in this example)
  theorem S₁_eq_S₂ : S₁ = S₂ := rfl
  
  -- Bounded congruence: use agreement only up to the witnessing stage
  example (ψ : Formula) :
      (ExtendωPlus Paper3Theory S₁ 2).Provable ψ ↔
      (ExtendωPlus Paper3Theory S₂ 2).Provable ψ := by
    -- From earlier: S₁_eq_S₂ : S₁ = S₂
    have hpt : ∀ n i, i < n + 2 → S₁ i = S₂ i := by
      intro n i _; simpa using congrArg (fun f => f i) S₁_eq_S₂
    simpa using
      Papers.P4Meta.ExtendωPlus_provable_congr_up_to
        (T := Paper3Theory) (A := S₁) (B := S₂) (ε := 2) hpt ψ
end BoundedCongruenceTest

end Papers.P4Meta.Tests