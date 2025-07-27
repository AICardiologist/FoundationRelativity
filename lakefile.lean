import Lake
open Lake DSL

package «FoundationRelativity» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- one lean_lib per root namespace (folder name = module prefix)
@[default_target] lean_lib Found where srcDir := "."
@[default_target] lean_lib Gap2 where srcDir := "."
@[default_target] lean_lib APFunctor where srcDir := "."
@[default_target] lean_lib RNPFunctor where srcDir := "."
@[default_target] lean_lib AnalyticPathologies where srcDir := "."
@[default_target] lean_lib Axiom where srcDir := "."
@[default_target] lean_lib LogicDSL where srcDir := "."
@[default_target] lean_lib CategoryTheory where srcDir := "."
@[default_target] lean_lib Papers where srcDir := "."

-- Test executables
lean_exe testFunctors where
  root := `test.FunctorTest

lean_exe testNonIdMorphisms where
  root := `test.NonIdMorphisms

lean_exe WitnessTests where
  root := `test.WitnessTest

lean_exe AllPathologiesTests where
  root := `test.AllPathologiesTest

lean_exe Gap2ProofTests where
  root := `test.Gap2ProofTest

lean_exe APProofTests where
  root := `test.APProofTest

lean_exe RNPProofTests where
  root := `test.RNPProofTest

lean_exe RNP3ProofTests where
  root := `test.RNP3ProofTest

lean_exe SpectralGapProofTests where
  root := `test.SpectralGapProofTest

lean_exe GodelGapProofTests where
  root := `test.GodelGapProofTest

-- Paper smoke tests (Day 1)
lean_exe PaperP1Tests where
  root := `Papers.P1_GBC.SmokeTest

lean_exe PaperP2Tests where
  root := `Papers.P2_BidualGap.SmokeTest

lean_exe PaperP3Tests where
  root := `Papers.P3_2CatFramework.SmokeTest

-- Paper unit tests (Day 2)
lean_exe Paper2SmokeTest where
  root := `Papers.P2_BidualGap.RelativityNonFunc

lean_exe Paper3SmokeTest where
  root := `Papers.P3_2CatFramework.FunctorialObstruction

-- Sprint 43 (Day 4 target)
lean_exe PseudoFunctorLawsTests where
  root := `CategoryTheory.PseudoFunctor

-- Sprint 43 Day 3: Enhanced test suite
lean_exe PseudoFunctorLaws where
  root := `test.PseudoFunctorLaws
