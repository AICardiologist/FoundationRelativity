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
@[default_target] lean_lib Logic where srcDir := "."

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

-- Constructive axiom hygiene guard
script axiomGuard do
  let p ← IO.Process.output {
    cmd := "bash", args := #["Scripts/constructive_guard.sh"]
  }
  IO.print p.stdout
  if p.stderr.length > 0 then IO.eprintln p.stderr
  if p.exitCode != 0 then
    return 1
  else
    return 0

-- Hidden sorry scanner
script sorryGuard do
  let p ← IO.Process.output {
    cmd := "bash", args := #["Scripts/sorry_scan.sh"]
  }
  IO.print p.stdout
  if p.stderr.length > 0 then IO.eprintln p.stderr
  if p.exitCode != 0 then
    return 1
  else
    return 0

-- Complete CI guard suite (also builds the smoke tests)
script fullGuard do
  let p1 ← IO.Process.output { cmd := "bash", args := #["Scripts/constructive_guard.sh"] }
  IO.print p1.stdout
  if p1.stderr.length > 0 then IO.eprintln p1.stderr
  if p1.exitCode != 0 then return 1

  let p2 ← IO.Process.output { cmd := "bash", args := #["Scripts/sorry_scan.sh"] }
  IO.print p2.stdout
  if p2.stderr.length > 0 then IO.eprintln p2.stderr
  if p2.exitCode != 0 then return 2

  -- Pin-safe smoke test target
  let p3 ← IO.Process.output { cmd := "bash", args := #["-lc", "lake build Papers.P2_BidualGap.Basics.FiniteCesaroTests"] }
  IO.print p3.stdout
  if p3.stderr.length > 0 then IO.eprintln p3.stderr
  if p3.exitCode != 0 then return 3

  -- §3 Boolean sublattice smoke tests
  let p4 ← IO.Process.output { cmd := "bash", args := #["-lc", "lake build Papers.P2_BidualGap.Gap.BooleanSubLatticeTests"] }
  IO.print p4.stdout
  if p4.stderr.length > 0 then IO.eprintln p4.stderr
  if p4.exitCode != 0 then return 4

  -- §3.1 Indicator spec smoke tests
  let p5 ← IO.Process.output { cmd := "bash", args := #["-lc", "lake build Papers.P2_BidualGap.Gap.IndicatorSpecTests"] }
  IO.print p5.stdout
  if p5.stderr.length > 0 then IO.eprintln p5.stderr
  if p5.exitCode != 0 then return 5

  -- §3.1 Indicator spec ↔ eventual-zero smoke tests
  let p6 ← IO.Process.output { cmd := "bash", args := #["-lc", "lake build Papers.P2_BidualGap.Gap.IndicatorEventualTests"] }
  IO.print p6.stdout
  if p6.stderr.length > 0 then IO.eprintln p6.stderr
  if p6.exitCode != 0 then return 6

  -- §3.1 Indicator c0Spec bridge smoke tests
  let p7 ← IO.Process.output { cmd := "bash", args := #["-lc", "lake build Papers.P2_BidualGap.Gap.C0SpecTests"] }
  IO.print p7.stdout
  if p7.stderr.length > 0 then IO.eprintln p7.stderr
  if p7.exitCode != 0 then return 7

  -- §3.2/3.4/3.5 ι embedding smoke tests
  let p8 ← IO.Process.output { cmd := "bash", args := #["-lc", "lake build Papers.P2_BidualGap.Gap.IotaTests"] }
  IO.print p8.stdout
  if p8.stderr.length > 0 then IO.eprintln p8.stderr
  if p8.exitCode != 0 then return 8

  println! "🛡️ All guards passed - fortress secure!"
  return 0

-- Paper smoke tests (Day 1)
lean_exe PaperP1Tests where
  root := `Papers.P1_GBC.SmokeTest

-- Sprint 44 Day 1: Paper #1 CI integration
lean_exe Paper1SmokeTest where
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

-- Sprint 43 Day 3: Additional regression test
lean_exe PseudoFunctorLawsTest where
  root := `test.PseudoFunctorLawsTests

-- Sprint 43 Day 4: Paper-level pseudo-functor instances
lean_exe PseudoFunctorInstances where
  root := `Papers.PseudoFunctorInstances

-- Sprint 35-36 Test Executables
lean_exe CheegerProofTests where
  root := `test.CheegerProofTests

lean_exe Rho4ProofTests where
  root := `test.Rho4ProofTests

-- Sprint 44 Day 1: Pseudo-natural transformation tests
lean_exe PseudoNatTransLawsTests where
  root := `test.PseudoNatTransLawsTests

-- QA Mandated: No-shortcuts enforcement tools
lean_exe cheap_proofs where
  root := `scripts.lean.CheapProofs
