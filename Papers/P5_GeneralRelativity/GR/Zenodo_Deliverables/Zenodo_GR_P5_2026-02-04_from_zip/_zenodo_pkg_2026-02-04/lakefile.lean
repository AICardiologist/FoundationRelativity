import Lake
open Lake DSL

package «FoundationRelativity» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- Main Papers library (active development)
@[default_target] lean_lib Papers where srcDir := "."

-- Essential smoke test executables
lean_exe Paper1SmokeTest where
  root := `Papers.P1_GBC.SmokeTest

lean_exe Paper2SmokeTest where
  root := `Papers.P2_BidualGap.SmokeTest

lean_exe Paper3SmokeTest where
  root := `Papers.P3_2CatFramework.SmokeTest

lean_lib Paper6Heisenberg where
  roots := #[`Papers.P6_Heisenberg.Main]

-- QA enforcement tools
lean_exe cheap_proofs where
  root := `scripts.lean.CheapProofs

-- Core CI guard suite
script fullGuard do
  -- Build Paper 2 minimal for smoke test
  let p1 ← IO.Process.output { cmd := "lake", args := #["build", "Papers.P2_BidualGap.P2_Minimal"] }
  IO.print p1.stdout
  if p1.stderr.length > 0 then IO.eprintln p1.stderr
  if p1.exitCode != 0 then return 1

  -- Build Paper 1 minimal for smoke test  
  let p2 ← IO.Process.output { cmd := "lake", args := #["build", "Papers.P1_GBC.P1_Minimal"] }
  IO.print p2.stdout
  if p2.stderr.length > 0 then IO.eprintln p2.stderr
  if p2.exitCode != 0 then return 2

  println! "🛡️ All guards passed - fortress secure!"
  return 0