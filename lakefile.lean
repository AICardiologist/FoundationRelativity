import Lake
open Lake DSL

package «FoundationRelativity» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

-- Main Papers library (active development)
@[default_target] lean_lib Papers where srcDir := "."

-- Smoke test executable
lean_exe Paper2SmokeTest where
  root := `Papers.P2_BidualGap.SmokeTest

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

  println! "All guards passed."
  return 0