import Lake
open Lake DSL

package «P2_BidualGap» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target] lean_lib Papers where
  srcDir := "."

lean_exe Paper2SmokeTest where
  root := `Papers.P2_BidualGap.SmokeTest
