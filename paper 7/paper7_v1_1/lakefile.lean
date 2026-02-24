import Lake
open Lake DSL

package «P7_PhysicalBidualGap» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target] lean_lib Papers where srcDir := "."
