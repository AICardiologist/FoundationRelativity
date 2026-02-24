import Lake
open Lake DSL

package «P32_QEDRenormalization» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target] lean_lib Papers where srcDir := "."
