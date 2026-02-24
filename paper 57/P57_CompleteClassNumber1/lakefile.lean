import Lake
open Lake DSL

package «P57_CompleteClassNumber1» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target] lean_lib Papers where srcDir := "."
