import Lake
open Lake DSL

package «P35_ConservationMetatheorem» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib Papers where
  srcDir := "."
