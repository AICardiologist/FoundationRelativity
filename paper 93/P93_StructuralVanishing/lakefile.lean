import Lake
open Lake DSL

package «papers» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.0-rc2"

@[default_target]
lean_lib «Papers» where
  srcDir := "."
