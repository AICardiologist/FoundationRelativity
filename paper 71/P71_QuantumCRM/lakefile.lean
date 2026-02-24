import Lake
open Lake DSL

package P71_QuantumCRM where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0-rc1"

@[default_target]
lean_lib Papers
