import Lake
open Lake DSL

package «FoundationRelativity» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
  @ "v4.3.0"

-- one lean_lib per root namespace (folder name = module prefix)
@[default_target] lean_lib Found where srcDir := "."
@[default_target] lean_lib Gap2 where srcDir := "."
@[default_target] lean_lib APFunctor where srcDir := "."
@[default_target] lean_lib RNPFunctor where srcDir := "."

-- Test executable
lean_exe PathTests where
  root := `PathologyTests

lean_exe testFunctors where
  root := `test.FunctorTest

lean_exe testNonIdMorphisms where
  root := `test.NonIdMorphisms

lean_exe WitnessTests where
  root := `test.WitnessTest

lean_exe Gap2MigrationTests where
  root := `test.Gap2MigrationTest
