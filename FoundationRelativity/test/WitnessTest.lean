import Found.WitnessCore

/-!
# Witness API Test
Quick tests to verify the witness API works as expected.
-/

open Found Foundation

-- Test pathology type
structure TestPathology where
  data : Nat

-- Test witness type function
example : WitnessType TestPathology bish = Empty := rfl
example : WitnessType TestPathology zfc = PUnit := rfl

-- Test functor construction
#check pathologyFunctor TestPathology

def main : IO Unit := do
  IO.println "✓ Witness API tests pass"