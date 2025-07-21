import RNPFunctor.Proofs3

/-!
# RNP₃ Proof Tests

Tests for RNP_Fail₃ formal proofs showing DC_{ω+1} requirement.
-/

open RNPFunctor

#check noWitness_bish₃
#check witness_zfc₃  
#check RNP_requires_DCω_plus

def main : IO Unit := do
  IO.println "✓ RNP₃ proof type-checks"