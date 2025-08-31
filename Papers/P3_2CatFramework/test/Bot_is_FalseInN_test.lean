/-
  Test that Bot_is_FalseInN is now a theorem with minimal axiom dependencies
  PR-5b: Should no longer depend on Ax.Bot_is_FalseInN
-/

import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Core

namespace Papers.P4Meta.ProofTheory

-- Should NOT show Ax.Bot_is_FalseInN in dependencies
#print axioms Bot_is_FalseInN
-- Expected: Only standard axioms (propext), NOT Ax.Bot_is_FalseInN

-- Verify it works as expected
example {T : Theory} [h : HasSigma1Reflection T] : ¬h.TrueInN Bot := Bot_is_FalseInN

end Papers.P4Meta.ProofTheory