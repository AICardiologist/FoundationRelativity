/-
  Test that Sigma1_Bot is now a theorem with no axiom dependencies
-/

import Papers.P3_2CatFramework.P4_Meta.ProofTheory.Core

open Papers.P4Meta.ProofTheory

-- Should show no Ax. dependencies
#print axioms Sigma1_Bot
-- Expected output: no axioms

-- Verify it's actually true
example : Sigma1 Bot := Sigma1_Bot