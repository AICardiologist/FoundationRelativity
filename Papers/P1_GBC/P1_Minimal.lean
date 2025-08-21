/-
  Paper 1: Rank-One Toggle - Minimal Target

  This file serves as the minimal build target for Paper 1's core results.
  It imports only the sorry-free modules that form the foundation of the
  rank-one toggle construction.

  Build: `lake build Papers.P1_GBC.P1_Minimal`
  Verify: `./scripts/no_sorry_p1_minimal.sh`
-/

-- Core rank-one toggle modules (sorry-free)
import Papers.P1_GBC.RankOneToggle.Projection

namespace Papers.P1_GBC
  def p1_minimal_marker : Unit := ()
  #eval (1 : Nat)
end Papers.P1_GBC

-- Export namespaces for convenient access
open RankOneToggle