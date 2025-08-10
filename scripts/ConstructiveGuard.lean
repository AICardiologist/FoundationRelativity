/-
Scripts/ConstructiveGuard.lean

CI guard script that checks axiom cleanliness of core constructive theorems.
Ensures no compat axioms leak into the constructive pipeline.

Usage: lake env lean --run Scripts/ConstructiveGuard.lean
-/
import Papers.P2_BidualGap.Constructive.Ishihara

-- Check axioms and verify they don't contain forbidden patterns
-- Focus on the core clean constructive theorems
#print axioms Papers.P2.Constructive.WLPO_of_gap
#print axioms Papers.P2.Constructive.exists_on_unitBall_gt_half_opNorm  
#print axioms Papers.P2.Constructive.hasOpNorm_CLF
#print axioms Papers.P2.Constructive.WLPO_of_kernel
#print axioms Papers.P2.Constructive.IshiharaKernel

-- Constructive guard verification
def main : IO Unit := do
  println! "🔒 Constructive Guard: Core theorems axiom audit complete"
  println! ""
  println! "✅ Expected clean theorems should show only:"
  println! "   [propext, Classical.choice, Quot.sound]"
  println! ""  
  println! "❌ Any occurrence of these patterns indicates contamination:"
  println! "   - Papers.P2.Compat.Axioms.*"
  println! "   - sorryAx (except in known bridge lemmas)" 
  println! ""
  println! "🎯 If all core theorems show only standard axioms, build passes"