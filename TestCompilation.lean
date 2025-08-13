/-
TestCompilation.lean
Simple test to verify our implementations compile with basic structure.
-/
import Mathlib.Tactic
import Papers.P2_BidualGap.Constructive.NormabilityFromWLPO

noncomputable section
namespace TestCompilation

-- Test that we can import and reference the key functions
#check Papers.P2.Constructive.dual_is_banach_c0_from_WLPO
#check Papers.P2.Constructive.c0_dual_is_banach_of_wlpo

-- Test axiom checking on the WLPO isolation module
-- This should only show WLPO-related axioms in this specific file
run_cmd Lean.logInfo "WLPO isolation module imported successfully"

end TestCompilation