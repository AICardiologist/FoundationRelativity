/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  PartB/PartB_Main.lean — LLPO ↔ KSSignDecision

  The main calibration result: LLPO is equivalent to the KS sign
  decision, confirming that Kochen-Specker contextuality has
  constructive cost exactly LLPO.
-/
import Papers.P24_KochenSpecker.PartB.Forward
import Papers.P24_KochenSpecker.PartB.Backward

namespace Papers.P24

/-- LLPO is equivalent to the KS sign decision.
    Forward: LLPO → KSSignDecision (via the real-valued LLPO bridge)
    Backward: KSSignDecision → LLPO (via geometric series encoding) -/
theorem llpo_iff_ks_sign : LLPO ↔ KSSignDecision :=
  ⟨ks_sign_of_llpo, llpo_of_ks_sign⟩

-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]
#print axioms llpo_iff_ks_sign

end Papers.P24
