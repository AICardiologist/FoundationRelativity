/-
  Paper 21: Bell Nonlocality and the Constructive Cost of Disjunction: LLPO
  PartB/PartB_Main.lean — Main equivalence: LLPO ↔ BellSignDecision

  Combines the forward direction (LLPO → BellSignDecision)
  with the backward direction (BellSignDecision → LLPO).
-/
import Papers.P21_BellLLPO.PartB.Forward
import Papers.P21_BellLLPO.PartB.Backward

namespace Papers.P21

/-- Theorem 6 (Main equivalence):
    LLPO is equivalent to the Bell sign decision.

    This is the central result of Paper 21:
    deciding the sign of the Bell asymmetry (Alice-side vs Bob-side
    nonlocality contribution) has exactly the logical strength of LLPO. -/
theorem llpo_iff_bell_sign :
    LLPO ↔ BellSignDecision :=
  ⟨bell_sign_of_llpo, llpo_of_bell_sign⟩

-- ============================================================
-- Axiom audit
-- Expected: [propext, Classical.choice, Quot.sound, llpo_real_of_llpo]
-- ============================================================
#print axioms llpo_iff_bell_sign

end Papers.P21
