/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  PartA/Uncolorability.lean — The CEGA graph is KS-uncolorable

  This is the combinatorial core: no {0,1}-coloring of the 18 CEGA
  vertices satisfies "exactly one = 1" in every context.

  Proved by native_decide over the 2^18 = 262,144 coloring search space.
  This is entirely constructive (BISH) — a finite exhaustive verification.
-/
import Papers.P24_KochenSpecker.Defs.CEGAData

namespace Papers.P24

/-- The CEGA 18-vector KS graph is uncolorable: no {true, false}-assignment
    to the 18 vertices satisfies "exactly one true per context" for all
    9 contexts simultaneously.

    This is a finite computation over 2^18 = 262,144 candidate colorings.
    The `native_decide` tactic delegates to compiled Lean code. -/
theorem cega_uncolorable : isKSUncolorable cegaGraph := by
  native_decide

-- Axiom audit
-- Expected: [Lean.ofReduceBool] (from native_decide)
#print axioms cega_uncolorable

end Papers.P24
