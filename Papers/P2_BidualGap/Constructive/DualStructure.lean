/-
  Papers/P2_BidualGap/Constructive/DualStructure.lean

  Stubs that connect WLPO to the constructive Banach-like behavior of duals.
  The key goal is to show WLPO implies the "closed under addition" part needed
  in DualIsBanach (and to supply a completeness witness when appropriate).
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Papers.P2_BidualGap.Basic

namespace Papers.P2.Constructive
open Papers.P2

/-- (Stub) WLPO implies the dual of `X` is Banach in the constructive sense.
    This is the crucial link you described: WLPO (via LLPO, etc.) gives enough
    strength for the existence of operator norms to be stable under addition. -/
theorem dual_is_banach_of_WLPO
  (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
  WLPO → DualIsBanach X := by
  -- TODO(P2-dual-structure-from-WLPO):
  --   - Prove "HasOperatorNorm f" + "HasOperatorNorm g" ⇒ "HasOperatorNorm (f+g)"
  --     under WLPO (norm existence/decidability step).
  --   - Provide a completeness witness `CompleteSpace (X →L[ℝ] ℝ)` as required
  --     by our constructive packaging (or show it follows in the settings we use).
  --
  -- Reference: Bridges & Richman, *Varieties of Constructive Mathematics*, and
  -- other CRM sources linking WLPO/LLPO to normability closure.
  sorry -- SORRY(P2-dual-structure-from-WLPO)

end Papers.P2.Constructive