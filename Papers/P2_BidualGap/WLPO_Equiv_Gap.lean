/-
  Papers/P2_BidualGap/WLPO_Equiv_Gap.lean
  WLPO ↔ BidualGapStrong — stubs only (no vacuous proofs).
-/
import Mathlib.Tactic
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.Constructive.Ishihara
import Papers.P2_BidualGap.Constructive.DualStructure

namespace Papers.P2
open Papers.P2.Constructive

/-- `BidualGapStrong → WLPO` (delegates via a monomorphic Type-level package to avoid universe issues). -/
lemma gap_implies_wlpo : BidualGapStrong → WLPO := by
  intro hGap
  -- Monomorphic witness → explicit-instance wrapper (no typeclass synthesis).
  exact Papers.P2.Constructive.WLPO_of_witness
    (Papers.P2.Constructive.kernel_from_gap hGap)

/-- (Stub) `WLPO → BidualGapStrong` via c₀/ℓ∞ with dual-structure provided by WLPO. -/
lemma wlpo_implies_gap : WLPO → BidualGapStrong := by
  intro hWLPO
  -- TODO(P2-WLPO→gap-strong):
  --   - Use `dual_is_banach_of_WLPO` to produce `DualIsBanach` for the spaces we need
  --     (e.g., X := c₀; then identify X*, X** and get the gap element in ℓ^∞).
  --   - Conclude `¬ surjective j : X → X**`.
  sorry

/-- (Stub) Main equivalence, bundling the two directions. -/
theorem gap_equiv_WLPO : BidualGapStrong ↔ WLPO := by
  constructor
  · exact gap_implies_wlpo
  · exact wlpo_implies_gap

end Papers.P2