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

/-- (Stub) `BidualGapStrong → WLPO` via Ishihara's argument. -/
lemma gap_implies_wlpo : BidualGapStrong → WLPO := by
  intro hGap
  -- TODO(P2-gap→WLPO-strong):
  --   Unpack `hGap` to get `X`, `DualIsBanach X`, `DualIsBanach X**`, and `¬surj j`.
  --   Build an `IshiharaKernel X` (f, gα, separation), then apply `WLPO_of_kernel`.
  sorry

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