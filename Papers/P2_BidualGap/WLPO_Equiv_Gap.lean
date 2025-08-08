/-
  Papers/P2_BidualGap/WLPO_Equiv_Gap.lean
  WLPO ↔ BidualGap — *stubs only*. No vacuous proofs.
-/
import Mathlib.Tactic
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.Compat.NonReflexive
import Papers.P2_BidualGap.Constructive.Ishihara

namespace Papers.P2
open Classical
noncomputable section

/-- (Stub) `BidualGap → WLPO` via Ishihara's argument. -/
lemma gap_implies_wlpo : BidualGap → WLPO := by
  intro hGap
  -- TODO:
  --   * Unpack the witness `⟨X, _, _, _, not_surj⟩`.
  --   * Build `Constructive.IshiharaKernel` from `j := inclusionInDoubleDual` and `not_surj`.
  --   * Apply `Constructive.WLPO_of_kernel`.
  sorry -- SORRY(P2-gap-implies-wlpo)

/-- (Stub) `WLPO → BidualGap` via a direct `c₀ / ℓ^∞` construction (professor's Option B). -/
lemma wlpo_implies_gap : WLPO → BidualGap := by
  intro hWLPO
  -- TODO:
  --   * Work in `X := c₀` with `X* = ℓ¹`, `X** = ℓ^∞`.
  --   * Use WLPO to build a functional on `ℓ^∞` vanishing on `c₀` that is not an ℓ¹ functional.
  --   * Conclude `¬ surjective (inclusionInDoubleDual ℝ X)`.
  sorry -- SORRY(P2-wlpo-implies-gap)

/-- (Stub) Main equivalence, bundling the two directions. -/
theorem gap_equiv_WLPO : BidualGap ↔ WLPO := by
  constructor
  · exact gap_implies_wlpo
  · exact wlpo_implies_gap

end Papers.P2