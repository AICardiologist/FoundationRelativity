/-
  P2_Smoke: non-CI aggregator that sanity-checks symbol names/signatures
  for the Paper 2 codebase. It's intentionally light: only `#check`s.
  
  IMPORTANT: This file is NOT in CI - it's for local development only.

  Usage (local only, after toolchain alignment):
    lake env lean Papers/P2_BidualGap/P2_Smoke.lean
-/
import Papers.P2_BidualGap.HB.OptionB.CorePure
import Papers.P2_BidualGap.HB.OptionB.Instances
import Papers.P2_BidualGap.HB.Compat.CompletenessTransport
import Papers.P2_BidualGap.Constructive.OpNormCore
import Papers.P2_BidualGap.Constructive.Ishihara

noncomputable section

-- Namespaces we'll reference explicitly to avoid accidental shadowing.
open Papers

/-- Smoke check: Option-B core API exists. -/
#check Papers.P2_BidualGap.HB.OptionB.CorePure.HasNonzeroQuotFunctional
#check Papers.P2_BidualGap.HB.OptionB.CorePure.QuotToGapBridge
#check Papers.P2_BidualGap.HB.OptionB.CorePure.GapX
#check Papers.P2_BidualGap.HB.OptionB.CorePure.gap_of_optionB

/-- Smoke check: OpNormCore's minimal interface exists. -/
#check Papers.P2_BidualGap.Constructive.OpNorm.HasOpNorm
#check Papers.P2_BidualGap.Constructive.OpNorm.UnitBall
#check Papers.P2_BidualGap.Constructive.OpNorm.valueSet
#check Papers.P2_BidualGap.Constructive.OpNorm.hasOpNorm_zero

/-- Smoke check: completeness transport shim (version-stable). -/
#check Papers.P2_BidualGap.HB.Compat.completeSpace_of_linearIsometryEquiv
#check Papers.P2_BidualGap.HB.Compat.completeSpace_iff_of_linearIsometryEquiv

/-
  End-to-end schema: Instances should discharge the typeclasses required by gap_of_optionB.
  By opening the Instances namespace, Lean can synthesize the instances for Q, X, DX.
-/
open Papers.P2_BidualGap.HB.OptionB
open Papers.P2_BidualGap.HB.OptionB.Instances

-- If inference succeeds, this #check pins that gap_of_optionB closes to `GapX DX`.
#check (Papers.P2_BidualGap.HB.OptionB.CorePure.gap_of_optionB
        : Papers.P2_BidualGap.HB.OptionB.CorePure.GapX DX)

end