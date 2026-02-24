# P2_BidualGap Slim

This folder is a minimal entrypoint for the WLPO ↔ BidualGapStrong proof path.

## Entry file
- `All.lean` re-exports the core modules:
  - `Papers.P2_BidualGap.Basic`
  - `Papers.P2_BidualGap.CRM_MetaClassical.Ishihara`
  - `Papers.P2_BidualGap.HB.DirectDual`
  - `Papers.P2_BidualGap.HB.WLPO_to_Gap_HB`
 - `WLPO_to_Gap_HB.lean` is a local copy of the main proof file for easy sharing.

## Main theorem
- `Papers.P2.HB.gap_equiv_wlpo : BidualGapStrong.{0} ↔ WLPO`

## Note
`HB/WLPO_to_Gap_HB.lean` now discharges `DualIsBanach` obligations with
classical proofs (no axioms). If you want a WLPO-only constructive route,
we can refine this further.
