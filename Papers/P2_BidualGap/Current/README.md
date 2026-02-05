# P2_BidualGap Current Workset

This folder is the **single entry point** for the next paper edit and Lean updates.
Everything here is a **curated, insulated workset** of the current LaTeX and Lean sources.

Important:
- Files in this folder are **symlinks** to the canonical sources in the main repo.
- Edit the files **here** to avoid wandering into WIP or archived material.
- Do **not** use files under `WIP/` for the main paper or the main Lean proof.

## LaTeX (current paper)
- `Current/latex/paper-v6-020526.tex` (main paper draft, v6 dated 2026-02-05)
- `Current/latex/WLPO_completion_report_v3.tex` (supporting report)

## Lean (current proof files)
- `Current/lean/Basic.lean`
- `Current/lean/P2_Minimal.lean`
- `Current/lean/P2_Full.lean`
- `Current/lean/HB/DirectDual.lean`
- `Current/lean/HB/WLPO_to_Gap_HB.lean`
- `Current/lean/HB/WLPO_DualBanach.lean`
- `Current/lean/HB/SigmaEpsilon.lean`
- `Current/lean/HB/OptionB/CorePure.lean`
- `Current/lean/HB/OptionB/Instances.lean`

## Build (from repo root)
Run from `/Users/quantmann/FoundationRelativity`:
- `lake build Papers.P2_BidualGap.P2_Full`
- `lake build Papers.P2_BidualGap.P2_Minimal`

## Notes
- WIP files contain sorries and are excluded from builds.
- If you need to add a file to this workset, add it here as a symlink and update this README.
