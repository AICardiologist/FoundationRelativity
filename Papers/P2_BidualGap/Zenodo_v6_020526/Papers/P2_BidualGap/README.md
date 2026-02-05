# Paper 2: WLPO ↔ Bidual Gap (Zenodo v6, 2026-02-05)

## Authoritative Sources (read this first)
- **Main paper**: `documentation/paper-v6-020526.tex`
- **Supporting report**: `documentation/WLPO_completion_report_v3.tex`

**Important:** In this Zenodo bundle, `paper-v6-020526.tex` is the only paper draft.
Do not create or edit any other `.tex` files here.

## Lean Sources
All Lean sources live under `Papers/P2_BidualGap/`.

Key entry points:
- `P2_Full.lean`
- `P2_Minimal.lean`
- `HB/DirectDual.lean`
- `HB/WLPO_to_Gap_HB.lean`
- `HB/WLPO_DualBanach.lean`

Standalone minimal build:
- `HB/OptionB/standalone/`

## Build Commands
From the bundle root:

```bash
lake clean
lake build Papers.P2_BidualGap.P2_Full
lake build Papers.P2_BidualGap.P2_Minimal
```

Standalone OptionB:

```bash
cd Papers/P2_BidualGap/HB/OptionB/standalone
lake clean
lake build
```

## Status Notes
- The main equivalence (WLPO ↔ bidual gap) is formalized in Lean.
- WLPO-conditional completeness lemmas are isolated in `HB/WLPO_DualBanach.lean`.
- The Stone window appears only as a paper sketch (Appendix) and is **not** formalized.

## AI Disclaimer
This formalization was produced with AI assistance under human direction and verified by Lean.
