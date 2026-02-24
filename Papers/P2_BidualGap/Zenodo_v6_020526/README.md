# Zenodo Bundle (P2_BidualGap v6, 2026-02-05)

This folder contains a minimal, self-contained bundle for the WLPO ↔ bidual-gap paper.
It excludes WIP/Archived material and includes only what is needed to rebuild the
Lean artifacts and the paper.

**Version policy (important):**
Only `paper-v6-020526.tex` is the current paper. The only other `.tex` file in this
bundle is the completion report (`WLPO_completion_report_v3.tex`). There are no
other drafts in this bundle; do not create or edit additional `.tex` files here.

## Contents (authoritative sources)
- `Papers/P2_BidualGap/` — Lean sources + paper sources
- `Papers/P2_BidualGap/documentation/paper-v6-020526.tex` — **main paper (use this)**
- `Papers/P2_BidualGap/documentation/WLPO_completion_report_v3.tex` — supporting report only
- `Papers/P2_BidualGap/README.md` and `Papers/P2_BidualGap/REPRODUCIBILITY.md`
- `HB/OptionB/standalone` — standalone minimal Lean project (own toolchain)
- `lean-toolchain`, `lakefile.lean`, `lake-manifest.json` — build configuration
- `LICENSE`, `CITATION.cff`

## Build (full Lean targets)
From this folder:

```bash
lake clean
lake build Papers.P2_BidualGap.P2_Full
lake build Papers.P2_BidualGap.P2_Minimal
```

## Build (OptionB standalone)

```bash
cd Papers/P2_BidualGap/HB/OptionB/standalone
lake clean
lake build
```
