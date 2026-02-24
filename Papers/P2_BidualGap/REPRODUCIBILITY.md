# Paper 2: Reproducibility Information (v6, 2026-02-05)

## Paper sources
- Main LaTeX: `documentation/paper-v6-020526.tex`
- Completion report: `documentation/WLPO_completion_report_v3.tex`

## Lean sources (current)
- Curated entry point: `Current/`
- Main Lean targets: `P2_Full.lean`, `P2_Minimal.lean`
- Key modules: `HB/DirectDual.lean`, `HB/WLPO_to_Gap_HB.lean`, `HB/WLPO_DualBanach.lean`, `HB/SigmaEpsilon.lean`
- OptionB minimal (standalone): `HB/OptionB/standalone/`

## Toolchains
- Root monorepo toolchain (for P2_Full/P2_Minimal): `leanprover/lean4:v4.23.0-rc2` (from `/Users/quantmann/FoundationRelativity/lean-toolchain`)
- OptionB standalone toolchain: `leanprover/lean4:v4.8.0` (from `HB/OptionB/standalone/lean-toolchain`)

## Build instructions

### A. OptionB standalone (minimal, no mathlib)

```bash
cd /Users/quantmann/FoundationRelativity/Papers/P2_BidualGap/HB/OptionB/standalone
lake clean
lake build
```

### B. Full mathlib-based build (monorepo root)

```bash
cd /Users/quantmann/FoundationRelativity
lake clean
lake build Papers.P2_BidualGap.P2_Full
lake build Papers.P2_BidualGap.P2_Minimal
```

## Verification status (this session)
- OptionB standalone: `lake clean` + `lake build` (success, 2026-02-05)
- Full root build: not executed in this session (requires running from repo root)

## Axiom audit commands

```lean
#print axioms WLPO_of_kernel
#print axioms WLPO_of_gap
#print axioms gap_from_WLPO
#print axioms gap_equiv_wlpo
```

## Notes
- Main equivalence is sorry-free in the current Lean build targets.
- WLPO-only dual completeness lemmas are isolated and optional.
- Stone window is a paper-level sketch in Appendix; not formalized in Lean.
