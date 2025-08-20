# PR: Add Paper 2 Option-B Minimal Reproducible Build

## Summary

This PR adds a reproducible, dependency-free "Option-B Minimal" build for Paper 2.

## What's included

- `P2_Minimal.lean` (CI target) importing OptionB/CorePure + minimal Instances
- No-sorry guard in CI via `scripts/no_sorry_p2_minimal.sh`
- Reproducibility docs + release notes
- GitHub Actions workflow for automated CI verification

### Key Files

**Core Implementation (0 sorries, no dependencies):**
- `Papers/P2_BidualGap/P2_Minimal.lean` - CI build target
- `Papers/P2_BidualGap/HB/OptionB/CorePure.lean` - Abstract Option-B interface
- `Papers/P2_BidualGap/HB/OptionB/Instances.lean` - End-to-end demonstration

**Infrastructure:**
- `.github/workflows/p2-minimal.yml` - CI workflow
- `scripts/no_sorry_p2_minimal.sh` - Sorry-free verification
- `Papers/P2_BidualGap/REPRODUCIBILITY.md` - Build instructions
- `Papers/P2_BidualGap/RELEASE_NOTES_v0.1.md` - Release documentation

## What's not included

- Mathlib-based full build (gated behind toolchain alignment) — kept out of this PR
- Classical ℓ∞/c₀ instance — provided as a skeleton only (`ClassicalInstances.lean`)
- WIP files with many sorries — isolated in `Papers/P2_BidualGap/WIP/`

## Why this PR

- Establishes a clean, CI-verified baseline artifact for the paper
- Keeps high-sorry/WIP files isolated from the minimal build
- Provides reproducible build tagged as `p2-minimal-v0.1`

## Acceptance criteria

✅ Paper2-Minimal CI is green  
✅ No "sorry" in minimal target (guarded by CI script)  
✅ Repository structure reflects minimal vs. WIP separation  
✅ Build completes in ~30 seconds with 0 errors  

## Testing

```bash
# Build minimal target
lake build Papers.P2_BidualGap.P2_Minimal

# Verify no sorries
./scripts/no_sorry_p2_minimal.sh
```

## Reviewer notes

The minimal artifact shows the Option-B theorem schema compiles, is sorry-free, and is reproducible (see `REPRODUCIBILITY.md`). The "full" build will come in a later PR after toolchain alignment.

The Option-B architecture provides:
1. `HasNonzeroQuotFunctional` - assumption interface
2. `QuotToGapBridge` - analytic bridge interface  
3. `gap_of_optionB` - modular combination theorem

This design allows different foundational assumptions (WLPO vs classical) to be plugged in without modifying the core bridge theorem.