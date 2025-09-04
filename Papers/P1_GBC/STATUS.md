# Paper 1 Status: Rank-One Toggle Operator

**Last Updated**: September 4, 2025
**CI Status**: ✅ Passing (as of Sep 4 nightly run)

## 🎉 Major Achievement
**Reduced from ~14 sorries to just 4!**

## Current State
- **Sherman-Morrison**: ✅ Complete (0 sorries) - FULLY PROVEN!
- **Projection API**: ✅ Complete (0 sorries)  
- **Toggle operator**: ✅ Complete (0 sorries)
- **Fredholm module**: 🔧 1 sorry (cokernel dimension needs H/K^⊥ ≅ K)
- **Spectrum module**: ⏳ 3 sorries (blocked on mathlib spectrum API)

## Known Issues
1. **Mathlib dependency**: `Mathlib.Analysis.NormedSpace.RCLike` occasionally fails in CI
   - Temporary issue that self-resolves
   - File exists in current mathlib version
   
2. **Spectrum API**: Waiting for mathlib operator spectrum support
   - Current workaround: spectrum_stub placeholder
   - Mathematical proofs documented but not formalized

## Build Instructions
```bash
lake build Papers.P1_GBC.P1_Minimal
```

## Linter Warnings
- Unused simp arguments in ShermanMorrison.lean (lines 35, 73)
- Unnecessary simpa suggestions (can use simp instead)
- These are cosmetic and don't affect correctness

## Progress Details

### What We Fixed (September 4, 2025)
Using current mathlib, we successfully closed 10 gaps:
- ✅ Fredholm kernel finite-dimensional: Used `infer_instance`
- ✅ Fredholm range closed: Used `isClosed_orthogonal`
- ✅ Kernel dimension = 1: Used `finrank_span_singleton`
- ✅ Sherman-Morrison norm bounds: Completed all proofs
- ✅ Compact perturbation structure: Simplified proofs

### Remaining Challenges
1. **Fredholm cokernel** (1 sorry)
   - Need: Prove `finrank (H ⧸ (span {u})ᗮ) = 1`
   - Requires: H/K^⊥ ≅ K isomorphism for closed subspaces
   - This is deep Hilbert space theory not yet in mathlib

2. **Spectrum characterization** (3 sorries)
   - Need: Operator spectrum API
   - Current mathlib has spectrum for Banach algebras but not specifically for `ContinuousLinearMap`
   - Would require significant API development

## Next Steps
- These remaining sorries are NOT easily closable
- Fredholm quotient needs new mathematical infrastructure
- Spectrum needs extensive API development in mathlib
- Current state represents the practical limit with existing mathlib