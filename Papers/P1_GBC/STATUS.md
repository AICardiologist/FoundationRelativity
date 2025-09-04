# Paper 1 Status: Rank-One Toggle Operator

**Last Updated**: September 4, 2025
**CI Status**: ✅ Passing (as of Sep 4 nightly run)

## Current State
- **Core implementation**: ~14 sorries remaining
- **Sherman-Morrison**: ✅ Complete (0 sorries)
- **Projection API**: ✅ Complete (0 sorries)  
- **Toggle operator**: ✅ Complete (0 sorries)
- **Spectrum module**: 3 sorries (mathlib spectrum API missing)
- **Fredholm alternative**: Framework only (documented stubs)

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

## Next Steps
- Wait for mathlib spectrum API updates
- Clean up linter warnings when convenient
- No urgent fixes needed - CI is stable