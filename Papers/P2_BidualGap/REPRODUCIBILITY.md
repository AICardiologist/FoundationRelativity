# Paper 2: Reproducibility Information

## Artifact DOI
- **10.5281/zenodo.13356587**

## Release
- **GitHub Release**: [p2-minimal-v0.1](https://github.com/AICardiologist/FoundationRelativity/releases/tag/p2-minimal-v0.1)

## Build Instructions

### Prerequisites
- Lean 4 (version specified in `lean-toolchain`)
- Lake build system (comes with Lean 4)

### Quick Build (Minimal Target)

```bash
# Clone repository
git clone https://github.com/FoundationRelativity/FoundationRelativity.git
cd FoundationRelativity

# Checkout tagged version
git checkout p2-minimal-v0.1

# Build minimal target (no dependencies)
lake build Papers.P2_BidualGap.P2_Minimal
```

### Build Details

**Repository**: https://github.com/FoundationRelativity/FoundationRelativity  
**Tag**: `p2-minimal-v0.1`  
**Build Target**: `Papers.P2_BidualGap.P2_Minimal`  
**Toolchain**: `leanprover/lean4:v4.23.0-rc2` (see `lean-toolchain`)  
**Build Time**: ~30 seconds (minimal target only)

## Artifact Structure

### Core Implementation (0 sorries, dependency-free)
- `Papers/P2_BidualGap/HB/OptionB/CorePure.lean` - Option B architecture
- `Papers/P2_BidualGap/HB/OptionB/Instances.lean` - Example instantiation

### Build Targets
- **P2_Minimal** - Clean build with Option B core (builds without mathlib)
- **P2_Full** - Complete build with all components (requires aligned toolchain)

## Option B Architecture

The Option B implementation provides a modular separation between:

1. **Assumption** (`HasNonzeroQuotFunctional`): 
   - Under classical choice (e.g., via Banach limit), a nonzero functional exists on ℓ∞/c₀
   - WLPO alone is not known to imply this for ℓ∞/c₀
   - For c₀ directly, WLPO provides the gap (Paper 2's constructive result)

2. **Bridge** (`QuotToGapBridge`):
   - Purely analytic: maps quotient functional to bidual gap
   - Works for any Banach space with appropriate structure

3. **Combination** (`gap_of_optionB`):
   - Modular theorem combining assumption and bridge
   - Instance-based for flexible instantiation

## Verification

The minimal build completes with:
- **0 errors**
- **0 sorries** in Option B core
- **Dependency-free** (no mathlib required for minimal target)

## Notes

- Option B Core compiles without mathlib
- The ℓ∞ instantiation is provided as an assumption
- A constructive c₀ path is developed separately in the full build
- WIP files are isolated in `Papers/P2_BidualGap/WIP/`

## LLM Acknowledgment

Development assisted by:
- Gemini 2.5 Deep Think (architecture brainstorming)
- GPT-5 Pro (Lean scaffolding and refactoring)
- Claude Code (repository management and build scripts)

All final proofs and code were verified by Lean; any LLM-generated suggestions were reviewed and rewritten as needed.