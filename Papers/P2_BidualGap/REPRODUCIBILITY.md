# Paper 2: Reproducibility Information

## Artifact DOI
- **Previous**: 10.5281/zenodo.13356587 (v0.1)
- **Current**: [To be assigned] (v0.2)

## Releases
- **v0.1**: [p2-minimal-v0.1](https://github.com/AICardiologist/FoundationRelativity/releases/tag/p2-minimal-v0.1) - Initial release
- **v0.2**: [p2-crm-v0.2](https://github.com/AICardiologist/FoundationRelativity/releases/tag/p2-crm-v0.2) - CRM methodology compliance update

## Build Instructions

### Prerequisites
- Lean 4 (version specified in `lean-toolchain`)
- Lake build system (comes with Lean 4)

### Quick Build (Main Theorem)

```bash
# Clone repository
git clone https://github.com/AICardiologist/FoundationRelativity.git
cd FoundationRelativity

# Checkout tagged version
git checkout p2-crm-v0.2

# Build main theorem
lake build Papers.P2_BidualGap.gap_equiv_wlpo
```

### Build Details

**Repository**: https://github.com/AICardiologist/FoundationRelativity  
**Current Tag**: `p2-crm-v0.2`  
**Build Target**: `Papers.P2_BidualGap.gap_equiv_wlpo`  
**Toolchain**: `leanprover/lean4:v4.22.0-rc4` (see `lean-toolchain`)  
**mathlib4**: `59e4fba0c656457728c559a7d280903732a6d9d1`  
**Build Time**: ~1-2 minutes (main theorem with dependencies)

## Artifact Structure

### Core Implementation (0 sorries)
- `Papers/P2_BidualGap/Core/HBExact.lean` - Finite Hahn-Banach
- `Papers/P2_BidualGap/Core/Kernel.lean` - Ishihara kernel infrastructure
- `Papers/P2_BidualGap/Bidual/*.lean` - Bidual space theory
- `Papers/P2_BidualGap/HB/Gap_to_WLPO_pure.lean` - Gap → WLPO direction
- `Papers/P2_BidualGap/HB/WLPO_to_Gap_pure.lean` - WLPO → Gap core
- `Papers/P2_BidualGap/HB/DirectDual.lean` - c₀ witness construction

### CRM Meta-Classical Components
- `Papers/P2_BidualGap/CRM_MetaClassical/Ishihara.lean` - Prop-level kernel
- `Papers/P2_BidualGap/CRM_MetaClassical/OpNormCore.lean` - Operator norms

### Documentation
- `Papers/P2_BidualGap/documentation/paper-v5.tex` - LaTeX paper with CRM updates
- `Papers/P2_BidualGap/README.md` - Project overview
- `Papers/P2_BidualGap/RELEASE_NOTES_v0.2.md` - Version 0.2 changes

### Build Targets
- **gap_equiv_wlpo** - Main equivalence theorem (0 sorries)
- **P2_Minimal** - Minimal build target
- **P2_Full** - Complete build with all components

## Version History

### v0.2 (September 2025) - CRM Compliance Update
- Meta-classical separation in Gap → WLPO direction
- Improved axiom hygiene with proper fencing
- Prop-level Ishihara kernel
- Updated LaTeX documentation
- 0 sorries in main theorem

### v0.1 (August 2025) - Initial Release
- Option B architecture
- Basic equivalence proof
- Initial formalization

## Verification

The main theorem builds with:
- **0 errors**
- **0 sorries** in core equivalence
- **3 WLPO-conditional sorries** in optional completeness module
- **Axioms used**: `[propext, Classical.choice, Quot.sound]` (only in Gap → WLPO)

## Archive Contents

The release archive (`p2-crm-v0.2.tar.gz`) contains:
- All Lean 4 source files for Paper 2
- CRM_MetaClassical directory with meta-theory components
- Updated LaTeX documentation (paper-v5.tex)
- README and release notes
- Build configuration files

Excluded from archive:
- Build artifacts (`.lake/`, `build/`)
- Work-in-progress files (`WIP/`)
- Test directories
- Archive directories
- System files (`.DS_Store`)

## Notes

- The main equivalence (bidual gap ↔ WLPO) is fully formalized with 0 sorries
- Classical axioms are properly fenced and only used in the Gap → WLPO direction
- The WLPO → Gap direction is fully constructive
- Three optional completeness lemmas remain as WLPO-conditional sorries

## LLM Acknowledgment

Development assisted by:
- Gemini 2.5 Deep Think (architecture brainstorming)
- GPT-5 Pro (Lean scaffolding and refactoring)
- Claude Code (repository management and build scripts)

All final proofs and code were verified by Lean; any LLM-generated suggestions were reviewed and rewritten as needed.