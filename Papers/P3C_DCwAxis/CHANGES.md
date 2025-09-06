# CHANGES for Paper 3C

## [1.0.0] - DCω → Baire Calibrator

### Added
- Complete proof skeleton for DCω → Baire (0 sorries)
  - `chain_of_DCω`: Builds indexed chain via state machine
  - `limit_mem`: Diagonal limit hits every dense open
  - Helper lemmas for length, prefix, and digit extraction
- Opaque `BaireNN` token for clean interface separation
- Adapter stub for future mathlib topology integration
- Paste-ready `.future` files for topology binding

### Architecture
- Core mathematical proof independent of topology
- Clean separation: skeleton proven, binding deferred
- Main build stays green with single intentional sorry

### Status
- **Skeleton**: 276 lines, 0 sorries ✅
- **Calibrator**: 1 intentional sorry (awaiting topology)
- **Future**: Paste-ready files close the gap

### Next Steps
When mathlib topology available:
1. Copy `.future` files over stubs
2. Remove final sorry
3. Full axis complete with 0 sorries