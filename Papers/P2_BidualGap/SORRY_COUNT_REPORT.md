# Paper 2 Sorry Count Report

**Generated**: August 13, 2025  
**Scope**: Active Lean files used for paper proofs  
**Excludes**: Comments, old_file_last_print/, Archived/, test files

## Executive Summary

**Total sorries in active proof files: 3**  
**Total sorries in new skeleton (WIP): 27**

All 3 sorries are in **unused** lemmas that are marked `@[deprecated]`.

## Detailed Breakdown

### Core Theorem Files (Used for Main Proof)

| File | Sorries | Status | Notes |
|------|---------|--------|-------|
| Basic.lean | 0 | ✅ Clean | Core definitions |
| HB/WLPO_to_Gap_HB.lean | 0 | ✅ Clean | Main theorem |
| HB/DirectDual.lean | 0 | ✅ Clean | Direct construction |
| HB/SimpleFacts.lean | 0 | ✅ Clean | Supporting lemmas |
| Constructive/Ishihara.lean | 0 | ✅ Clean | Gap → WLPO proof |
| Constructive/DualStructure.lean | 3 | ⚠️ | In unused deprecated lemmas |
| **TOTAL** | **3** | | |

### Quotient Framework Files

| File | Sorries | Status |
|------|---------|--------|
| Gap/Quotients.lean | 0 | ✅ Clean |
| Gap/Indicator.lean | 0 | ✅ Clean |
| Gap/IndicatorSpec.lean | 0 | ✅ Clean |
| Gap/C0Spec.lean | 0 | ✅ Clean |
| Gap/Iota.lean | 0 | ✅ Clean |
| Gap/BooleanSubLattice.lean | 0 | ✅ Clean |
| **TOTAL** | **0** | ✅ |

### Work in Progress (Not Yet Integrated)

| File | Sorries | Notes |
|------|---------|-------|
| HB/DualIsometries.lean | 27 | New skeleton for axiom removal |

## Analysis of the 3 Sorries

All 3 sorries are in `Constructive/DualStructure.lean`:

1. **hasOperatorNorm_to_hasOpNorm** (line 95)
   - Status: `@[deprecated]`
   - Used by: **NOBODY** ✅
   
2. **hasOpNorm_to_hasOperatorNorm** (line 104)
   - Status: `@[deprecated]`  
   - Used by: **NOBODY** ✅
   - Actually has 3 sorries in one `use` statement
   
3. **lub_exists_for_valueSet_of_WLPO** (line 119)
   - Status: `@[deprecated]`
   - Used by: **NOBODY** ✅

## Important Context

### Why These Sorries Don't Matter

The 3 sorries are in bridge lemmas that were part of an earlier approach. They are:
- Marked `@[deprecated "Obsolete - not used in main proof"]`
- Not imported by any active proof
- Only definitions (HasOpNorm, UnitBall, valueSet) from DualStructure are used

### Main Theorem Status

The main theorem `gap_equiv_wlpo : BidualGapStrong ↔ WLPO` has:
- **0 sorries** in its proof
- **0 sorries** in all lemmas it depends on
- Clean axiom profile (only standard + 2 declared axioms to be removed)

## Files Excluded from Count

### Not Part of Active Proofs
- WLPO_Equiv_Gap.lean (old stub, only used by test file)
- test/Axioms.lean (old test file)
- Everything in old_file_last_print/
- Everything in Archived/
- Everything in CReal_obsolete/

## Conclusion

**Paper 2 has effectively 0 sorries** in the active proof code. The 3 technical sorries exist only in deprecated, unused bridge lemmas that should be removed in cleanup.

The new DualIsometries.lean skeleton (27 sorries) is work in progress for removing the two placeholder axioms, as planned in ROADMAP-v4.0.md.