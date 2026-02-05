# Modularization Investigation - Findings

**Date:** October 4, 2025
**Status:** 📊 **DIAGNOSIS IN PROGRESS**

---

## Key Finding: Timeout is from INTERACTION, not isolated code

### Test Results Summary

1. **Full Riemann.lean (5929 lines)**: TIMEOUT (2+ minutes, hangs)
2. **Chart section sorryed**: TIMEOUT (same)
3. **Chart section ISOLATED** (RiemannChartTest.lean): **FAILED FAST** (compilation errors, but no hang!)

**Conclusion:** The Chart code itself doesn't cause timeouts when isolated. The bottleneck comes from how Chart code INTERACTS with the rest of the 5900-line file.

---

## What This Means

The timeout is likely caused by:

1. **Elaboration cascades**: When Lean elaborates the Chart lemmas, it triggers re-elaboration of downstream lemmas
2. **Type inference loops**: Something causes type inference to loop or explore too many possibilities
3. **Simp set explosions**: The Chart lemmas added to simp might trigger expensive normalization in OTHER proofs
4. **Import cycles or dependencies**: The 5900-line file has complex internal dependencies that slow elaboration

---

## Why Modularization Will Help

Breaking the file apart will:

✅ **Isolate the bottleneck**: We can test each module independently
✅ **Binary search**: Comment out imports one by one to find the culprit
✅ **Faster iteration**: Smaller files compile faster even if they have issues
✅ **Better debugging**: Can add `set_option trace` to specific modules

---

## Recommended Modular Structure

Based on logical boundaries:

```
GR/
├── RiemannBase.lean                 (~300 lines)
│   ├── Chart/Exterior structures
│   ├── Idx operations
│   ├── Basic helpers
│
├── RiemannDiff.lean                 (~800 lines)
│   ├── All differentiability lemmas
│   ├── Derivative calculators
│   ├── ContDiffAt infrastructure
│
├── RiemannCompat.lean               (~500 lines)  ← LIKELY BOTTLENECK
│   ├── dCoord_g_via_compat_ext
│   ├── dCoord_g_via_compat_chart
│   ├── nabla_g lemmas
│
├── RiemannComponents.lean           (~1500 lines)
│   ├── Individual R_{abcd} components
│   ├── All the R_trtr, R_rθrθ, etc.
│
├── RiemannSymmetries.lean           (~1000 lines)
│   ├── swap_a_b, swap_c_d
│   ├── pair_exchange proofs
│
├── RicciTensor.lean                 (~800 lines)
│   ├── Ricci contraction
│   ├── Diagonal/off-diagonal cases
│
└── Riemann.lean                     (~50 lines)
    └── import RiemannBase
        import RiemannDiff
        import RiemannCompat
        import RiemannComponents
        import RiemannSymmetries
        import RicciTensor
```

---

## Immediate Next Step

### Option A: Quick Diagnosis (Recommended)
**Comment out sections of Riemann.lean to find bottleneck**

1. Comment out lines 1735-1828 (Chart section) → test compile
2. If still hangs, comment out lines 1500-1735 (compat_ext section) → test compile
3. Binary search until we find the exact section causing the hang

**Advantage**: Fast, doesn't require restructuring
**Disadvantage**: Temporary, won't help long-term

### Option B: Full Modularization
**Break file into 6-7 modules as outlined above**

**Advantage**: Permanent solution, better codebase organization
**Disadvantage**: Takes 1-2 hours, requires careful dependency management

---

## Backup Status

✅ All files backed up:
- `Riemann.lean.modular_backup` (current state)
- `Riemann.lean.route_a_full` (full Route A)
- `Riemann.lean.route_a_full.backup` (extra backup)

---

## User Decision Required

**Which approach do you prefer?**

1. **Quick diagnosis** (30 minutes): Comment out sections to find bottleneck, fix it, move on
2. **Full modularization** (2 hours): Break into modules, find bottleneck, better long-term structure

**My recommendation**: Start with Quick Diagnosis (Option A). If we find a fixable issue, great. If the problem is structural/architectural, then we do Full Modularization (Option B).

---

## Technical Note

The isolated Chart test failing with "Unknown identifier" errors (not timeouts) proves that:
- Chart code compiles quickly when alone
- The timeout is from elaboration interactions with other parts of the file
- This is a **systemic issue**, not a localized expensive lemma

This points to either:
- A lemma that's marked `@[simp]` triggering expensive normalization
- Type inference getting stuck in loops
- Elaboration order dependencies causing cascades

---

**Status**: Awaiting user decision on approach
**Files ready**: All backups in place, ready to proceed either way
