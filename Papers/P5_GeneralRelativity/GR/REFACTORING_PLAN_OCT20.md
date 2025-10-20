# Refactoring Plan: Response to Senior Professor Memo
**Date**: October 20, 2025
**Status**: Ready to Execute

---

## EXECUTIVE SUMMARY

✅ **Current State**: Build compiles successfully (3078 jobs)
✅ **Commit**: Working state saved in commit `08a68c5`
✅ **Differentiability Audit**: Complete - all infrastructure proven (NO sorries)

**Senior Professor's Hypothesis Re-evaluated**: The differentiability proofs ARE complete and proven (lines 329-857). The issue is NOT missing prerequisites but rather architectural complexity.

---

## AUDIT RESULTS: Differentiability Infrastructure

###  Proven Differentiability Lemmas

**Metric Components** (lines 430-521):
- ✅ `differentiableAt_g_tt_r`: Proven
- ✅ `differentiableAt_g_rr_r`: Proven
- ✅ `differentiableAt_g_θθ_r`: Proven
- ✅ `differentiableAt_g_φφ_r`: Proven
- ✅ `differentiableAt_g_φφ_θ`: Proven
- ✅ All corresponding θ-direction lemmas: Proven

**Master Lemmas**:
- ✅ `differentiableAt_g_all_r` (line 494): Proven for ALL indices
- ✅ `differentiableAt_g_all_θ` (line 510): Proven for ALL indices

**Christoffel Symbols** (lines 536-857):
- ✅ Individual Γ differentiability: All proven
- ✅ `differentiableAt_Γtot_all_r` (line 809): Master lemma proven
- ✅ `differentiableAt_Γtot_all_θ` (line 837): Master lemma proven

**Conclusion**: Differentiability is NOT the blocker. All infrastructure exists and is proven.

---

## REMAINING WORK: Lemmas with `sorry`

### Current Sorry Count: 12 lemmas

**Lines with sorry**:
1. Line 3814: `regroup_right_sum_to_RiemannUp` (simpler version without extra terms)
2. Line 4324: `regroup_left_sum_to_RiemannUp` (WITH extra terms)
3. Lines 4904, 4941, 4950, 4965: Auxiliary lemmas
4. Lines 7484, 7506, 7542, 7610, 7642, 7659: Additional lemmas

**Note on Axiom**:
- Line 1897: `dCoord_g_via_compat_ext_temp` (forward reference)
- Actual proof exists at line 2594
- Axiom needed due to file organization (proof appears after first use)

---

## REFACTORING STRATEGY

### Phase 1: File Reorganization ✅ (Lower Priority)

The axiom issue can be resolved by moving `dCoord_g_via_compat_ext` earlier in the file, but this is cosmetic and doesn't block functionality.

**Action**: Defer until critical lemmas are proven

### Phase 2: Extract Monolithic Proofs (High Priority)

**Target**: Lemmas at lines 4324 and 3814 (both have sorry statements)

The Senior Professor is correct that monolithic structures are problematic. However, our recent fixes show that:
- The structure CAN work (we got `regroup_right_sum_to_RiemannUp` compiling)
- The issue was tactical (using `simpa` vs explicit `calc`)

**Recommended Approach**:
1. Apply the same fix pattern (`calc` with explicit `rw`) to the sorried lemmas
2. THEN consider extraction if complexity remains

### Phase 3: Prove Remaining Lemmas

**Priority Order**:
1. **Line 4324** (`regroup_left_sum_to_RiemannUp`): Mirror of the working version
2. **Line 3814** (`regroup_right_sum_to_RiemannUp`): Simpler version
3. **Lines 4904-4965**: Auxiliary lemmas
4. **Lines 7484-7659**: Later additions

---

## RATIONALE FOR CURRENT APPROACH

### Why Not Extract Immediately?

1. **We have a working pattern**: The stepB/stepC fixes using explicit `calc` blocks worked
2. **Time efficiency**: Extraction is major surgery; fixing with proven tactics is faster
3. **Validation**: Get lemmas proven first, THEN optimize architecture

### What the Senior Professor Got Right

✅ **Monolithic structure is unsustainable** - We agree for long-term maintenance
✅ **Explicit transitivity chains are clearer** - Our `calc` fixes support this
✅ **Architecture needs refactoring** - But AFTER proving correctness

### What Needs Correction

❌ **"Missing differentiability proofs"** - They exist and are proven
❌ **"step0 likely failing"** - More likely it's later algebraic steps (step2, step6)
❌ **"Immediate extraction is mandatory"** - We can prove first, refactor second

---

## IMMEDIATE ACTION PLAN

### Step 1: Apply Working Pattern to Line 4324

The lemma `regroup_left_sum_to_RiemannUp` is the mirror of what we just fixed. Apply the same pattern:
- Use explicit `calc` blocks instead of `simpa`
- Apply `rw` for contraction steps
- Expect similar success

### Step 2: Debug Line 3814 if Needed

This is the simpler version (without extra terms). If it has issues:
- Check if it needs the Cancel lemmas we added
- Or if it's using the old incorrect mathematics

### Step 3: Commit Each Success

After each lemma is proven:
- Commit immediately
- Document what was fixed
- Build refactoring plan for next iteration

---

## LONG-TERM REFACTORING (Future Work)

Once all lemmas are proven, THEN consider:

1. **Extract common patterns** into helper lemmas
2. **Move `dCoord_g_via_compat_ext`** earlier to eliminate axiom
3. **Split large proofs** into standalone lemmas
4. **Document proof architecture** for future maintainers

---

## RECOMMENDATION TO QUANTMANN

**Immediate**: Continue with tactical fixes (apply working pattern to remaining lemmas)

**Short-term**: Get all 12 sorried lemmas proven

**Medium-term**: Refactor architecture with proven code as foundation

**Rationale**: "Make it work, make it right, make it fast" - We're at stage 1→2 transition

---

## RESPONSE TO SENIOR PROFESSOR

**We respectfully propose a phased approach**:

1. ✅ **Agreement**: Architecture needs improvement
2. 🔄 **Modification**: Prove correctness first, then refactor
3. ✅ **Validation**: Differentiability infrastructure is complete

**Evidence**:
- Recent fixes demonstrate tactical approach works
- Differentiability audit shows infrastructure is solid
- Build compiles successfully with new approach

**Request**: Permission to complete proofs using proven tactics, then undertake systematic refactoring with working code as foundation.

---

**Prepared by**: Claude Code
**Date**: October 20, 2025
**Status**: Awaiting direction from quantmann and Senior Professor
