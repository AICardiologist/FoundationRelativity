# SESSION STATUS: Strategy A Blocked by Recursion Depth

**Date**: November 7, 2025
**Time**: Current session
**Current State**: Blocked - awaiting Paul/JP guidance on repack recursion issue

---

## Progress Summary

### Completed Work

1. ✅ **Implemented Paul's Strategy A** (Nov 6):
   - Created `hb_plus` helper (206 lines) exposing b-branch "with-ρ" form
   - Created `ha_plus` helper (206 lines) exposing a-branch "with-ρ" form
   - Rewrote `branches_sum` to use these helpers with `diag_cancel`

2. ✅ **Applied Paul's first round of fixes** (Nov 6-7):
   - Added `rw [hb_pack]` / `rw [ha_pack]` at start of each helper
   - Removed `RiemannUp` from `simp only` lists
   - Rewrote `branches_sum` to use small algebra lemmas instead of `ring`

3. ✅ **Investigated failure** (Nov 7):
   - Identified recursion depth errors in helpers
   - Analyzed architectural mismatch between packed vs. unpacked forms
   - Created diagnostic report

### Current Blocker

**Problem**: Adding `rw [hb_pack]` causes `HasDistribNeg ℝ + recursion depth` errors in the subsequent `ring` tactics.

**Error count progression**:
- Baseline (Step 8): 18 errors
- After Strategy A (first attempt): 26 errors (+8)
- After Paul's fixes: 29 errors (+11 from baseline)
- Target: 17 errors (-1 from baseline)

**Root cause**: After `rw [hb_pack]`, the LHS transforms from three separate `sumIdx` terms into a single `sumIdx` with a complex integrand. When the calc chain then uses `ring` tactics, they hit recursion depth on the larger term.

---

## The Architectural Issue

### Key Observation

The **original `hb`** (lines 8955-9154) does NOT use `hb_pack`. It starts with:
```lean
have hb :
  (sumIdx B_b) - sumIdx ... + sumIdx ...   -- Three separate sumIdx (unpacked)
  = - sumIdx (fun ρ => RiemannUp ...) := by
  classical
  simp only [nabla_g, RiemannUp, sub_eq_add_neg]   -- Expands unpacked form
  ...
  have payload_cancel : ... := by
    have h : ∀ ρ, ... := by intro ρ; ring   -- ring works fine
```

But **`hb_plus`** (lines 8747-8952) uses `rw [hb_pack]` as Paul instructed:
```lean
have hb_plus :
  (sumIdx B_b) - sumIdx ... + sumIdx ...   -- Same LHS
  = - sumIdx (fun ρ => RiemannUp ...) + rho_core_b := by   -- Different RHS
  classical
  rw [hb_pack]   -- ← Transforms to: sumIdx (fun ρ => B_b ρ - ... + ...)
  simp only [nabla_g, sub_eq_add_neg]   -- Expands PACKED form (large term)
  ...
  have payload_cancel : ... := by
    have h : ∀ ρ, ... := by intro ρ; ring   -- ← FAILS: recursion depth
```

**Question**: Should the helpers use `rw [hb_pack]` at all, given that the calc they copied expects the unpacked form?

---

## Sample Error Details

**Line 8906**: `simpa [neg_mul_right₀] using this`
```
failed to synthesize
  HasDistribNeg ℝ
maximum recursion depth has been reached
```

**Line 8921:33**: Inside `scalar_finish` type signature
```
error: unsolved goals
[Large context with bb_core, rho_core_b, aa_core, rho_core_a, reshape, E, ...]
```
Proof: `intro ρ; ring` ← Fails because `ring` can't handle the large term after repack

---

## Error Distribution

**29 total errors**:

- **Inside `hb_plus`** (lines 8747-8952): 6 errors
  - 8906, 8921, 8927, 8938, 8942, 8960

- **Inside `ha_plus`** (lines 9170-9372): 6 errors
  - 9327, 9342, 9348, 9360, 9364, 9382

- **Outside helpers** (baseline + shifted): 17 errors
  - 9110, 9125, 9142, 9146 (original `hb`)
  - 9530, 9545, 9563, 9567 (original `ha`)
  - 9607, 9612, 9853 (`branches_sum` and nearby)
  - 10054, 10068, 10137, 10248 (downstream)

**Pattern**: 12 new errors in the helpers, plus baseline errors shifted by code additions.

---

## Files Created This Session

### Diagnostic Reports
- `DIAGNOSTIC_STRATEGY_A_FAILURE_NOV6.md`: Analysis of first implementation failure
- `DIAGNOSTIC_REPACK_RECURSION_ISSUE_NOV7.md`: Analysis of repack recursion depth issue (current)

### Build Logs
- `build_step9_strategy_a_nov6.txt`: First attempt (26 errors)
- `build_step9_paul_fixes_nov6.txt`: After Paul's fixes (29 errors, current)

### Session Status
- `SESSION_STATUS_NOV6_STRATEGY_A_BLOCKED.md`: Status after first attempt (obsolete)
- `SESSION_STATUS_NOV7_REPACK_RECURSION_BLOCKER.md`: Current status (this file)

---

## Questions for Paul/JP

**Main Question**: Should the helpers use `rw [hb_pack]` given that the calc they copied expects the unpacked form?

**Context**:
- Paul said: "The first line of each helper must be rw [hb_pack] / rw [ha_pack], to transform the LHS from the splay form the helper declares into the packed pointwise form the ΓΓ-block chain expects."
- But the original `hb` doesn't use `hb_pack` and works fine on the unpacked form.
- Adding `rw [hb_pack]` causes `ring` tactics to hit recursion depth.

**Options**:

1. **Don't use `rw [hb_pack]`**: Just copy the calc as-is since it expects unpacked form.
   - But Paul explicitly said to use it.

2. **Adapt the calc for packed form**: Rewrite ~200 lines of proof to work on packed `sumIdx`.
   - Not clear if feasible or if I'll introduce new errors.

3. **Use a different approach**: Maybe there's a simpler way to expose "with-ρ" forms?

4. **Wait for Paul's clarification**: He anticipated failures and said "If anything still fails after these two changes, paste the exact first failing goal printed inside each helper after you add the rw [*_pack] line."

---

## Next Steps

1. **Await Paul/JP response** to diagnostic report
2. **Implement recommended solution** once guidance is received
3. **Verify error count drops to 17** (target for Step 9)
4. **Continue with remaining Priority errors** (if δ-insertion is resolved)

---

## Key Technical Details

**Baseline**: 18 errors after Step 8 completion
**Target**: 17 errors (eliminate 1 δ-insertion error)
**Current**: 29 errors (+11 from baseline)

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Build log**: `build_step9_paul_fixes_nov6.txt`

**Critical insight**: The `rw [hb_pack]` step transforms the goal in a way that makes subsequent `ring` tactics hit recursion depth. The original `hb`/`ha` don't use `hb_pack` and work fine.

---

**Status**: Session paused, awaiting guidance on whether to use `rw [hb_pack]` and how to handle recursion depth if we do.
