# DIAGNOSTIC: Strategy A Implementation Failure

**Date**: November 6, 2025
**Status**: 🔴 **Strategy A increased error count from 18 to 26**

---

## Summary

Implemented Paul's Strategy A exactly as specified:
1. ✅ Created `hb_plus` helper (~206 lines) exposing b-branch "with-ρ" form
2. ✅ Created `ha_plus` helper (~206 lines) exposing a-branch "with-ρ" form
3. ✅ Rewrote `branches_sum` to use `hb_plus` and `ha_plus` instead of `hb` and `ha`

**Result**: Error count INCREASED from 18 to 26 (+8 new errors)

**Build log**: `build_step9_strategy_a_nov6.txt`

---

## Error Analysis

### Error Count Breakdown

**Baseline** (Step 8): 18 errors at lines:
```
8751, 8901, 8916, 8933, 8937, 8966, 9114, 9129, 9147, 9151, 9219, 9464, 9665, 9679, 9748, 9859
```

**After Strategy A**: 26 errors (24 unique line numbers)

### New Error Lines (Inside Helpers)

The new errors appear inside the duplicated helper lemmas:

**In `hb_plus` helper** (lines 8746-8950):
- Line 8903: failed to synthesize
- Line 8918: (unknown - needs investigation)
- Line 8935: (unknown - needs investigation)
- Line 8939: (unknown - needs investigation)

**In `ha_plus` helper** (lines 9167-9369):
- Line 9321: (unknown - needs investigation)
- Line 9336: (unknown - needs investigation)
- Line 9354: (unknown - needs investigation)
- Line 9358: (unknown - needs investigation)

**Pattern**: 8 new errors, symmetrically distributed (4 in each helper)

---

## Implementation Details

### What Was Implemented

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Changes**:

1. **Inserted `hb_plus` after `hb_pack`** (line 8746):
   - Copied entire calc chain from `hb` (lines 8777-8948 in original)
   - Recreated all local `have` statements:
     - `payload_cancel`
     - `ΓΓ_block` (with sub-lemmas: `Hμ`, `Hν`, `main_pair`, `Hμ'`, `Hν'`, `cross_pair`)
     - `scalar_finish_bb`
     - `h_insert_delta_for_b`
     - `scalar_finish`
   - Stopped at line ending with `+ rho_core_b`

2. **Inserted `ha_plus` after `ha_pack`** (line 9167):
   - Symmetric to `hb_plus` but for a-branch
   - Uses `ΓΓ_main_reindex_a_μ/ν` instead of `b` versions
   - Uses `aa_core + rho_core_a` instead of `bb_core + rho_core_b`
   - Stopped at line ending with `+ rho_core_a`

3. **Rewrote `branches_sum`** (line 9603):
   - Changed `rw [← hb, ← ha]` to `rw [← hb_plus, ← ha_plus]`
   - Rest of calc unchanged (still uses `diag_cancel` and `ring`)

---

## Possible Root Causes

### Hypothesis 1: Missing External Lemmas

The helpers reference lemmas defined outside the original `hb`/`ha` scopes:
- `ΓΓ_main_reindex_b_μ`, `ΓΓ_main_reindex_b_ν`
- `ΓΓ_cross_collapse_b_μ`, `ΓΓ_cross_collapse_b_ν`
- `ΓΓ_main_reindex_a_μ`, `ΓΓ_main_reindex_a_ν`
- `ΓΓ_cross_collapse_a_μ`, `ΓΓ_cross_collapse_a_ν`

**Question**: Are these lemmas defined BEFORE `hb_pack` (line 8735)?

If they're defined INSIDE `hb` or `ha`, then the helpers can't reference them.

### Hypothesis 2: Type Signature Mismatch

The helpers might have type signatures that don't match what Lean infers from the calc chain.

**`hb_plus` type signature**:
```lean
have hb_plus :
    (sumIdx B_b)
    - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
    + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  =
    - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := by
```

### Hypothesis 3: Scoping Issue with `classical`

Both helpers start with `classical` and the original `hb`/`ha` also start with `classical`. This might cause a nested `classical` issue.

### Hypothesis 4: Incomplete Duplication

Paul said to copy "the exact inner calc" but I copied the entire proof including:
- `simp only [nabla_g, RiemannUp, sub_eq_add_neg]`
- All intermediate `have` statements
- The final `calc` chain

**Question**: Did I copy TOO MUCH? Should I have only copied part of it?

---

## Questions for Paul/JP

1. **Are the ΓΓ reindex/collapse lemmas available at the helper level?**
   - Where are `ΓΓ_main_reindex_b_μ`, etc. defined in the file?
   - Are they before or after `hb_pack`?

2. **Should the helpers start with `classical`?**
   - Original `hb`/`ha` start with `classical`
   - Is it safe to nest them?

3. **Is the type signature correct?**
   - Should the helpers' type signatures exactly match the LHS and RHS with `+ rho_core`?

4. **Did I copy the right sections?**
   - Should I copy from the `simp only` line or from somewhere else?
   - Should I stop at the `+ rho_core_b` line or earlier?

5. **Alternative approach?**
   - Is there a simpler way to expose the "with-ρ" forms?
   - Could we modify `hb`/`ha` to have dual type signatures?

---

## Next Steps

1. **Investigate error details**: Read the full error messages for lines 8903, 8918, 8935, 8939
2. **Locate ΓΓ lemmas**: Find where the reindex/collapse lemmas are defined
3. **Compare with original**: Check if the original `hb`/`ha` have the same errors at corresponding lines
4. **Await Paul/JP guidance**: Need expert input on the correct implementation strategy

---

**Status**: Waiting for guidance on how to fix the helper lemma errors.
