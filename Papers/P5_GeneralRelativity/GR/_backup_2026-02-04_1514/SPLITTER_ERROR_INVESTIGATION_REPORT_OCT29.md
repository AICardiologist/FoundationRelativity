# Comprehensive Investigation Report: ΓΓ Splitter Errors (Lines 7236, 7521)

**Date**: October 29, 2025
**Status**: ❌ All attempted fixes failed - JP's guidance needed
**Error count baseline**: 21 errors (2 splitter + 19 downstream)

---

## Executive Summary

This report documents **three failed attempts** to fix the 2 "unsolved goals" errors in the `ΓΓ_quartet_split_b` and `ΓΓ_quartet_split_a` lemmas at lines 7236 and 7521. All attempts either maintained the same error count or increased it, indicating a fundamental misunderstanding of the required proof structure.

**Key finding**: The issue is not a simple tactical fix but a structural problem with how the proof attempts to transform between "packed" and "unpacked" algebraic forms.

---

## Error Context

### Location and Description

**Lines 7236 and 7521**: `unsolved goals` errors in the final calc step of splitter lemmas

**Current proof structure** (line 7494 in b-branch, 7741 in a-branch):
```lean
calc
  ( sumIdx (fun ρ => sumIdx (fun e =>
      ((Γtot M r θ ρ μ a * Γtot M r θ e ν ρ)
     - (Γtot M r θ ρ ν a * Γtot M r θ e μ ρ)) * g M e b r θ))
  + sumIdx (fun ρ => sumIdx (fun e =>
      ((Γtot M r θ ρ μ a * Γtot M r θ e ν b)
     - (Γtot M r θ ρ ν a * Γtot M r θ e μ b)) * g M ρ e r θ)) )
      = ( g M b b r θ *
            ( sumIdx (fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
            - sumIdx (fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ) ) )
        + sumIdx (fun ρ =>
            g M ρ ρ r θ *
              ( Γtot M r θ ρ μ a * Γtot M r θ ρ ν b
              - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b )) := by
        simp [first_block, second_block]  -- ❌ FAILS
```

**Build warnings**:
```
warning: This simp argument is unused: first_block
warning: This simp argument is unused: second_block
```

This indicates `simp` cannot find where to apply these hypotheses.

### Available Lemmas

**first_block** (proven at line 7239):
```lean
sumIdx (fun ρ => sumIdx (fun e =>
  ((Γtot M r θ ρ μ a * Γtot M r θ e ν ρ)
 - (Γtot M r θ ρ ν a * Γtot M r θ e μ ρ)) * g M e b r θ))
=
sumIdx (fun ρ =>
  g M b b r θ * (Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
- g M b b r θ * (Γtot M r θ ρ ν a * Γtot M r θ b μ ρ))
```
**Form**: Produces "unpacked" form (g M b b r θ distributed inside sumIdx)

**first_block_packed** (proven at line 7290):
```lean
g M b b r θ *
  ( sumIdx (fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
  - sumIdx (fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ) )
=
sumIdx (fun ρ =>
  g M b b r θ * (Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
- g M b b r θ * (Γtot M r θ ρ ν a * Γtot M r θ b μ ρ))
```
**Form**: Transforms "packed" → "unpacked" (inverse of what we need)

**first_block_aligned** (defined at line 7326):
```lean
-- Same as first_block but with swapped factors inside sums
-- Uses swap₁, swap₂ to reorder products
```

**second_block** (proven at line 7340):
```lean
sumIdx (fun ρ => sumIdx (fun e =>
  ((Γtot M r θ ρ μ a * Γtot M r θ e ν b)
 - (Γtot M r θ ρ ν a * Γtot M r θ e μ b)) * g M ρ e r θ))
=
sumIdx (fun ρ =>
  g M ρ ρ r θ *
    ( Γtot M r θ ρ μ a * Γtot M r θ ρ ν b
    - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b ))
```
**Form**: Already in the form the goal needs (packed)

---

## Attempt 1: Use `first_block_aligned` Instead of `first_block`

**Date**: October 29, 2025 (early session)
**Hypothesis**: Maybe `simp` needs the aligned version with swapped factors

### Changes Made

**Line 7494**:
```lean
-- BEFORE:
simp [first_block, second_block]

-- AFTER:
simp [first_block_aligned, second_block]
```

**Line 7741**: Same change for a-branch

### Result

❌ **FAILED** - Error count: 21 → 23 (+2 errors)

**New errors created**:
- Lines 7236, 7521: Still "unsolved goals" (original errors remain)
- NEW warnings: Both `first_block_aligned` and `second_block` marked as "unused simp arguments"

**Build log**: `build_splitter_aligned_fix_oct29.txt`

### Analysis

The problem is NOT which version of the hypothesis to use. Both `first_block` and `first_block_aligned` produce the same "unused simp arguments" warning, proving that `simp` fundamentally cannot apply these lemmas in the current proof context.

**Reverted**: Yes, with `git checkout`

---

## Attempt 2: Add `first_block_packed.symm` to Explicit `rw`

**Date**: October 29, 2025 (mid session)
**Hypothesis**: Use explicit `rw` with the packing transformation instead of `simp`

### Changes Made

**Line 7494**:
```lean
-- BEFORE:
simp [first_block, second_block]

-- AFTER:
rw [first_block, second_block, first_block_packed.symm]
```

**Line 7741**: Same change for a-branch

**Reasoning**:
- `rw [first_block]` transforms first sumIdx part (produces unpacked form)
- `rw [second_block]` transforms second sumIdx part (already packed)
- `rw [first_block_packed.symm]` converts unpacked → packed form

### Result

❌ **FAILED** - Error count: 21 → 23 (+2 errors)

**Errors**:
- Lines 7236, 7521: Still "unsolved goals" (original errors remain)
- Line 8304: NEW "unsolved goals" (b-branch downstream)
- Line 8514: NEW "unsolved goals" (a-branch downstream)

**Error breakdown** (from build log):
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7236:58: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7521:58: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8304:65: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8514:65: unsolved goals
[...19 more cascading errors...]
```

**Build log**: `build_splitter_rw_fix_oct29.txt`

### Analysis

Adding explicit `rw` steps not only failed to fix the original errors but created NEW downstream errors. This suggests:
1. The transformation sequence is incorrect
2. The resulting goal state after the `rw` steps doesn't match what downstream proofs expect
3. There may be missing intermediate steps or the wrong order of operations

**Reverted**: Yes, with `git checkout`

---

## Attempt 3: Modify `bb_core_reindexed` Lemma (Previous Session)

**Date**: October 28-29, 2025 (documented in earlier reports)
**Hypothesis**: The reindexing lemma statement itself is wrong

### Changes Made

Modified the `bb_core_reindexed` lemma statement at line 7448 to change the expected algebraic form.

### Result

❌ **FAILED** - Error count: 21 → 27 (+6 errors)

Created 6 new type mismatch errors cascading through the proof.

**Reverted**: Yes

---

## Common Pattern Across All Failures

### The Fundamental Issue

All three attempts fail because of a mismatch between:
1. **What `first_block` produces**: "Unpacked" form with `g M b b r θ` distributed inside `sumIdx`
2. **What the goal needs**: "Packed" form with `g M b b r θ` factored outside

**The transformation gap**:
```lean
-- first_block gives us:
sumIdx (fun ρ => g M b b r θ * A - g M b b r θ * B)

-- Goal needs:
g M b b r θ * (sumIdx (fun ρ => A) - sumIdx (fun ρ => B))

-- first_block_packed goes the WRONG direction:
-- It proves: packed → unpacked
-- We need: unpacked → packed (i.e., first_block_packed.symm)
```

### Why `simp` Fails

When `simp [first_block, second_block]` runs:
1. It applies `first_block` to rewrite the first nested sumIdx
2. This produces the unpacked form
3. It applies `second_block` to rewrite the second nested sumIdx
4. Now it has: `unpacked_form + packed_form`
5. But the goal expects: `packed_form + packed_form`
6. `simp` has no way to pack the first term, so it fails with "unused simp arguments"

### Why Explicit `rw` Fails

When `rw [first_block, second_block, first_block_packed.symm]` runs:
1. `rw [first_block]` rewrites first part → unpacked
2. `rw [second_block]` rewrites second part → packed
3. `rw [first_block_packed.symm]` tries to pack the first part
4. BUT: The pattern in `first_block_packed.symm` doesn't match the current goal structure
5. This creates a type mismatch that propagates downstream

---

## Root Cause Analysis

### The Algebraic Challenge

The proof needs to show:
```lean
(nested_sums_A + nested_sums_B) = (packed_A + packed_B)
```

Where:
- `nested_sums_A` transforms to unpacked_A via `first_block`
- `nested_sums_B` transforms to packed_B via `second_block`
- unpacked_A needs to transform to packed_A somehow

**The missing piece**: There's no clean way to go from unpacked_A to packed_A in the current proof structure.

### Why This Is Hard

The transformation `sumIdx (f * A - f * B) = f * (sumIdx A - sumIdx B)` requires:
1. Distributing multiplication: `sumIdx (f*A - f*B) = sumIdx (f*A) - sumIdx (f*B)`
2. Factoring out constant: `sumIdx (f*A) - sumIdx (f*B) = f * sumIdx A - f * sumIdx B`
3. Distributive law: `f * sumIdx A - f * sumIdx B = f * (sumIdx A - sumIdx B)`

But the current lemmas don't provide this path cleanly, and `simp` can't figure it out automatically.

---

## Comparison to Successful ΓΓ_block Proofs

### What Worked in ΓΓ_block (Lines 8384-8403, 8593-8612)

In the previous session, we successfully fixed similar errors in `have ΓΓ_block` proofs using a 3-step calc pattern:

```lean
calc
  -- Original complex expression
  ( sumIdx (fun ρ => ...) - sumIdx (fun ρ => ...) )
+ ( sumIdx (fun ρ => ...) - sumIdx (fun ρ => ...) )

  -- Step 1: COLLAPSE - Apply transformations
  = ( sumIdx (fun ρ => g M ρ b r θ * sumIdx (fun e => ...))
    - sumIdx (fun ρ => g M ρ b r θ * sumIdx (fun e => ...)) )
  + ( sumIdx (fun ρ => g M ρ ρ r θ * (...))
    - sumIdx (fun ρ => g M ρ ρ r θ * (...)) ) := by
      rw [main_pair, cross_pair]

  -- Step 2: COLLECT - Move subtraction inside, factor
  _ = sumIdx (fun ρ => g M ρ b r θ * ( sumIdx ... - sumIdx ... ))
    + sumIdx (fun ρ => g M ρ ρ r θ * ( ... - ... )) := by
      congr 1
      · rw [← sumIdx_map_sub]; simp only [mul_sub]
      · rw [← sumIdx_map_sub]; simp only [mul_sub]

  -- Step 3: FOLD - Fold into named forms
  _ = bb_core + rho_core_b := by
      rw [← h_bb_core, ← h_rho_core_b]
```

**Why this worked**: Each calc step had a clear, single-purpose transformation with controlled tactical application.

### Why Splitters Are Different

The splitter proofs have a nested calc structure:
1. **Outer calc** (lines 7480-7502): Assembles first_block + second_block
2. **first_block calc** (lines 7250-7287): Complex nested transformation with diagonality reductions
3. The outer calc expects to use first_block and second_block, but they produce incompatible forms

The ΓΓ_block proofs had flat structure where all transformations happened in sequence. The splitters have nested structure where inner transformations don't align with outer requirements.

---

## JP's Guidance (From SESSION_REPORT_OCT29_JP_CALC_BREAKTHROUGH.md)

### What JP Suggested

For the ΓΓ splitter goals, JP provided this drop-in pattern:

```lean
have splitter :
  ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ))
  - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ ρ * g M e b r θ)) )
  =
  sumIdx (fun ρ => g M ρ b r θ *
            ( sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)
            - sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) )) := by
  -- Collapse
  rw [Hμ, Hν]
  -- Collect (one outer sum only)
  congr 1
  rw [← sumIdx_map_sub]
  simp only [mul_sub]
```

### Key Constraints

1. **Never put Hμ, Hν inside simpa** - Apply them with `rw` before the simpa/fold step
2. **Avoid `simp [sumIdx, ...]` at goal top-level** - It expands the finite type and destroys the skeleton
3. **Keep steps single-purpose** - So failure location is unambiguous
4. **Use purpose-built collection lemmas**:
   - `sumIdx_map_sub` - move `-` inside a single Σ
   - `sumIdx_sub_same_right` - when right factor matches
5. **If diagonality needed, use it late and explicitly**

### Why I Couldn't Apply This

**Problem**: JP's pattern assumes we have `Hμ` and `Hν` hypotheses that directly transform the goal. But in the current splitter proof:
1. We're in a nested calc block
2. The transformations are already done via `first_block` and `second_block`
3. There's no `Hμ`, `Hν` in scope at line 7494
4. The proof structure is fundamentally different from what JP's pattern expects

---

## Diagnostic Information

### Files Created

1. `build_splitter_aligned_fix_oct29.txt` - Attempt 1 (first_block_aligned)
2. `build_splitter_rw_fix_oct29.txt` - Attempt 2 (rw with packed.symm)
3. Earlier session logs documenting Attempt 3

### Current File State

**Riemann.lean**: Reverted to baseline (21 errors)
- Line 7494: `simp [first_block, second_block]` (original, failing)
- Line 7741: `simp [first_block, second_block]` (original, failing)

### Error State

**21 errors total**:
- 2 "unsolved goals" at lines 7236, 7521 (splitter proofs)
- 19 cascading errors predicted to reduce after splitter fixes

---

## Questions for JP (or Next Investigator)

### Primary Questions

1. **Should the entire `ΓΓ_quartet_split_b/a` lemma proof be restructured?**
   - Replace the nested calc structure with JP's flat 3-step pattern?
   - Define different intermediate hypotheses that produce compatible forms?

2. **Is there a missing helper lemma for unpacked → packed transformation?**
   - Something like `sumIdx_factor_const_from_sub` that does the full transformation in one step?

3. **Are the lemma statements themselves wrong?**
   - Should `bb_core_reindexed` be defined differently?
   - Should `first_block` be proven to produce the packed form directly?

### Specific Tactical Questions

1. **Where should Hμ and Hν come from in the splitter context?**
   - They exist in the ΓΓ_block context but not in the splitter proof
   - Should they be defined at the splitter lemma level?

2. **What is the correct sequence of collection lemmas?**
   - `sumIdx_map_sub` alone doesn't complete the transformation
   - What combination of lemmas bridges unpacked → packed?

3. **Should the proof use `conv` tactics instead?**
   - To surgically target specific subexpressions for transformation?

---

## Recommended Next Steps

### Option A: Wait for JP's Direct Guidance

**Best if**: The proof structure requires deep tactical knowledge that only JP has.

**Action**: Provide JP with:
- This report
- The exact goal state at line 7494
- The definitions of all helper lemmas
- Request for drop-in tactical guidance or restructuring plan

### Option B: Attempt Full Restructuring

**Best if**: We're confident the nested structure is fundamentally wrong.

**Action**:
1. Rewrite `ΓΓ_quartet_split_b` from scratch using JP's 3-step pattern
2. Define Hμ, Hν at the lemma level (not nested inside first_block)
3. Use JP's collapse → collect → fold discipline throughout

**Risk**: High - could create more errors without clear understanding

### Option C: Investigate Helper Lemmas

**Best if**: The missing piece is a single lemma.

**Action**:
1. Search mathlib for lemmas about factoring constants from sums
2. Prove a custom `sumIdx_factor_mul_sub` lemma if needed
3. Try using it in place of first_block_packed.symm

**Risk**: Medium - may not address the fundamental structural issue

---

## Conclusion

After three failed attempts with different approaches:
1. Using aligned hypothesis version (+2 errors)
2. Explicit rw with packing transformation (+2 errors)
3. Modifying lemma statement (+6 errors)

The evidence strongly suggests this is **not a simple tactical fix** but a **fundamental structural issue** with how the proof attempts to compose transformations. The mismatch between unpacked and packed forms cannot be resolved by changing which lemmas are applied or in what order - the proof structure itself may need redesigning.

**File state**: Baseline restored (21 errors)
**Recommendation**: Escalate to JP for structural guidance before attempting further fixes

---

**Prepared by**: Claude Code
**Date**: October 29, 2025
**Status**: ❌ Investigation complete, all fixes failed, awaiting expert guidance
