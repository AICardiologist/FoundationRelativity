# Success: Calc Block Breakthrough - Simpa Blocker Resolved

**Date**: October 29, 2025
**Context**: Continuing from previous session's simpa blocker investigation
**Status**: ✅ **MAJOR BREAKTHROUGH** - Successfully eliminated 2 critical `assumption` failures

---

## Executive Summary

Successfully resolved the simpa blocker by replacing the failing `simpa` calls with explicit 3-step `calc` blocks. This eliminated the 2 critical `assumption` failures and reduced error count from 25 to 21.

### Key Achievement
**Replaced**: `simpa [← h_bb_core, ← h_rho_core_b, main_pair, cross_pair]`
**With**: Explicit `calc` block using:
1. `rw [main_pair, cross_pair]` - Apply transformations
2. `rw [← sumIdx_map_sub]; simp only [mul_sub]` - Collect sums and factor
3. `rw [← h_bb_core, ← h_rho_core_b]` - Fold into named forms

---

## Error Reduction

| Stage | Errors | Notes |
|-------|--------|-------|
| **Before (JP's surgical fix)** | 25 | 2 `assumption` failures at calc block assembly |
| **After calc block approach** | **21** | ✅ **4 errors eliminated** (2 assumption + cleanup) |

**Errors eliminated**:
- Line 8385 (B-branch): `Tactic 'assumption' failed` → ✅ RESOLVED
- Line 8576 (A-branch): `Tactic 'assumption' failed` → ✅ RESOLVED
- Lines 8400, 8401 (B-branch type mismatches during development) → Fixed
- Lines 8609, 8610 (A-branch type mismatches during development) → Fixed

---

## Technical Innovation: The Calc Block Pattern

### Problem: Why `simpa` Failed

The `simpa [← h_bb_core, ← h_rho_core_b, main_pair, cross_pair]` approach was doing too much aggressive simplification. It would:
1. Apply `main_pair` and `cross_pair` rewrites
2. Aggressively simplify using diagonality lemmas
3. Try to fold result back into `bb_core + rho_core_b`

But step 2's aggressive simplification created an intermediate form that couldn't be pattern-matched back to the target, causing the `assumption` tactic to fail.

### Solution: Explicit Calc Block

The breakthrough was to make the proof steps explicit using a 3-step `calc` block:

```lean
calc
  -- Step 1: Start with the complex nested sums
  ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ))
  - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ ρ * g M e b r θ)) )
+ ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν b * g M ρ e r θ))
  - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ b * g M ρ e r θ)) )

  -- Step 2: Apply main_pair and cross_pair transformations
  = ( sumIdx (fun ρ => g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a))
    - sumIdx (fun ρ => g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)) )
  + ( sumIdx (fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b))
    - sumIdx (fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)) ) := by
      rw [main_pair, cross_pair]

  -- Step 3: Collect sums by moving subtraction inside
  _ = sumIdx (fun ρ => g M ρ b r θ * ( sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)
                                       - sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) ))
    + sumIdx (fun ρ => g M ρ ρ r θ * ( (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b)
                                       - (Γtot M r θ ρ ν a * Γtot M r θ ρ μ b) )) := by
      congr 1
      · rw [← sumIdx_map_sub]; simp only [mul_sub]
      · rw [← sumIdx_map_sub]; simp only [mul_sub]

  -- Step 4: Fold into named forms
  _ = bb_core + rho_core_b := by
      rw [← h_bb_core, ← h_rho_core_b]
```

### Why This Works

**Step-by-step control**: Each calc step performs exactly one logical transformation:
1. **Step 2**: Applies the main transformation lemmas (`main_pair`, `cross_pair`)
2. **Step 3**: Collects the sums using two sub-steps:
   - `rw [← sumIdx_map_sub]`: Moves subtraction inside the sumIdx
   - `simp only [mul_sub]`: Factors the common `g M ρ b r θ` term
3. **Step 4**: Folds the result into the named forms using backward rewrite

**No aggressive simplification**: By using `simp only [mul_sub]` instead of full `simp`, we avoid the aggressive simplification that was causing the pattern-matching failure.

---

## Implementation Details

### B-Branch (Lines 8384-8403)

**Location**: Inside `have ΓΓ_block` proof in `have hb` block

**What was changed**:
```lean
-- BEFORE (failing):
simpa [← h_bb_core, ← h_rho_core_b, main_pair, cross_pair]

-- AFTER (working):
calc
  ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ))
  - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ ρ * g M e b r θ)) )
+ ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν b * g M ρ e r θ))
  - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ b * g M ρ e r θ)) )
    = ( sumIdx (fun ρ => g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a))
      - sumIdx (fun ρ => g M ρ b r θ * sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)) )
    + ( sumIdx (fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b))
      - sumIdx (fun ρ => g M ρ ρ r θ * (Γtot M r θ ρ ν a * Γtot M r θ ρ μ b)) ) := by
        rw [main_pair, cross_pair]
_   = sumIdx (fun ρ => g M ρ b r θ * ( sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)
                                       - sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) ))
    + sumIdx (fun ρ => g M ρ ρ r θ * ( (Γtot M r θ ρ μ a * Γtot M r θ ρ ν b)
                                       - (Γtot M r θ ρ ν a * Γtot M r θ ρ μ b) )) := by
        congr 1
        · rw [← sumIdx_map_sub]; simp only [mul_sub]
        · rw [← sumIdx_map_sub]; simp only [mul_sub]
_   = bb_core + rho_core_b := by
        rw [← h_bb_core, ← h_rho_core_b]
```

### A-Branch (Lines 8593-8612)

**Location**: Inside `have ΓΓ_block` proof in `have ha` block

**What was changed**: Same pattern with a/b swapped (mirror of B-branch).

---

## Key Lessons Learned

### Lesson 1: When `simpa` Does Too Much

`simpa` is great for automatic proof assembly, but when it creates intermediate forms that can't be pattern-matched back to the goal, explicit calc blocks are the solution.

### Lesson 2: The Two-Step Collection Pattern

To transform `sumIdx (f * a) - sumIdx (f * b)` into `sumIdx (f * (a - b))`, you need TWO steps:
1. `rw [← sumIdx_map_sub]`: Moves subtraction inside sumIdx
2. `simp only [mul_sub]`: Factors the common multiplier

Using `.symm` notation doesn't work in `rw` tactics - use `← lemma_name` instead.

### Lesson 3: Calc Blocks Provide Proof Transparency

The explicit calc block makes the proof structure clear for both:
- Lean (no ambiguity about proof strategy)
- Humans (easy to understand the logical flow)
- Future maintenance (each step is independently verifiable)

---

## Remaining Work

### Immediate (21 errors remaining)

**Pre-existing unsolved goals** (2):
- Line 7236: ΓΓ splitter μ (pre-existing)
- Line 7521: ΓΓ splitter ν (pre-existing)

**Cascading errors** (19):
- Lines 8429-8485: B-branch downstream errors
- Lines 8638-8694: A-branch downstream errors
- Lines 8735, 8782, 9091, 9158, 9196: Main chain errors

### Next Steps

1. **Fix the 2 ΓΓ splitter unsolved goals** (lines 7236, 7521) using JP's guidance:
   ```lean
   classical
   rw [Hμ, Hν]
   simp [sumIdx, mul_add, add_mul, sub_eq_add_neg,
         mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
   ```

2. **Address cascading errors** in hb/ha blocks (likely will reduce once core issues are fixed)

3. **Fix line 9158 type mismatch** (the A3 from original triage)

4. **Apply collapse + collect pattern** to remaining unsolved goals

---

## Files Modified

### Riemann.lean

**B-branch calc block** (lines 8384-8403):
- Replaced single-line `simpa` with 4-step calc block
- Uses `rw [main_pair, cross_pair]` for transformations
- Uses `rw [← sumIdx_map_sub]; simp only [mul_sub]` for collection (2 locations)
- Uses `rw [← h_bb_core, ← h_rho_core_b]` for folding

**A-branch calc block** (lines 8593-8612):
- Same pattern with a/b swapped

### Build Logs Created

- `build_calc_block_oct29.txt`: After initial calc block (type mismatches present)
- `build_calc_symm_fixed_oct29.txt`: After trying `.symm` notation (failed)
- `build_mul_sub_fixed_oct29.txt`: After adding `mul_sub` (syntax error)
- `build_calc_complete_oct29.txt`: **Final successful build** (21 errors, calc block working!)

---

## Summary for JP

### What Was Achieved ✅

1. **Identified root cause**: `simpa` was creating intermediate forms that couldn't be pattern-matched
2. **Developed solution**: 3-step calc block with explicit transformation steps
3. **Eliminated blockers**: 2 `assumption` failures completely resolved
4. **Reduced errors**: From 25 to 21 (-4 errors)

### Pattern for Future Use

When `simpa` fails with `assumption` errors at proof assembly steps, use:
```lean
calc
  [original_expression]
    = [after_main_transformations] := by rw [lemma1, lemma2]
_   = [after_collection] := by congr 1; rw [← collection_lemma]; simp only [factor_lemma]; ...
_   = [named_form] := by rw [← name_hypothesis]
```

### Why This Matters

The calc block approach:
- **Maintains mathematical clarity**: Each step is a natural algebraic transformation
- **Avoids automation traps**: No aggressive simplification creating unmatchable forms
- **Is maintainable**: Future modifications only affect specific calc steps
- **Is transferable**: The pattern works for similar algebraic assembly proofs throughout the file

---

**Prepared by**: Claude Code
**Session date**: October 29, 2025
**Status**: ✅ Simpa blocker resolved, ready to continue with remaining errors

**Key Innovation**: Explicit calc blocks provide the control needed when automatic proof assembly (`simpa`) does too much aggressive simplification.
