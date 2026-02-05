# Progress Report: Paul's Surgical Fixes - October 31, 2025

**Date**: October 31, 2025
**Task**: Implementing Paul's surgical plan for Block A fixes
**Status**: ⏳ **IN PROGRESS** - Calc blocks fixed, sumIdx_pick_one pending
**Current Build**: `build_scalar_complete_oct31.txt` (running)

---

## Executive Summary

Implementing Paul's detailed surgical fixes for Block A. Successfully completed the calc block fixes using `scalar_pack4`. The `sumIdx_pick_one` metavariable errors require Paul's more complex 5-step recipe and are next.

**Completed:**
- ✅ Added `fold_add_right` helper lemma
- ✅ Replaced calc blocks with `scalar_pack4` approach (both branches)
- ✅ Added missing `this` to close scalar_finish proofs

**In Progress:**
- ⏳ Building to verify calc fixes (23 → ? errors expected)
- ⏳ Awaiting build results to proceed with sumIdx_pick_one fixes

---

## Changes Implemented

### 1. Added fold_add_right Helper Lemma

**Location**: Riemann.lean:168-170 (after `fold_add_left`, before `scalar_pack4`)

```lean
/-- Fold addition on right: a * c + b * c = (a + b) * c -/
@[simp] lemma fold_add_right {a b c : ℝ} : a * c + b * c = (a + b) * c := by
  ring
```

**Why**: Paul explained that `simp [fold_add_left, fold_sub_right]` couldn't convert `(-A)*g + B*g` to `(-A + B)*g` because we only had left-factoring, not right-factoring for addition.

**Status**: ✅ COMPLETE

---

### 2. Fixed Calc Blocks Using scalar_pack4 (b-branch)

**Location**: Riemann.lean:8650-8656

**Before** (failed with "unsolved goals"):
```lean
have commute : gbb * (C - D) = (C - D) * gbb := by ring
-- Deterministic normalization: two folds + final regroup
calc
  (-(A) * gbb + B * gbb) + gbb * (C - D)
      = (-(A) * gbb + B * gbb) + (C - D) * gbb := by
          rw [commute]
  _   = ((-A + B) * gbb) + ((C - D) * gbb)     := by
          simp [fold_add_left, fold_sub_right]  -- LEFT UNSOLVED
  _   = ((-A + B) + (C - D)) * gbb             := by ring
```

**After** (Paul's recommended single-step):
```lean
-- Deterministic normalization: scalar_pack4 handles the entire reshape
have : (-(A) * gbb + B * gbb) + gbb * (C - D)
       = ((-A + B) + (C - D)) * gbb := by
  -- scalar_pack4 is written exactly for this shape
  simpa [mul_comm] using scalar_pack4 A B C D gbb
-- Use the packaged form to complete the goal
this
```

**Why Paul's approach is better**:
- Single step instead of 3-step calc chain
- Uses existing `scalar_pack4` lemma that proves exactly this pattern
- Deterministic, heartbeat-cheap
- No AC search needed

**Status**: ✅ COMPLETE

---

### 3. Fixed Calc Blocks Using scalar_pack4 (a-branch)

**Location**: Riemann.lean:8857-8863

**Same transformation as b-branch**, replacing failed calc with scalar_pack4 approach.

**Status**: ✅ COMPLETE

---

### 4. Added Missing `this` to Close scalar_finish Proofs

**Issue Discovered**: Both `scalar_finish_bb` (line 8642) and `scalar_finish_aa` (line 8849) had "unsolved goals" errors because the `have :` created an intermediate result but never used it to close the goal.

**Fix Applied**:
- Line 8656: Added `this` after the `have :` in b-branch
- Line 8863: Added `this` after the `have :` in a-branch

**Why**: The `have :` proves the equality, but Lean needs explicit instruction to use it (`this`) to complete the outer proof.

**Status**: ✅ COMPLETE

---

## Current Build Status

**Build**: `build_scalar_complete_oct31.txt` (in progress)

**Previous Build**: `build_paul_calc_fixes_oct31.txt`
- Error count: 23 (baseline was 22)
- New errors at 8642:89 and 8847:89 (now fixed with `this`)
- Calc block errors at 8652, 8861 eliminated
- Metavariable errors at 8672, 8877 persist (expected)

**Expected Current Build**:
- Error count: Hoping for 21 (remove 2 scalar_finish errors)
- Remaining: Metavariable errors at sumIdx_pick_one (8672, 8877) + others

---

## Pending: sumIdx_pick_one Metavariable Fixes

**Paul's 5-Step Recipe** (not yet implemented):

### Step 1: Freeze the payload
```lean
set core : Idx → ℝ :=
  (fun ρ =>
     (sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a))
   - (sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a))) with hcore
```

### Step 2: Turn metric into delta and move constants right
```lean
have hδ : ∀ ρ, g M ρ b r θ = (if ρ = b then 1 else 0) * g M b b r θ := by
  intro ρ
  -- diagonal metric: all off-diagonals = 0
  cases ρ <;> cases b <;> simp [g]

have hshape :
  sumIdx (fun ρ => g M ρ b r θ * core ρ)
    = sumIdx (fun ρ => core ρ * (if ρ = b then 1 else 0) * (g M b b r θ)) := by
  classical
  refine sumIdx_congr (fun ρ => ?_)
  simpa [hδ ρ, mul_comm, mul_left_comm, mul_assoc]
```

### Step 3: Pull right constant out
```lean
have hpull :
  sumIdx (fun ρ => core ρ * (if ρ = b then 1 else 0) * (g M b b r θ))
    = (sumIdx (fun ρ => core ρ * (if ρ = b then 1 else 0))) * (g M b b r θ) := by
  simpa [sumIdx_mul_right]
```

### Step 4: Apply pick_one with explicit F and k
```lean
have hpick :
  sumIdx (fun ρ => core ρ * (if ρ = b then 1 else 0)) = core b :=
  sumIdx_pick_one (F := core) (k := b)
```

### Step 5: Assemble
```lean
have :
  sumIdx (fun ρ => g M ρ b r θ * core ρ)
    = core b * (g M b b r θ) := by
  simpa [hpick] using hshape.trans hpull
```

**Status**: ⏳ PENDING (awaiting build results before implementing)

**Why Not Implemented Yet**:
- Want to verify calc fixes reduced error count first
- Need to understand exact goal state from build errors
- May need to adjust recipe based on actual goal structure

---

## Paul's Key Insights

### On Calc Blocks
> "The calc-block 'unsolved goals' at 8652 and 8861: You asked simp [fold_add_left, fold_sub_right] to convert `(-(A) * gbb + B * gbb) + (C - D) * gbb` into `((-A + B) * gbb) + ((C - D) * gbb)`. But you don't have a right‑factoring lemma for addition (only fold_sub_right for subtraction and fold_add_left for left factoring). So simp can't get from (-A)*g + B*g to (-A + B)*g."

**Solution**: Use `scalar_pack4` which handles the entire pattern in one step.

### On sumIdx_pick_one Metavariable Errors
> "The sumIdx_pick_one metavariable errors at 8672 and 8881: The error `Invalid rewrite argument … pattern is a metavariable (\`?m.3393 b\`)` tells you two things:
> 1. You're rewriting in the wrong direction for the current goal shape
> 2. Lean cannot infer what the function F : Idx → ℝ is (hence the metavariable). You must freeze it with a set/let and specify it as (F := core) and (k := b)"

**Solution**: 5-step recipe to freeze core, normalize to delta form, and supply explicit arguments.

### On sumIdx_pick_one Direction
> "Direction matters. In your log, the goal was of the form F b = sumIdx …. If you need to introduce the sum, rewrite with ←hpick or use convert"

---

## Next Steps

### Immediate
1. ⏳ **Wait for build completion** (`build_scalar_complete_oct31.txt`)
2. **Verify error count** (expect 21 or lower)
3. **Examine remaining errors** in Block A (8672, 8877)

### If Calc Fixes Succeed (Expected)
1. **Implement Paul's 5-step recipe** for b-branch (8672)
2. **Implement same for a-branch** (8877)
3. **Build and verify** sumIdx_pick_one fixes
4. **Report results** to Paul (with "next build excerpt for lines 8640–8916")

### If Calc Fixes Have Issues
1. **Diagnose unexpected errors**
2. **Consult Paul** with exact goal states
3. **Iterate on fixes**

---

## Build History

| Build | Errors | Notes |
|-------|--------|-------|
| `build_corrected_fixes_oct31.txt` | 22 | Baseline (reverted bad changes) |
| `build_paul_calc_fixes_oct31.txt` | 23 | Added scalar_pack4, missing `this` |
| `build_scalar_complete_oct31.txt` | ? | Added `this` to close proofs (RUNNING) |

---

## Code Quality Notes

**Heartbeat Safety**: All changes use Paul's recommended deterministic, lightweight tactics:
- `scalar_pack4`: Exact pattern match, no search
- `simpa [mul_comm]`: Minimal simplification
- `ring`: Deterministic ring solver
- No global `simp` with AC lemmas
- No expensive elaboration

**Structure**: Following Paul's modular approach:
- Helper lemmas at top (fold_add_right)
- Intermediate `have :` for clarity
- Explicit closure with `this`
- Clear comments documenting strategy

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 31, 2025
**Status**: Calc fixes complete, awaiting build to proceed with sumIdx_pick_one
**Next Update**: After `build_scalar_complete_oct31.txt` completes

---

**End of Progress Report**
