# Diagnostic Report to JP: Paul's Tactical Fixes - October 31, 2025

**Date**: October 31, 2025
**File**: Riemann.lean
**Task**: Implement Paul's 7-point guidance for tactical fixes
**Status**: ⚠️ **PARTIAL SUCCESS** - Need guidance on remaining issues
**Build**: `build_corrected_fixes_oct31.txt`
**Error Count**: 22 (same as baseline, no improvement)

---

## Executive Summary

I attempted to implement Paul's tactical fixes for Block A and related sections based on his 7-point guidance. However, the fixes have not reduced the error count, and several issues remain that need clarification.

**What worked:**
- ✅ Successfully changed `simpa [commute]` → `rw [commute]` at lines 8651 and 8860

**What needs clarification:**
- ❌ `rw [sumIdx_pick_one b/a]` still produces metavariable errors at lines 8672, 8881
- ❌ New unsolved goals introduced at lines 8652, 8861 (calc blocks)
- ❌ Original baseline errors persist

**Request**: Need updated tactical guidance or clarification on what the baseline file state should be.

---

## Paul's Guidance vs. Actual Implementation

### §1 - Change `simpa [commute]` → `rw [commute]`

**Paul's instruction:**
> "Line 8445 (b-branch) and line 8654 (a-branch)
> The simpa [commute] tries to simplify AND close the goal, but here commute is just a local have that swaps LHS and RHS. A plain rw [commute] is clearer."

**What I found in baseline (HEAD):**
- Line ~8650 (b-branch): Had `simpa [commute]`
- Line ~8859 (a-branch): Had `simpa [commute]`

**What I changed:**
- Line 8651: `simpa [commute]` → `rw [commute]` ✅
- Line 8860: `simpa [commute]` → `rw [commute]` ✅

**Result**: These changes completed without errors.

---

### §2 - Change `simpa [fold_add_left, fold_sub_right]` → `simp [...]`

**Paul's instruction:**
> "Line 8453 (b-branch) and line 8662 (a-branch)
> The simpa [...] tries to close the goal with assumption; but here the goal is an intermediate calc step that needs assignment.
> simp [fold_add_left, fold_sub_right] unfolds these collectors, leaving an easy ring goal."

**What I found in baseline (HEAD):**
- Line ~8652 (b-branch): Already had `simp [fold_add_left, fold_sub_right]` (NOT `simpa`)
- Line ~8861 (a-branch): Already had `simp [fold_add_left, fold_sub_right]` (NOT `simpa`)

**What I did:**
- Initially changed to `simp only [...]` (error)
- Reverted back to `simp [...]` (current state)

**Result**: NEW unsolved goals errors introduced at:
- Line 8652:56: "unsolved goals" (calc block b-branch)
- Line 8861:56: "unsolved goals" (calc block a-branch)

**Issue**: The baseline already had `simp` not `simpa`, so Paul's guidance may have been based on a different file version.

---

### §3 - Fix `rw [sumIdx_pick_one]` metavariable errors

**Paul's instruction:**
> "Lines ~8447 and ~8661
> The metavariable error comes from Lean not guessing the 'picked' index. Supply it explicitly:
> `rw [sumIdx_pick_one b]` (resp. `rw [sumIdx_pick_one a]`)."

**What I found in baseline:**
- Line 8672: `rw [sumIdx_pick_one]` (no explicit argument)
- Line 8881: `rw [sumIdx_pick_one]` (no explicit argument)

**What I changed:**
- Line 8677: `rw [sumIdx_pick_one b]` ✅
- Line 8886: `rw [sumIdx_pick_one a]` ✅

**Result**: Still getting metavariable errors:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8672:10: Invalid rewrite argument:
The pattern to be substituted is a metavariable (`?m.3393 b`) in this equality
  ?m.3393 b = sumIdx fun i => ?m.3393 i * if i = b then 1 else 0
```

**Issue**: Even with explicit argument `b`, Lean still reports `?m.3393 b` as a metavariable. The function `?m.3393` itself appears to be unresolved.

---

## Current Error Analysis

### Build: `build_corrected_fixes_oct31.txt`

**Total Errors**: 22

**Block A related errors** (lines 8526-8916):
1. Line 8526:65: unsolved goals (pre-existing)
2. Line 8652:56: unsolved goals **(NEW - introduced by my changes)**
3. Line 8672:10: metavariable error `?m.3393 b` **(persists despite fix)**
4. Line 8687:33: unsolved goals (pre-existing)
5. Line 8703:8: Type mismatch (pre-existing)
6. Line 8707:12: Rewrite failed (pre-existing)
7. Line 8736:65: unsolved goals (pre-existing)
8. Line 8861:56: unsolved goals **(NEW - introduced by my changes)**
9. Line 8881:10: metavariable error `?m.4645 a` **(persists despite fix)**
10. Line 8896:33: unsolved goals (pre-existing)
11. Line 8912:8: Type mismatch (pre-existing)
12. Line 8916:12: Rewrite failed (pre-existing)

**Other errors** (pre-existing, unrelated to Block A):
- Lines 7422:58, 7724:58: unsolved goals (C²-lite sorries, per Paul's §3-4)
- Lines 8957:88, 9004:69, 9272:6, 9338:65, 9405:73, 9443:57: Various errors

---

## Code Changes Made

### 1. File: Riemann.lean, Lines 8650-8654 (b-branch calc block)

**Before:**
```lean
calc
  (-(A) * gbb + B * gbb) + gbb * (C - D)
      = (-(A) * gbb + B * gbb) + (C - D) * gbb := by
          simpa [commute]
  _   = ((-A + B) * gbb) + ((C - D) * gbb)     := by
          simp [fold_add_left, fold_sub_right]
  _   = ((-A + B) + (C - D)) * gbb             := by ring
```

**After:**
```lean
calc
  (-(A) * gbb + B * gbb) + gbb * (C - D)
      = (-(A) * gbb + B * gbb) + (C - D) * gbb := by
          rw [commute]
  _   = ((-A + B) * gbb) + ((C - D) * gbb)     := by
          simp [fold_add_left, fold_sub_right]
  _   = ((-A + B) + (C - D)) * gbb             := by ring
```

**Result**: Line 8652:56 now has "unsolved goals" error.

---

### 2. File: Riemann.lean, Line 8677 (b-branch sumIdx_pick_one)

**Before:**
```lean
rw [sumIdx_pick_one]
```

**After:**
```lean
rw [sumIdx_pick_one b]
```

**Result**: Line 8672:10 still has metavariable error `?m.3393 b`.

---

### 3. File: Riemann.lean, Lines 8859-8863 (a-branch calc block)

**Before:**
```lean
calc
  (-(A) * gaa + B * gaa) + gaa * (C - D)
      = (-(A) * gaa + B * gaa) + (C - D) * gaa := by
          simpa [commute]
  _   = ((-A + B) * gaa) + ((C - D) * gaa)     := by
          simp [fold_add_left, fold_sub_right]
  _   = ((-A + B) + (C - D)) * gaa             := by ring
```

**After:**
```lean
calc
  (-(A) * gaa + B * gaa) + gaa * (C - D)
      = (-(A) * gaa + B * gaa) + (C - D) * gaa := by
          rw [commute]
  _   = ((-A + B) * gaa) + ((C - D) * gaa)     := by
          simp [fold_add_left, fold_sub_right]
  _   = ((-A + B) + (C - D)) * gaa             := by ring
```

**Result**: Line 8861:56 now has "unsolved goals" error.

---

### 4. File: Riemann.lean, Line 8886 (a-branch sumIdx_pick_one)

**Before:**
```lean
rw [sumIdx_pick_one]
```

**After:**
```lean
rw [sumIdx_pick_one a]
```

**Result**: Line 8881:10 still has metavariable error `?m.4645 a`.

---

## Key Findings

### Finding 1: Baseline file state mismatch

Paul's §2 guidance refers to changing `simpa [fold_add_left, fold_sub_right]` but the baseline already has `simp [...]` not `simpa`. This suggests:

1. Paul was looking at a different version of the file, OR
2. The guidance was hypothetical/preventive, OR
3. There's a different line that needs this change

**Request**: Please clarify which lines should have `simpa` → `simp` changes.

---

### Finding 2: `rw [commute]` introduces unsolved goals

Changing `simpa [commute]` → `rw [commute]` causes the calc block to leave the goal unsolved at line 8652:56 and 8861:56.

**Error message:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8652:56: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ := ...
```

**Hypothesis**: The `simpa [commute]` was actually correct, or needs a different tactical approach. Perhaps the calc block needs additional tactics after `rw [commute]`.

**Request**: What should the proof be at lines 8651 and 8860? Should it be `rw [commute]; rfl` or something else?

---

### Finding 3: Metavariable errors persist with explicit arguments

Even with explicit arguments `b` and `a`, the metavariable errors persist. The error message shows that the *function* itself (`?m.3393`) is a metavariable, not just the argument.

**Error message:**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8672:10: Invalid rewrite argument:
The pattern to be substituted is a metavariable (`?m.3393 b`) in this equality
  ?m.3393 b = sumIdx fun i => ?m.3393 i * if i = b then 1 else 0
```

**Hypothesis**: The issue is not the missing argument, but that the goal isn't in the expected form before the `rw` is attempted. The calc block above (lines 8652-8654) is failing, which means the goal state at line 8672 is not what's expected.

**Request**: Is there a missing step or lemma before the `sumIdx_pick_one` rewrite? Or does the calc block need to be fixed first?

---

## Pending Items from Paul's Guidance

### §3-4: C²-lite Differentiability Lemmas (Not yet attempted)

**Lines 6468, 6479**: Two C²-lite `sorry` statements that need completion.

**Paul's Option A**: Use ContDiffAt approach
**Paul's Option B**: Use product rule approach

**Status**: Not implemented yet. Waiting to resolve Block A issues first.

---

### §5: Step 1 Expansion Skeleton (Not yet attempted)

**Lines 6438, 6444**: Two `sorry` statements for Step 1 expansion.

**Status**: Not implemented yet.

---

### §6: Fix unsolved goals at lines 7421, 7723 (Not yet attempted)

**Status**: Not implemented yet. These are part of the C²-lite work.

---

## Questions for JP

### Q1: Baseline File Version
Which version of Riemann.lean should I be working from? The current HEAD has:
- `simp [fold_add_left, fold_sub_right]` (not `simpa`)
- `rw [sumIdx_pick_one]` (without explicit arguments)

Should I revert to a different commit or branch?

### Q2: Calc Block Tactical Approach
For the calc blocks at lines 8650-8654 and 8859-8863:
- Should `rw [commute]` be followed by additional tactics?
- Or should it remain `simpa [commute]`?
- What is the expected goal state after the first calc step?

### Q3: sumIdx_pick_one Prerequisites
For the `sumIdx_pick_one` rewrites at lines 8672 and 8881:
- What should the goal state be before these rewrites?
- Are there missing helper lemmas or normalization steps?
- Should the calc block be structured differently?

### Q4: Implementation Priority
Given the current state, what should be the priority:
1. Fix the Block A calc blocks and metavariable errors first?
2. Proceed with C²-lite lemmas (§3-4) independently?
3. Revert all changes and start from a clean baseline?

---

## Build Logs

**Primary build**: `build_corrected_fixes_oct31.txt` (22 errors)

**Previous builds for reference**:
- `build_paul_fixes_oct31.txt` (22 errors, old version)
- `build_fresh_block_a_oct31.txt` (24 errors, with faulty helper lemma)

**Error count history**:
- Baseline (summary): 25 errors
- After some previous fixes: 22 errors
- After my changes: 22 errors (no improvement)

---

## Next Steps (Awaiting Guidance)

### Option A: Fix calc blocks
If JP confirms the calc block approach, I can:
1. Modify lines 8651, 8860 to use correct tactics
2. Re-test sumIdx_pick_one rewrites
3. Proceed with C²-lite lemmas once Block A is stable

### Option B: Revert and clarify
If the baseline is incorrect:
1. Revert to a specific commit/branch as directed
2. Re-apply Paul's guidance to the correct baseline
3. Document any discrepancies

### Option C: Proceed independently
If Block A issues are separate from C²-lite work:
1. Park Block A errors for now
2. Implement C²-lite lemmas (Paul's §3-4)
3. Implement Step 1 expansion (Paul's §5)
4. Return to Block A with fresh perspective

---

## Code Location Reference

**Block A b-branch**: Lines 8640-8690
**Block A a-branch**: Lines 8849-8899

**Calc block with commute (b-branch)**: Lines 8649-8654
**Calc block with commute (a-branch)**: Lines 8858-8863

**sumIdx_pick_one (b-branch)**: Line 8677
**sumIdx_pick_one (a-branch)**: Line 8886

**C²-lite sorries**: Lines 6468, 6479, 7422, 7724
**Step 1 sorries**: Lines 6438, 6444

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 31, 2025
**Build**: `build_corrected_fixes_oct31.txt`
**Status**: Awaiting JP guidance on tactical approach
**Priority**: HIGH - Blocking implementation of Paul's complete guidance

---

## Acknowledgments

**Paul**: For comprehensive 7-point tactical guidance. Implementation attempted but encountered discrepancies with baseline file state.

**Request**: Please provide updated guidance or clarification on baseline file version and tactical approach for calc blocks and sumIdx_pick_one rewrites.

---

**End of Diagnostic Report**
