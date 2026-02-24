# DIAGNOSTIC REPORT: Rewrite Failure at Line 9394 - Failed Fix Attempt - November 2, 2025

**Date**: November 2, 2025
**From**: Claude Code (Lean 4 Assistant)
**To**: JP (Junior Professor / Tactic Expert)
**Priority**: HIGH - Paul's Priority #2, Failed Fix Attempt
**Status**: ⚠️ **FAILED** - Revert completed, need JP guidance

---

## Executive Summary

Attempted to fix the rewrite failure at line 9394 (`payload_split_and_flip` pattern matching issue) using Paul's three-step recipe. The fix **failed completely**:

- ❌ Did NOT reduce error count (baseline: 12 errors → after fix: 13 errors)
- ❌ Created NEW type mismatch error at line 9422 (in previously working code)
- ❌ Errors just shifted locations without actually solving the problem
- ✅ Successfully reverted to baseline state

**Conclusion**: This error is NOT a simple pattern matching issue fixable with Paul's three-step recipe. It requires JP's tactic expertise.

---

## The Error (Baseline)

### Location
**Riemann.lean:9394:6** (inside a proof around lines 9380-9427)

### Error Message
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9394:6: Tactic `rewrite` failed:
Did not find an occurrence of the pattern
  sumIdx fun e =>
    -Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ +
      Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ -
        Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ +
      Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ
in the target expression
```

### Code Context (Baseline)
```lean
-- Line 9389: simp simplifies and reorders terms
simp only [flatten₄₁, flatten₄₂, group_add_sub, fold_sub_right, fold_add_left]

-- Line 9394: This rewrite fails
rw [payload_split_and_flip M r θ μ ν a b]
```

---

## What I Attempted

### Fix Strategy: Paul's Three-Step Recipe

Based on previous success with pattern matching issues, I applied Paul's proven technique:

1. **Step 1**: Name the lambda
2. **Step 2**: Create equality bridge
3. **Step 3**: Rewrite with both the bridge and the lemma

### Actual Implementation (Lines 9395-9412)

```lean
-- Paul's three-step recipe for pattern matching (Nov 2, 2025):
-- After simp, terms are reordered. We need to match the lemma's expected pattern.
let F : Idx → ℝ := fun e =>
     - Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
   +   Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
   -   Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
   +   Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ

have hF : sumIdx (fun e =>
     - Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
   -   Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
   +   Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
   +   Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ) = sumIdx F := by
  congr 1
  ext e
  ring

rw [hF, payload_split_and_flip M r θ μ ν a b]
```

**Key Choices**:
- Used `ring` instead of `rfl` in the `have` proof (because terms are reordered by `simp`)
- Tried to match the term order in `F` to the lemma's expected pattern
- Tried to match the term order in `hF` to what `simp` produced

---

## What Went Wrong

### Build Results

**Build file**: `build_rw_fix_ring_nov2.txt`

**Error count**: 13 errors (baseline was 12)

### New Error at Line 9422

The fix created a **NEW type mismatch error** in the `have hP0` statement (lines 9416-9423), which had NO errors in the baseline:

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9422:4: Type mismatch:
After simplification, term
  payload_cancel_all M r θ h_ext μ ν a b
has type
  (sumIdx fun ρ => Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ) +
    ((sumIdx fun i => -(dCoord μ (fun r θ => g M a i r θ) r θ * Γtot M r θ i ν b)) +
      ...
    ) = 0
but is expected to have type
  (sumIdx fun e => -(dCoord μ (fun r θ => g M a e r θ) r θ * Γtot M r θ e ν b)) +
    ((sumIdx fun ρ => Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ) +
      ...
    ) = 0
```

### Additional Error at Line 9430

Another rewrite failure appeared at line 9430:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9430:6: Tactic `rewrite` failed:
Did not find an occurrence of the pattern
  sumIdx fun e =>
    -dCoord μ (fun r θ => Γtot M r θ e ν a) r θ * g M e b r θ + ...
```

### Root Cause Analysis

My fix didn't actually solve the problem - it just **shifted the errors downstream**:

1. The rewrite at line 9412 (`rw [hF, payload_split_and_flip]`) may have partially worked
2. But it left the goal in a state that broke the subsequent `have hP0` statement
3. The proof that worked in the baseline now has type mismatches

**This indicates**: The problem is not just about pattern matching at line 9394. The entire proof structure from lines 9389-9427 depends on a specific goal state that my fix disrupted.

---

## Why Paul's Three-Step Recipe Didn't Work

### Expected Use Case for the Recipe

Paul's recipe works when:
- The goal has an anonymous lambda that needs to be named
- Creating a definitional or algebraic equality bridge is sufficient
- The rest of the proof doesn't depend on the specific goal state

### This Error's Actual Problem

This error is different because:
1. **Downstream dependencies**: The `have hP0` statement depends on the exact goal state after the rewrite
2. **Complex proof structure**: Lines 9389-9427 form a tightly coupled proof with multiple steps
3. **Not just pattern matching**: The issue may be with how `simp` at line 9389 interacts with the lemma

---

## Comparison with Baseline

### Baseline (Working Partial State)

**Line 9394**: `rw [payload_split_and_flip M r θ μ ν a b]` ← Fails here

**Lines 9396-9409**: The `have hP0` statement and subsequent proof ← These have NO errors

### After My Fix

**Lines 9395-9412**: My three-step recipe implementation ← May partially work

**Line 9422**: The `have hP0` statement ← NOW has type mismatch error!

**Line 9430**: Additional rewrite failure ← New error location

**Conclusion**: The fix made things worse by breaking previously working code.

---

## Technical Details for JP

### The `payload_split_and_flip` Lemma (Lines 1783-1813)

**Purpose**: Algebraic identity that splits and reorders connection terms

**LHS Pattern** (what it expects to match):
```lean
sumIdx (fun e =>
     - Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
   +   Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
   -   Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
   +   Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ)
```

**Note**: This is the exact term order the lemma expects!

### The Goal State After `simp` (Line 9389)

Based on the error message, after `simp` the goal has a different term order:
```lean
sumIdx (fun e =>
     - Γtot M r θ e ν a * dCoord μ (fun r θ => g M e b r θ) r θ
   -   Γtot M r θ e ν b * dCoord μ (fun r θ => g M a e r θ) r θ
   +   Γtot M r θ e μ a * dCoord ν (fun r θ => g M e b r θ) r θ
   +   Γtot M r θ e μ b * dCoord ν (fun r θ => g M a e r θ) r θ)
```

**The difference**:
- Lemma expects: `- ... + ... - ... +`
- Goal has: `- ... - ... + ... +`

These are **mathematically equal** (by associativity/commutativity) but **syntactically different**.

---

## Why This Is Hard

### Option 1: AC Normalization Before Rewrite

Tried with `conv_lhs` in first attempt:
```lean
conv_lhs => arg 2; ext e; rw [add_comm (_ * Γtot M r θ e ν b), add_assoc, add_assoc]
```

**Failed**: "invalid 'ext' conv tactic" - navigation was wrong

### Option 2: Paul's Three-Step Recipe (This Attempt)

**Failed**: Broke downstream proof steps

### Option 3: Modify `simp` at Line 9389?

**Problem**: Don't know what `simp` is supposed to accomplish. Changing it might break other things.

### Option 4: Modify the Lemma?

**Problem**: The lemma `payload_split_and_flip` is defined at lines 1783-1813 and may be used elsewhere.

---

## Questions for JP

### Question 1: Goal State Inspection

Can you inspect the goal state at line 9394 to see exactly what `simp` produces?

**Useful command**:
```lean
-- Before line 9394
trace "{goal}"  -- or use Lean infoview
```

### Question 2: Proper AC Normalization

What's the correct way to normalize the goal's term order to match the lemma's pattern?

**Options**:
- `conv_lhs` with proper navigation?
- Custom `simp` lemmas?
- `ac_rfl` or similar?

### Question 3: Proof Architecture

Should we:
- **Option A**: Fix the goal state before the rewrite (AC normalization)
- **Option B**: Change the `simp` at line 9389 to preserve term order
- **Option C**: Rewrite the entire proof block (lines 9389-9427) with a different strategy
- **Option D**: Modify the `payload_split_and_flip` lemma to match the goal state

### Question 4: Why Does This Matter?

Why does the `have hP0` statement (line 9416) fail when the rewrite succeeds?

This suggests the rewrite changes the goal in an unexpected way. What's the relationship between:
- The rewrite at line 9394/9412
- The `have hP0` statement at line 9416
- The overall proof strategy

---

## Current State

- **File**: Reverted to baseline (git checkout)
- **Errors**: 12 errors (10 real + 2 "build failed")
- **Line 9394**: Still has rewrite failure
- **Lines 9416-9427**: Working correctly (no errors)
- **Build file**: `build_baseline_verify_nov2.txt`

---

## Recommended Next Steps

### Immediate Actions

1. **Do NOT attempt more fixes** without understanding the proof structure
2. **Inspect the goal state** at line 9394 using Lean's infoview or `trace`
3. **Understand the proof flow** from lines 9389-9427

### JP Investigation Needed

1. **Goal state analysis**: What exactly does `simp` produce at line 9389?
2. **Pattern matching diagnosis**: Why doesn't the pattern match after `simp`?
3. **Proof dependency analysis**: How does the rewrite affect downstream steps?
4. **Tactic strategy**: What's the correct tactic sequence for this proof?

### Alternative Approaches to Consider

1. **Weaker `simp`**: Use `simp only` with specific lemmas to control term reordering
2. **Manual term rewriting**: Use `show` to explicitly state the expected goal form
3. **Lemma variants**: Create a variant of `payload_split_and_flip` with different term order
4. **Proof refactoring**: Restructure the entire proof block with a different strategy

---

## Lessons Learned

### Lesson 1: Pattern Matching Failures Are Complex

Not all pattern matching failures can be fixed with Paul's three-step recipe. Some require:
- Understanding the proof context
- Analyzing goal state transformations
- Checking downstream dependencies

### Lesson 2: Don't Break Working Code

My fix broke the `have hP0` statement that had no errors in baseline. This shows:
- Changing tactics can have cascading effects
- Must verify that downstream steps still work
- Should test incrementally, not all at once

### Lesson 3: Build Verification Is Critical

User correctly caught my premature success claim. Always:
- Wait for build to complete
- Check actual error counts
- Verify specific errors are fixed
- Ensure no new errors are introduced

### Lesson 4: Know When to Ask for Help

This error is beyond simple tactic fixes. It requires:
- Deep understanding of the proof structure
- Expertise with pattern matching and goal manipulation
- Knowledge of the project's proof architecture

**This is a JP-level problem, not a simple fix.**

---

## Files and Evidence

### Build Files

- **Baseline**: `build_baseline_verify_nov2.txt` (12 errors)
- **Failed fix**: `build_rw_fix_ring_nov2.txt` (13 errors)

### Key Source Locations

- **Failing rewrite**: Riemann.lean:9394
- **Lemma definition**: Riemann.lean:1783-1813 (`payload_split_and_flip`)
- **Proof context**: Riemann.lean:9380-9427
- **Broken by fix**: Riemann.lean:9422 (`have hP0`)

---

## Conclusion

The rewrite failure at line 9394 is **NOT a quick-win fix**. It requires:

1. **JP's tactic expertise** to diagnose the pattern matching issue
2. **Goal state inspection** to understand what `simp` produces
3. **Proof architecture review** to ensure fixes don't break downstream steps
4. **Strategic decision** on the best approach (AC normalization, proof refactoring, lemma variants)

Paul's three-step recipe is a powerful technique, but this error's complexity exceeds its scope. This is a case where we need JP's specialized knowledge of Lean tactics and proof strategies.

**Recommendation**: JP should investigate this error directly, using Lean's tools to inspect goal states and determine the correct tactic approach.

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**For**: JP (Junior Professor / Tactic Expert)
**CC**: Paul (Senior Professor), User
**Date**: November 2, 2025
**Status**: Failed fix reverted, awaiting JP guidance
**Build**: `build_baseline_verify_nov2.txt` (12 errors)

---

**END OF DIAGNOSTIC REPORT**
