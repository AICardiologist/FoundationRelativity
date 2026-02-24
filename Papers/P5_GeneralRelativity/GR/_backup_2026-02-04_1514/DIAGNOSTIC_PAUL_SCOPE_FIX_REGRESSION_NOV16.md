# Diagnostic Report: Paul's Scope Fix REGRESSED - November 16, 2024

**Status**: ❌ **BUILD FAILS - 16 errors** (+6 from 10-error baseline)
**For**: Paul (Tactic Professor)
**From**: Claude Code
**Date**: November 16, 2024

---

## Executive Summary

Paul's surgical fix to eliminate variable shadowing in the b-branch has **REGRESSED** and made the situation **WORSE**:

- **Before scope fix** (with parenthesization fix): 10 errors
- **After Paul's surgical scope fix**: **16 errors** (+6 errors = REGRESSION)
- **Root cause**: Unknown - need to analyze the specific errors introduced
- **Build status**: **FAILS** ❌

---

## 1. Error Count Progression

| Version | Errors | Change | Notes |
|---------|--------|--------|-------|
| Nov 16 baseline (parenthesization fix) | 10 | - | After fixing `change` tactic |
| **After Paul's scope fix** | **16** | **+6** | **REGRESSION** |

**Net result**: Paul's scope fix introduced 6 **NEW** errors.

---

## 2. What Changed in Paul's Scope Fix

**Location**: `Riemann.lean:8954-8981`

**Changes applied**:

1. **Removed** the inner `let B_b` definition that was shadowing
2. **Replaced** `LHS_regroup` proof to use `ring` for three-sum regrouping
3. **Updated** `Hpack` to work directly with outer `B_b` using `sumIdx_add2_sub`

**Code applied**:
```lean
-- Regroup only the three-Σ expression that appears on the calc LHS.
-- Deterministic: just reassociate A - X + Y to (A + Y) - X.
have LHS_regroup :
  (sumIdx B_b)
  - sumIdx (fun ρ => Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b)
  + sumIdx (fun ρ => Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b)
    =
  (sumIdx B_b
   + sumIdx (fun ρ => Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b))
  - sumIdx (fun ρ => Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b) := by
  ring

-- Package exactly (ΣB_b + ΣG) − ΣF → Σ(B_b + G − F), no AC search:
have Hpack :
  (sumIdx B_b
   + sumIdx (fun ρ => Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b))
  - sumIdx (fun ρ => Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b)
    =
  sumIdx (fun ρ =>
    B_b ρ
    + (Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b)
    - (Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b)) := by
  simpa using
    sumIdx_add2_sub
      (B_b)
      (fun ρ => Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b)
      (fun ρ => Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b)
```

---

## 3. Critical Issue: Unknown WHERE B_b Is Defined

**Problem**: We cannot find where `B_b` is initially defined in the file!

**Search attempts**:
- Searched for `let B_b :=` - **no matches**
- Searched for `B_b := fun` - **no matches**
- Searched for `^\s+B_b\s*:=\s*fun` - **no matches**

**Observation**: The calc block at line 8943 references `(sumIdx B_b)` on the LHS, which means `B_b` **MUST** be defined somewhere earlier in the file, but we cannot locate it.

**Hypothesis**: `B_b` might be:
1. Defined much earlier in the file (before line 8800)
2. Defined with different syntax (e.g., in a `where` clause or pattern match)
3. Inherited from a different scope/context

**Impact**: Without knowing B_b's definition, we cannot diagnose why the scope fix failed.

---

## 4. Suspected Root Causes

### Hypothesis A: Outer B_b Doesn't Exist

**If** there was no outer `B_b` binding before the calc block, then:
- The calc LHS `(sumIdx B_b)` at line 8943 would be **undefined**
- Paul's fix assumes outer `B_b` exists and removes the inner redefinition
- Result: **B_b becomes undefined** → NEW errors

**Evidence needed**: Find where `B_b` is initially bound

---

### Hypothesis B: Type Mismatch Between Outer B_b and Hpack

**If** outer `B_b` exists but has a different structure:
- `Hpack` now tries to use `B_b ρ` inside the sum
- But outer `B_b` might not be a function `ρ → ...`
- Result: Type mismatch errors

**Evidence needed**: Check B_b's type signature

---

### Hypothesis C: simpa Using Still Triggers Recursion

**If** `simpa using sumIdx_add2_sub ...` still brings in AC lemmas:
- Same issue as previous AC-free fix attempt
- Maximum recursion depth errors
- Cascade failures

**Evidence needed**: Check build log for recursion errors

---

## 5. Immediate Next Steps

### Step 1: Locate Outer B_b Definition ⭐ **URGENT**

Search wider range:
```bash
grep -n "B_b" Papers/P5_GeneralRelativity/GR/Riemann.lean | head -100
```

Look for:
- Earlier `let B_b := ...`
- `where B_b := ...` clauses
- Pattern matches introducing `B_b`

---

### Step 2: Extract Full Error Messages from Build Log

```bash
sed -n '/^error: Papers\/P5_GeneralRelativity\/GR\/Riemann.lean:9030:/,/^error:/p' \
  Papers/P5_GeneralRelativity/GR/build_paul_scope_fix_full_nov16.txt | head -100
```

Analyze:
- What type mismatch occurred?
- Are there recursion errors?
- Which proofs failed?

---

### Step 3: Compare Error Lines (10-error vs 16-error builds)

**10-error build errors**:
1. Line 9030:45: Application type mismatch
2. Line 9032:26: unsolved goals
3-10: Pre-existing errors (lines 8796, 9200, 9215, 9233, 9237, 9052, 9278, 9515)

**16-error build errors**: **NEED TO EXTRACT**

**Goal**: Identify which 6 NEW errors were introduced by the scope fix

---

## 6. Rollback Recommendation

Given the regression, consider **reverting** Paul's scope fix and returning to the 10-error state:

```bash
git checkout HEAD -- Papers/P5_GeneralRelativity/GR/Riemann.lean
```

Then re-apply **only** the parenthesization fix (lines 8960-8961) which successfully reduced errors from 15 → 14.

---

## 7. Alternative Approach: Minimal Fix

Instead of removing the inner `let B_b`, try a **minimal bridging fix**:

1. **Keep** the inner `let B_b` definition
2. **Add** an explicit equality proving outer `B_b` = inner `B_b`
3. **Use** that equality to bridge the scope gap

Example:
```lean
-- Prove inner B_b equals the pattern outer calc expects
have B_b_eq : B_b = (outer calc pattern) := by simp [B_b]

-- Use the equality in the chain
exact LHS_regroup.trans ((B_b_eq ▸ Hpack).trans (Hshape.trans Hδ))
```

---

## 8. Questions for Paul

1. **Where is outer `B_b` defined?** We cannot locate it in the file.

2. **What is `B_b`'s type signature?** Is it:
   - `B_b : Idx → ℝ` (function from index to scalar)?
   - `B_b : ℝ` (scalar value)?
   - Something else?

3. **Should we revert the scope fix?** Given the +6 error regression, should we go back to the 10-error state and try a different approach?

4. **Is the outer `B_b` assumption valid?** Does the calc LHS at line 8943 actually reference a pre-existing `B_b`, or was the inner definition the ONLY `B_b`?

---

## 9. Technical Details

### Build Log Locations
- **Full build log**: `Papers/P5_GeneralRelativity/GR/build_paul_scope_fix_full_nov16.txt`
- **Error count**: 16 total

### Code Locations
- **Scope fix applied**: Riemann.lean:8954-8981
- **Calc LHS referencing B_b**: Riemann.lean:8943
- **Transitive chain error**: Riemann.lean:9030

### Previous States
- **Parenthesization fix (10 errors)**: LAST KNOWN GOOD
- **Before parenthesization (15 errors)**: Baseline with `change` tactic failure
- **After scope fix (16 errors)**: **CURRENT STATE** - REGRESSION

---

## 10. Conclusion

Paul's scope fix has **regressed** the error count from 10 to 16 errors. The root cause is unclear without:

1. Knowing where outer `B_b` is defined
2. Seeing the full error messages for the 16 errors
3. Understanding what 6 NEW errors were introduced

**Critical blocker**: Cannot find outer `B_b` definition despite extensive searching.

**Recommended action**:
1. **URGENT**: Locate outer `B_b` definition
2. Extract and analyze all 16 error messages
3. Consider **REVERTING** to the 10-error state if outer `B_b` doesn't exist

---

**Report Completed**: November 16, 2024
**Build Log**: `Papers/P5_GeneralRelativity/GR/build_paul_scope_fix_full_nov16.txt`
**Errors**: 16 total (+6 regression from 10)
**Recommendation**: **INVESTIGATE OUTER B_b DEFINITION URGENTLY**
