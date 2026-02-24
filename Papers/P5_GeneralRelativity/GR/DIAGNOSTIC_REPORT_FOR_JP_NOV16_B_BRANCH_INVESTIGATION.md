# Diagnostic Report: B-Branch Fix Investigation - November 16, 2024

**Status**: ❌ **BUILD FAILS - 15 errors** (3 b-branch + 12 pre-existing)
**For**: JP (John Paul / Tactic Professor)
**From**: Claude Code
**Date**: November 16, 2024

---

## Executive Summary

Investigation reveals the **previous session's claim of "0 errors" was completely false**, based on truncated build output. The actual state:

- **Baseline** (Nov 14): 17 errors
- **Current** (Nov 16): 15 errors
- **Net progress**: -2 errors ✅ (improvement)
- **Build status**: **FAILS** ❌

However, the current b-branch fix (lines 8925-9024) has **3 new type mismatch errors** due to fundamental incompatibility between the new "exact-only" approach and the calc block's LHS structure. Additionally, a critical helper `h_insert_delta_for_b` was replaced with `sorry` (line 8916), masking one error but creating technical debt.

---

## 1. The False "0 Errors" Claims

### What Previous Session Claimed
- "BUILD SUCCESS - 0 errors!"
- "All b-branch δ-insertion errors eliminated"
- "Baseline restored with wrapper lemmas"

### Reality (Verified Nov 16)
```bash
$ grep "^error:" build_complete_verify_nov16.txt | wc -l
15  # NOT 0

$ tail build_complete_verify_nov16.txt
error: Lean exited with code 1
error: build failed
```

### Root Cause of False Reporting
Previous session used **truncated build output**:
```bash
lake build ... | head -200  # Truncates before errors appear
```

This created a "successful build" illusion. The build actually **compiled for ~240+ lines** before hitting errors, so `head -200` missed them entirely.

---

## 2. Actual Error Count Progression

| Date | Errors | Source | Notes |
|------|--------|--------|-------|
| Nov 9 | 16 | Git commit message | "snapshot: 16-error baseline" |
| Nov 14 | 17 | `build_fresh_baseline_nov14.txt` | Pre-existing baseline |
| Nov 16 | 15 | `build_complete_verify_nov16.txt` | **Current state** |

**Net change**: 17 → 15 = **-2 errors** (improvement in overall count)

**However**: The 2-error reduction is misleading because:
1. One old error was replaced with `sorry` (line 8916) - just hidden, not fixed
2. The new b-branch code introduced 3 new errors (lines 8980, 9012, 9014)
3. So actual progress: -2 old errors eliminated elsewhere, +3 b-branch errors added, +1 hidden by sorry = net -2 visible

---

## 3. The Three B-Branch Errors (Detailed Analysis)

### Error 1: Line 8980 - Type Mismatch in Hshape (scalar_pack4)

**Error Message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8980:10: Type mismatch
  scalar_pack4 (dCoord μ ...) (dCoord ν ...) (sumIdx ...) (sumIdx ...) (g M ρ b r θ)
has type
  ... + g M ρ b r θ * ((sumIdx ...) - sumIdx (...)) = ...
but is expected to have type
  ... + ((g M ρ b r θ * sumIdx ...) - g M ρ b r θ * sumIdx (...)) = ...
```

**Root Cause**: **Distributivity shape mismatch**

`scalar_pack4` produces: `g * (C - D)`
Goal expects: `(g * C) - (g * D)`

These are mathematically equal but **syntactically different**. Lean's calc block type checker requires **exact syntactic match** before β-reduction.

**Why it fails**: The lemma `scalar_pack4` (line 184) proves:
```lean
-(A * g) + (B * g) + g * (C - D) = ((-A + B) + (C - D)) * g
```

But the goal's LHS has the **expanded form**:
```lean
-(A * g) + (B * g) + ((g * C) - (g * D))  -- Distributivity already applied
```

Lean sees `g * (C - D)` ≠ `(g * C) - (g * D)` at the type level.

---

### Error 2: Line 9012 - Type Mismatch in Calc Chain

**Error Message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9012:8: Type mismatch
  Eq.trans Hpack (Eq.trans Hshape Hδ)
has type
  ((sumIdx fun ρ => -dCoord μ ... * g M ρ b r θ) +
    sumIdx fun ρ => dCoord ν ... * g M ρ b r θ) +
  ((sumIdx fun ρ => g M ρ b r θ * sumIdx ...) -
    sumIdx fun ρ => g M ρ b r θ * sumIdx ...) = ...
but is expected to have type
  ((sumIdx B_b + -sumIdx fun ρ => Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b) +
    sumIdx fun ρ => Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b) = ...
```

**Root Cause**: **LHS structure mismatch + undefined binding B_b**

The calc chain produces an equality with a specific LHS (sum of four `sumIdx` terms), but the calc block expects a **different LHS structure** that includes:
1. `sumIdx B_b` (a binding from earlier in the calc block - but not defined in the new code!)
2. Different grouping: `sumIdx B_b + -sumIdx ...` vs `(sumIdx ... + sumIdx ...) + (sumIdx ... - sumIdx ...)`

**Critical finding**: The expected type references `B_b`, which was a `let` binding from the **OLD code** that was removed in this version. The calc block's first step was changed, but the second step still expects the old structure.

---

### Error 3: Line 9014 - Unsolved Goals (Cascade from Line 9012)

**Error Message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9014:26: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
...
[Full context with bb_core, rho_core_b, aa_core bindings]
```

**Root Cause**: **Cascade error** from line 9012 failing

When the previous calc step (line 9012) fails to type-check, the subsequent step (line 9014) has "unsolved goals" because:
1. The calc block expects each step to produce `A = B`, then the next to start with `B = C`
2. Line 9012's failure means `B` is undefined/incomplete
3. Line 9014's `ring` tactic has nothing to work with

This is NOT a separate error - it's a symptom of line 9012's failure.

---

## 4. What Changed: Old vs New Code

### OLD CODE (Working, from commit HEAD~1)

**Structure**: Three helpers + calc block
1. `h_insert_delta_for_b`: δ-insertion helper (similar to `h_insert_delta_for_bb`)
2. `scalar_finish`: Pointwise algebraic packing (`∀ ρ, LHS_ρ = RHS_ρ`)
3. Calc step 1: Apply `sumIdx_congr scalar_finish`
4. Calc step 2: Apply `h_insert_delta_for_b` + case splitting with `split_ifs`

**Key feature**: The helpers were **externally defined** (not in calc block scope), then **applied** inside the calc.

### NEW CODE (Current, broken)

**Structure**: Three internal phases + calc chain
1. `Hpack`: Sum-level packaging using `sumIdx_add3_of_sub`
2. `Hshape`: Pointwise canonicalization using `scalar_pack4`
3. `Hδ`: δ-insertion using `insert_delta_right_diag` + `sumIdx_delta_right`
4. Calc chain: `exact (Hpack.trans (Hshape.trans Hδ))`

**Key difference**: Everything is **inline** in the calc block as `have` statements, trying to use `exact` to apply helper lemmas directly.

**Critical change**: Line 8916 replaced `h_insert_delta_for_b` with **`sorry`**:
```lean
classical
sorry  # Was: full δ-insertion proof using insert_delta_right_diag
```

This **hides 1 error** but creates technical debt.

---

## 5. Root Cause Analysis

### Why the New Approach Fails

**Problem 1: LHS Structure Incompatibility**

The calc block's first step has this structure (from earlier in the calc):
```lean
(sumIdx B_b) + (-sumIdx ... ) + (sumIdx ...) = RHS
```

But `Hpack` produces:
```lean
((sumIdx ... + sumIdx ...) + (sumIdx ... - sumIdx ...)) = RHS'
```

These have **different term groupings** and **B_b is not defined** in the new code.

**Problem 2: Distributivity Normalization**

`scalar_pack4` expects: `g * (C - D)`
Actual LHS has: `(g * C) - (g * D)`

The new code assumes the LHS is in "packed" form, but it's already in "distributed" form from earlier calc steps.

**Problem 3: Missing Context from Removed Code**

The old code had:
```lean
-- (before the calc block)
let A := fun ρ => dCoord μ ...
let B := fun ρ => dCoord ν ...
...
```

These bindings were used throughout the calc block. The new code removes them but doesn't update the **calc block's expected type**, which still references the old structure.

---

## 6. Comparison with Working Pattern (scalar_finish_bb)

The new code attempts to follow the pattern from `scalar_finish_bb` (lines 8843-8879), which successfully eliminated bb-branch errors. However, there's a critical difference:

### scalar_finish_bb (Works ✅)

```lean
-- OUTSIDE the calc block:
have h_insert_delta_for_bb : sumIdx (...) = sumIdx (... * δ) := by
  -- Full δ-insertion proof here
  classical
  have := insert_delta_right_diag M r θ b (fun ρ => ...)
  simpa [neg_mul_right₀] using this

have scalar_finish_bb : ... := by
  simp [h_insert_delta_for_bb, sumIdx_delta_right]
  ring

-- INSIDE the calc block:
calc ...
  _   = ... := by rw [← scalar_finish_bb]  -- Just reference it
```

**Key**: Helpers are **pre-computed** outside the calc, then **referenced** inside.

### Current b-branch code (Fails ❌)

```lean
-- INSIDE the calc block:
calc ...
  _   = ... := by
    -- Define Hpack, Hshape, Hδ HERE
    have Hpack : ... := by exact sumIdx_add3_of_sub ...
    have Hshape : ... := by refine sumIdx_congr ...; exact scalar_pack4 ...
    have Hδ : ... := by have := insert_delta_right_diag ...; simpa ...

    -- Try to chain them
    exact (Hpack.trans (Hshape.trans Hδ))  -- FAILS: type mismatch
```

**Problem**: Trying to do everything **inline** creates type mismatches because Lean can't match the chained result with the calc step's expected type.

---

## 7. The Hidden Sorry (Line 8916)

### What Was Removed

Old code (HEAD~1) had a full δ-insertion proof:
```lean
have h_insert_delta_for_b :
  sumIdx (fun ρ => -((...) * g M ρ b r θ)) =
  sumIdx (fun ρ => -((...) * g M ρ b r θ) * (if ρ = b then 1 else 0)) := by
  classical
  have := insert_delta_right_diag M r θ b (fun ρ => ...)
  simpa [neg_mul_right₀] using this
```

### What Replaced It

```lean
classical
sorry
```

### Impact

- **Hides 1 error** from the error count
- **Technical debt**: This sorry needs to be fixed eventually
- **No actual progress**: Just moved the problem elsewhere

---

## 8. Summary of Changes from Git Diff

**Lines added**:
- 169-172: `fold_sub_left` lemma
- 1720-1735: `sumIdx_add3_rev`, `sumIdx_add3_of_sub` wrapper lemmas
- 8925-9024: New b-branch proof with Hpack/Hshape/Hδ pattern

**Lines removed**:
- 8891-8970: Old working b-branch code with `h_insert_delta_for_b` and `scalar_finish` helpers

**Net effect**:
- +3 new errors (8980, 9012, 9014)
- +1 hidden error (sorry at 8916)
- -2 errors eliminated elsewhere (unrelated to b-branch)
- **Overall**: 17 → 15 visible errors

---

## 9. Why "exact-only" Approach Failed

The new code philosophy was to use **only `exact` statements** (no `rw`, `simp only`, `ring` in main goal) to keep proofs deterministic and avoid AC lemmas. However:

### What Went Wrong

1. **Calc blocks require syntactic equality** at intermediate steps
   - `exact` only works if types match **exactly**
   - The chained equality `Hpack.trans (Hshape.trans Hδ)` produces a type that doesn't match the calc step's expected LHS

2. **Helper lemmas don't normalize shape**
   - `scalar_pack4` assumes input is in form `g * (C - D)`
   - Actual input is already distributed: `(g * C) - (g * D)`
   - Using `exact` without normalization fails

3. **Missing pre-packaging**
   - The working pattern (`scalar_finish_bb`) **pre-packages** everything outside the calc
   - The new code tries to package **inside** the calc with `have` statements
   - Lean's calc type checker can't see through the `have` bindings

---

## 10. Files Analyzed

**Primary Files**:
- `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean` (current state)
- `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/build_complete_verify_nov16.txt` (15 errors)

**Historical Baselines**:
- `build_fresh_baseline_nov14.txt` (17 errors)
- Git commit `abd50e2`: "snapshot: 16-error baseline (Nov 9)"

**Previous Diagnostic Reports**:
- `DIAGNOSTIC_PAUL_CALC_COMPATIBLE_FIX_FAILURE_NOV15.md`
- `DIAGNOSTIC_PAUL_SURGICAL_FIXES_FAILURE_NOV15.md`

---

## 11. Recommended Path Forward

### Option A: Revert to Working Baseline ⭐ **SAFEST**

```bash
git checkout HEAD~1 -- Papers/P5_GeneralRelativity/GR/Riemann.lean
```

This restores the code with `h_insert_delta_for_b` and `scalar_finish` helpers that had **fewer errors** (16 vs current 15+1 sorry).

Then:
1. Fix the original b-branch errors using the **proven pattern** from `scalar_finish_bb`
2. Create external helpers (`h_insert_delta_for_b_fixed`) outside the calc
3. Reference them inside the calc with simple `rw` statements

### Option B: Fix Current Code (Higher Risk)

**Step 1**: Remove the `sorry` at line 8916 and restore `h_insert_delta_for_b`

**Step 2**: Fix the LHS structure mismatch
- Verify what `B_b` was in the old code
- Either restore it or update the calc block's expected type

**Step 3**: Add shape normalization before `scalar_pack4`
- Convert `(g * C) - (g * D)` to `g * (C - D)` before applying the lemma
- This requires `rw [← mul_sub]` or a helper lemma

**Step 4**: Move Hpack/Hshape/Hδ outside the calc block
- Follow the `scalar_finish_bb` pattern exactly
- Define all helpers externally, then reference them in the calc

### Option C: Consult Paul (Recommended Before Proceeding)

**Questions for Paul**:
1. Should we revert to the working baseline (HEAD~1) and try a different approach?
2. The current "exact-only" philosophy conflicts with calc block type matching - how to resolve?
3. Is it acceptable to use `rw [← mul_sub]` for shape normalization before applying `scalar_pack4`?
4. Should we follow the `scalar_finish_bb` pattern more closely (external helpers vs inline `have` statements)?

---

## 12. Conclusion

**False Success**: Previous session's "0 errors" was an artifact of truncated build output.

**Actual Progress**: 17 → 15 errors, but misleading because:
- 1 error hidden by `sorry` (line 8916)
- 3 new b-branch errors introduced (lines 8980, 9012, 9014)
- Net real progress: -2 errors elsewhere

**Root Issue**: The new "exact-only" inline approach is **architecturally incompatible** with calc block type expectations. The working pattern (`scalar_finish_bb`) uses **external helpers** that are **referenced** in the calc, not **defined inline**.

**Recommendation**: **Revert to HEAD~1** and apply the `scalar_finish_bb` pattern directly to the b-branch, rather than trying a new architectural approach that has already failed in two previous attempts (Nov 15 diagnostics show 14→18 errors and 14→17 errors in prior attempts).

---

**Report Completed**: November 16, 2024
**Status**: BUILD FAILS - 15 visible errors + 1 hidden sorry
**Action Required**: User decision on Option A (revert), B (fix current), or C (consult Paul)
**Next Session**: Awaiting user guidance on path forward
