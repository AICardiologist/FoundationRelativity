# DIAGNOSTIC: Implementation Errors in Paul's Three Surgical Fixes - November 10, 2025

**Status**: ❌ **IMPLEMENTATION FAILED**
**Result**: 14 → 18 errors (regression)
**For**: Paul
**From**: Claude Code

---

## Executive Summary

Attempted to implement Paul's three surgical fixes (A, B, C) to the b-branch calc block. All three fixes were applied to Riemann.lean, but the build resulted in **18 errors** (up from 14 baseline), indicating implementation errors in transcribing or applying the fix snippets.

**Key Finding**: Each of the three fixes introduced new errors, suggesting either:
1. Transcription errors when copying Paul's code snippets
2. Missing context or dependencies in the instructions
3. Interaction effects between the fixes

---

## Build Results Summary

| Metric | Value |
|--------|-------|
| Baseline Errors | 14 |
| Post-Fix Errors | 18 |
| Regression | +4 errors |
| New Errors | 6 (lines 8895, 8922, 8924, 8969, 8998, 9002) |
| Shifted Errors | 12 (a-branch and downstream) |

---

## Error Analysis by Fix

### **Fix A: Remove `[neg_mul_right₀]` from δ-insertion** (lines 8893-8899)

**Implementation**:
```lean
      classical
      -- No arithmetic rewriting; just use the δ-insertion lemma as-is.
      simpa using insert_delta_right_diag M r θ b (fun ρ =>
        - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
            - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
            + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
            - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ))
```

**Error at Line 8895**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8895:6: Type mismatch: After simplification, term
  insert_delta_right_diag M r θ b fun ρ =>
    -((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
          sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a) -
        sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)
 has type
  g M b b r θ *
      ((-sumIdx fun ρ => Γtot M r θ ρ ν a * Γtot M r θ b μ ρ) +
        ((sumIdx fun ρ => Γtot M r θ ρ μ a * Γtot M r θ b ν ρ) -
          (dCoord μ (fun r θ => Γtot M r θ b ν a) r θ - dCoord ν (fun r θ => Γtot M r θ b μ a) r θ))) =
    sumIdx fun ρ =>
      if ρ = b then
        g M b ρ r θ *
          ((-sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν a * Γtot M r θ ρ μ ρ_1) + ... )
      else 0
 but is expected to have type
  sumIdx (fun ρ => ...) = sumIdx (fun ρ => ... * (if ρ = b then 1 else 0))
```

**Root Cause**:
- The `simpa using insert_delta_right_diag...` directly applies the lemma without an intermediate `have` step
- This causes a type mismatch because `insert_delta_right_diag` produces an equation with `if ρ = b then ... else 0` on the RHS, but the goal expects `... * (if ρ = b then 1 else 0)`
- **Possible Fix**: Need intermediate `have := insert_delta_right_diag ...; simpa using this` or restructure the goal

**Severity**: HIGH - Blocks Fix A completely

---

### **Fix C: Replace `intro ρ; ring` with case split** (lines 8915-8928)

**Implementation**:
```lean
              * g M ρ b r θ ) := by
      classical
      intro ρ
      by_cases hb : ρ = b
      · -- Case ρ = b: the inserted δ collapses to 1
        subst hb
        simpa [if_pos rfl, mul_one, one_mul, add_comm, add_left_comm, add_assoc,
               mul_comm, mul_left_comm, mul_assoc]
      · -- Case ρ ≠ b: the inserted δ collapses to 0
        have hb' : ρ ≠ b := hb
        simp [if_neg hb', zero_mul, mul_zero, add_comm, add_left_comm, add_assoc,
              mul_comm, mul_left_comm, mul_assoc]
```

**Error at Line 8922** (case pos):
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8922:8: Tactic `assumption` failed

case pos
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a ρ : Idx
bb_core : ℝ := sumIdx fun ρ_1 => ...
...
```

**Root Cause**:
- The `simpa` tactic at line 8922 (after `subst hb`) is trying to close the goal but fails
- The goal state shows we're in `case pos` (ρ = b) but the proof isn't constructing the right term
- **Possible Issue**: Wrong simp set, or the substitution doesn't align with what the goal expects

**Severity**: HIGH - Case pos branch doesn't close

**Error at Line 8924** (case neg):
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8924:6: unsolved goals
case neg
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
μ ν a b : Idx
bb_core : ℝ :=
  sumIdx fun ρ =>
    g M ρ b r θ *
      ((sumIdx fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) -
       sumIdx fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
h_bb_core : bb_core = ...
```

**Root Cause**:
- The `simp` tactic at line 8924 (case ρ ≠ b) fails to close the goal
- Expected: When `ρ ≠ b`, the `if ρ = b then 1 else 0` collapses to `0`, making entire expression `0`
- **Possible Issue**: The `if_neg` simplification isn't firing, or the simp set doesn't include necessary zero-propagation lemmas

**Severity**: HIGH - Case neg branch doesn't close

---

### **Fix B: h_pack_b construction and calc modification** (lines 8932-8998)

**Implementation Part 1: h_pack_b** (lines 8932-8979):
```lean
    have h_pack_b :
        (sumIdx B_b)
          - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
          + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
      =
        sumIdx (fun ρ =>
          B_b ρ
          - (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)
          + (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b)) := by
      classical
      set A := (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)) with hA
      set C := (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b)) with hC

      -- Step 1: sumIdx_map_sub
      have h_sub : (sumIdx B_b) - sumIdx A = sumIdx (fun ρ => B_b ρ - A ρ) := by
        simpa [hA] using (sumIdx_map_sub B_b A)

      -- Step 2: sumIdx_add_distrib
      have h_add :
          sumIdx (fun ρ => B_b ρ - A ρ) + sumIdx C
          = sumIdx (fun ρ => (B_b ρ - A ρ) + C ρ) := by
        simpa [hC] using (sumIdx_add_distrib (fun ρ => B_b ρ - A ρ) C).symm

      -- Step 3: pointwise re-associate
      have h_paren :
          (fun ρ => (B_b ρ - A ρ) + C ρ)
          = (fun ρ => B_b ρ - A ρ + C ρ) := by
        funext ρ
        simpa [add_assoc]

      -- Stitch steps together
      calc
        (sumIdx B_b) - sumIdx A + sumIdx C
            = sumIdx (fun ρ => B_b ρ - A ρ) + sumIdx C := by simpa [h_sub]
        _   = sumIdx (fun ρ => (B_b ρ - A ρ) + C ρ)   := h_add
        _   = sumIdx (fun ρ => B_b ρ - A ρ + C ρ)     := by
                exact congrArg (fun f : Idx → ℝ => sumIdx f) h_paren
        _   = sumIdx (fun ρ =>
                B_b ρ
                - (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)
                + (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b)) := by
                simpa [hA, hC]
```

**Error at Line 8969**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8969:61: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
```

**Root Cause**:
- The final `simpa [hA, hC]` at line 8969 triggers **maximum recursion depth**
- This is the EXACT problem Paul's fix was supposed to avoid!
- **Critical Discovery**: Even using local lemmas (`sumIdx_map_sub`, `sumIdx_add_distrib`), the final step still hits recursion
- **Possible Issue**: The `simpa [hA, hC]` is unfolding the `set` definitions and re-introducing the subtraction that causes recursion

**Severity**: CRITICAL - Recursion reappears despite Paul's fix

**Implementation Part 2: Modified calc block** (lines 8981-8998):
```lean
    calc
      (sumIdx B_b)
    - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
    + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
        = sumIdx (fun ρ =>
            B_b ρ
            - (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)
            + (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b)) := h_pack_b
      _ = sumIdx (fun ρ =>
              - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
                 - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
                 + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
                 - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) )
               * g M ρ b r θ) := by
        -- Use sumIdx_congr with scalar_finish. Now sub_eq_add_neg is UNDER the binder (safe).
        refine sumIdx_congr ?_
        intro ρ
        simpa [nabla_g, RiemannUp, sub_eq_add_neg] using (scalar_finish ρ)
```

**Error at Line 8998**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8998:8: Type mismatch: After simplification, term
  scalar_finish ρ
 has type
  -(g M b ρ r θ * dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) +
        g M b ρ r θ * dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
      g M b ρ r θ *
        ((sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν a * Γtot M r θ ρ μ ρ_1) +
          -sumIdx fun ρ_1 => Γtot M r θ ρ_1 μ a * Γtot M r θ ρ ν ρ_1) =
    -(g M b ρ r θ *
        ((dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ + -dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ +
            sumIdx fun ρ_1 => Γtot M r θ ρ_1 ν a * Γtot M r θ ρ μ ρ_1) + ...))
 but is expected to have type
  B_b ρ - (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)
    + (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b) =
  -(dCoord μ ...) * g M ρ b r θ
```

**Root Cause**:
- `scalar_finish` proves a different equality than what the calc block expects
- The `simpa [nabla_g, RiemannUp, sub_eq_add_neg]` transformation doesn't align the LHS and RHS correctly
- **Possible Issue**: The definitions of `B_b`, `nabla_g`, `RiemannUp` aren't unfolding in a way that makes `scalar_finish ρ` match the calc goal

**Severity**: HIGH - Calc block's second step breaks

**Error at Line 9002**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9002:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

**Root Cause**:
- Downstream error caused by the failure at line 8998
- The calc block is incomplete, causing subsequent proofs to fail

**Severity**: MEDIUM - Cascading error from line 8998

---

## Errors in a-branch (lines 9179+)

The a-branch has not been modified yet, but shows shifted line numbers and one new error:

**Line 9179**: `failed to synthesize HasDistribNeg ℝ`
- This suggests my b-branch changes somehow affected the a-branch elaboration
- Possible backward propagation effect

---

## Summary of Implementation Issues

### Fix A (δ-insertion)
- **Issue**: Direct `simpa using insert_delta_right_diag...` causes type mismatch
- **Suspected Cause**: Missing intermediate `have` step or incorrect goal structure
- **Fix Attempt Status**: ❌ Failed

### Fix C (case split)
- **Issue**: Both `case pos` and `case neg` branches fail to close
- **Suspected Cause**: Wrong simp sets or missing definitional unfoldings
- **Fix Attempt Status**: ❌ Failed

### Fix B (h_pack_b)
- **Issue 1**: Recursion depth at line 8969 despite using local lemmas
- **Issue 2**: Type mismatch at line 8998 when applying `scalar_finish`
- **Suspected Cause**: `simpa [hA, hC]` re-introduces recursion; `scalar_finish` type doesn't align
- **Fix Attempt Status**: ❌ Failed (critical)

---

## Questions for Paul

### 1. Fix A - Direct simpa

**Q**: Should the δ-insertion use `simpa using insert_delta_right_diag...` directly, or should it be:
```lean
have := insert_delta_right_diag M r θ b (fun ρ => ...)
simpa using this
```

**Context**: Direct application causes type mismatch because the lemma's RHS has `if ρ = b then ... else 0` but goal expects `... * (if ρ = b then 1 else 0)`.

### 2. Fix C - Case split simp sets

**Q**: What should the simp sets be for the two branches?

**Context**:
- `case pos` (ρ = b): After `subst hb`, what definitional unfolds are needed?
- `case neg` (ρ ≠ b): The `if_neg` simplification isn't propagating the `0` multiplication

### 3. Fix B - Recursion at line 8969

**Q**: Why does `simpa [hA, hC]` at line 8969 trigger recursion depth?

**Context**: This is inside `h_pack_b`, which uses only local linearity lemmas. The final step just unfolds `set` definitions to get from:
```lean
sumIdx (fun ρ => B_b ρ - A ρ + C ρ)
```
to:
```lean
sumIdx (fun ρ => B_b ρ - (Γtot...) * (nabla_g...) + (Γtot...) * (nabla_g...))
```

**Hypothesis**: The act of unfolding `A` and `C` re-introduces the subtraction context that triggers HasDistribNeg search?

### 4. Fix B - scalar_finish type mismatch

**Q**: What's the correct way to apply `scalar_finish ρ` in the calc block at line 8998?

**Context**:
- `scalar_finish` has type: `∀ ρ, (expanded LHS) = (collapsed RHS)`
- Calc block expects: `(B_b ρ - A ρ + C ρ) = (collapsed RHS * g M ρ b r θ)`
- The `simpa [nabla_g, RiemannUp, sub_eq_add_neg]` doesn't align these

---

## Recommended Next Steps

### Option 1: Wait for Paul's Corrected Guidance (PREFERRED)
Paul's diagnosis has been accurate. We need:
1. Clarification on Fix A (direct simpa vs intermediate have)
2. Correct simp sets for Fix C
3. Explanation for why Fix B hits recursion at line 8969
4. Guidance on aligning `scalar_finish` type with calc goal

### Option 2: Incremental Debug
Test each fix independently:
1. Apply ONLY Fix A, build, verify no recursion
2. Apply ONLY Fix C, build, verify case split works
3. Apply ONLY Fix B, build, identify exact line causing recursion

### Option 3: Alternative Approach
Consider abandoning the three-fix approach and trying a different structural solution (e.g., rewriting the entire calc block from scratch).

---

## Files Created This Session

1. **`build_paul_surgical_fixes_b_branch_nov10.txt`** - Build log with 18 errors
2. **`DIAGNOSTIC_IMPLEMENTATION_ERRORS_PAUL_FIX_NOV10.md`** - This diagnostic

## Files Referenced

- **`Riemann.lean`** - Main proof file (in modified state with all three fixes applied but broken)
- **`build_helpers_removed_nov10.txt`** - Baseline 14-error build log
- **`VERIFICATION_SNAPSHOT_2025-11-10.md`** - Baseline error index

---

## Current State

- ✅ All three fixes applied to b-branch
- ❌ Build has 18 errors (4 error regression)
- ⏸️ **BLOCKED** awaiting Paul's corrected guidance on implementation errors

---

**Report Time**: November 10, 2025, Post-Build Analysis
**Next**: Await Paul's response on how to correctly implement the three fixes
**Lesson Learned**: Even with explicit fix instructions, implementation details (simp sets, intermediate steps, type alignments) are critical and easy to get wrong

---

## Appendix: Full Error Index

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8895:6: Type mismatch (Fix A)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8922:8: Tactic `assumption` failed (Fix C - case pos)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8924:6: unsolved goals (Fix C - case neg)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8969:61: maximum recursion depth (Fix B - h_pack_b)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8998:8: Type mismatch (Fix B - calc)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9002:12: Tactic `rewrite` failed (cascading from 8998)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8751:65: unsolved goals (baseline - shifted)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9179:6: failed to synthesize HasDistribNeg (a-branch - new!)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9194:33: unsolved goals (a-branch)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9212:8: Type mismatch (a-branch)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9216:12: Tactic `rewrite` failed (a-branch)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9031:65: unsolved goals (baseline - shifted)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9257:88: unsolved goals (baseline - shifted)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9494:15: Type mismatch (baseline - shifted)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9695:4: Type mismatch (baseline - shifted)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9709:6: Tactic `rewrite` failed (baseline - shifted)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9778:65: unsolved goals (baseline - shifted)
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9889:57: unsolved goals (baseline - shifted)
```
