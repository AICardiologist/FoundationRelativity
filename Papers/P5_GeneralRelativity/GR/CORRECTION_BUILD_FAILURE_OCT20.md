# ❌ BUILD FAILURE: Corrected Lemma Implementation
**Date**: October 20, 2025
**Status**: **PARTIAL SUCCESS - BUILD FAILED** ⚠️

---

## EXECUTIVE SUMMARY

**Implemented all corrections from JP's plan, but build failed** due to tactical issues in the `Cancel_right_r_expanded` and `Cancel_right_θ_expanded` lemmas.

**What Succeeded**:
- ✅ `ExtraRight_r` and `ExtraRight_θ` definitions inserted (lines 2914-2920)
- ✅ `g_times_RiemannBody_comm` helper lemma inserted and compiling (lines 4010-4022)
- ✅ Corrected `regroup_right_sum_to_RiemannUp` statement inserted (lines 4027-4156)

**What Failed**:
- ❌ `Cancel_right_r_expanded` lemma (lines 2924-3016) - compilation errors
- ❌ `Cancel_right_θ_expanded` lemma (lines 3020-3107) - compilation errors
- ❌ Overall build fails

---

## BUILD ERRORS

### Error 1: Line 2977 - Unknown identifier `sumIdx_mul_right`

**Location**: `Cancel_right_r_expanded`, in proof of `second_is_Extra`

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2977:18: Unknown identifier `sumIdx_mul_right`
```

**Context** (lines 2976-2977):
```lean
simp [mul_add, add_mul, sumIdx_add, sumIdx_mul_left,
      sumIdx_mul_right, mul_comm, mul_left_comm, mul_assoc]
```

**Root Cause**: JP's template code references `sumIdx_mul_right`, but this lemma doesn't exist in the codebase.

**Actual Available Lemmas** (from Riemann.lean):
- Line 2181: `sumIdx_mul_g_right` - contracts with metric
- Line 2190: `sumIdx_mul_g_left` - contracts with metric
- Line 2213: `sumIdx_mul_g_left_comm` - commutativity variant

**Issue**: JP's code assumes general `sumIdx_mul_left/right` lemmas exist, but the codebase only has **metric-specific** contraction lemmas `sumIdx_mul_g_left/right`.

---

### Error 2: Line 2960 - `sumIdx_congr` unification failure

**Location**: `Cancel_right_r_expanded`, in proof of `LHS_expanded`

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2960:4: Tactic `apply` failed: could not unify the conclusion of `@sumIdx_congr`
  sumIdx ?f = sumIdx ?g
with the goal
  (sumIdx fun k => Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ) =
    (sumIdx fun k => Γtot M r θ k Idx.θ a * sumIdx fun lam => Γtot M r θ lam Idx.r k * g M lam b r θ) +
      sumIdx fun k => Γtot M r θ k Idx.θ a * sumIdx fun lam => Γtot M r θ lam Idx.r b * g M k lam r θ
```

**Context** (lines 2959-2961):
```lean
-- pointwise compat + distribute
apply sumIdx_congr; intro k
simp [compat_r k, mul_add]
```

**Issue**: The goal has a **sum on LHS** equal to a **sum of two sums on RHS**. `sumIdx_congr` expects `sumIdx f = sumIdx g` (single sum on each side), but we have:
- LHS: `sumIdx (fun k => ...)`
- RHS: `sumIdx (...) + sumIdx (...)`

This requires `funext` + rewriting, not `sumIdx_congr`.

---

### Error 3: Line 2983 - Nested `sumIdx_congr` unification failure

**Location**: `Cancel_right_r_expanded`, in proof of `second_is_Extra` calc chain

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2983:12: Tactic `apply` failed: could not unify the conclusion of `@sumIdx_congr`
  sumIdx ?f = sumIdx ?g
with the goal
  (Γtot M r θ lam Idx.r b * sumIdx fun k => Γtot M r θ k Idx.θ a * g M k lam r θ) =
    Γtot M r θ lam Idx.r b * sumIdx fun ρ => g M lam ρ r θ * Γtot M r θ ρ Idx.θ a
```

**Context** (lines 2982-2985):
```lean
apply sumIdx_congr; intro lam
apply sumIdx_congr; intro k
-- use g_symm to flip indices on g
simp [mul_comm, mul_left_comm, mul_assoc, g_symm]
```

**Issue**: After the first `sumIdx_congr`, we're inside a pointwise equality. The second `apply sumIdx_congr` is trying to prove:
- LHS function body: `Γtot ... * sumIdx (fun k => ...)`
- RHS function body: `Γtot ... * sumIdx (fun ρ => ...)`

But the goal shows **an equality with Γ scaled outside the sum**, which can't be directly attacked with `sumIdx_congr` (which expects the outer structure to already be `sumIdx f = sumIdx g`).

**Correct Pattern Needed**: Use `congr_arg₂` or `congrArg` to handle the multiplication by `Γtot ... lam Idx.r b` **before** trying to apply pointwise reasoning to the inner sums.

---

### Error 4: Line 3003 - Missing `sumIdx_mul_right` again

**Location**: `Cancel_right_r_expanded`, in proof of `first_to_M`

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:3003:76: Unknown identifier `sumIdx_mul_right`
```

**Context** (line 3003):
```lean
simpa [mul_comm, mul_left_comm, mul_assoc, sumIdx_add, sumIdx_mul_left, sumIdx_mul_right]
     using this.symm
```

**Same Issue**: References non-existent `sumIdx_mul_right`.

---

### Error 5: Similar failures in `Cancel_right_θ_expanded`

The `Cancel_right_θ_expanded` lemma (lines 3020-3107) has the **exact same structural issues** as `Cancel_right_r_expanded` - it's a mirror copy with r ↔ θ swapped.

---

## ROOT CAUSE ANALYSIS

### Issue 1: Missing General Sum Manipulation Lemmas

JP's code assumes the existence of **general lemmas** for factoring constants out of sums:
- `sumIdx_mul_left`: `sumIdx (fun i => c * f i) = c * sumIdx f`
- `sumIdx_mul_right`: `sumIdx (fun i => f i * c) = (sumIdx f) * c`

**Reality**: The codebase only has **metric-specific contraction lemmas**:
- `sumIdx_mul_g_left`: `sumIdx (fun k => g M a k r θ * F k) = g M a a r θ * F a` (contracts index)
- `sumIdx_mul_g_right`: `sumIdx (fun k => F k * g M k b r θ) = g M b b r θ * F b` (contracts index)

These are **not** general constant-factoring lemmas - they perform **metric contraction** (Einstein summation).

**What's Needed**:
Either:
1. **Add general sum manipulation lemmas** to the infrastructure
2. **Rewrite the Cancel lemma proofs** using only existing lemmas

---

### Issue 2: Incorrect Tactic for Sum-Level Equality

JP's code pattern:
```lean
apply sumIdx_congr; intro k
simp [compat_r k, mul_add]
```

**Problem**: This tries to prove `sumIdx f = sumIdx g1 + sumIdx g2` by pointwise reasoning, but `sumIdx_congr` only handles `sumIdx f = sumIdx g`.

**Correct Pattern** (used successfully elsewhere in Riemann.lean):
```lean
have := sumIdx_congr_then_fold (by funext k; simp [compat_r k, mul_add])
-- or direct calc chain with explicit .trans steps
```

---

### Issue 3: Nested Structural Mismatch

JP's code:
```lean
apply sumIdx_congr; intro lam
apply sumIdx_congr; intro k
```

**Problem**: After the first `sumIdx_congr`, we're **inside a function body** `fun lam => (Γtot ... lam ...) * sumIdx (...)`.  The second `apply sumIdx_congr` fails because the goal isn't in the form `sumIdx f = sumIdx g` - it has the Γtot factor outside.

**Correct Pattern**:
```lean
apply sumIdx_congr; intro lam
congr 1  -- handle the multiplication by Γtot
ext k    -- now we're inside the inner sum
simp [g_symm, mul_comm]
```

---

## WHAT JP'S CODE TEMPLATE ATTEMPTED

JP provided a **strategic sketch** of the proof structure:

**Goal**: Prove `Σ_k Γ^k_{θa} (∂_r g_{kb}) = M_r + ExtraRight_r`

**Strategy**:
1. **Step 1**: Expand `∂_r g_{kb}` using metric compatibility into two branches (T1 + T2)
2. **Step 2**: Identify T2 as `ExtraRight_r` via Γ₁ recognition and index swapping
3. **Step 3**: Identify T1 as `M_r` using existing lemma `Riemann_via_Γ₁_Cancel_r`

This strategy is **mathematically correct**, but the **tactical implementation** has the issues described above.

---

## FILES MODIFIED (SO FAR)

### /Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean

**Lines 2914-2920**: ✅ `ExtraRight_r` and `ExtraRight_θ` definitions (COMPILING)
```lean
noncomputable def ExtraRight_r (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun lam => Γtot M r θ lam Idx.r b * Γ₁ M r θ lam a Idx.θ)

noncomputable def ExtraRight_θ (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun lam => Γtot M r θ lam Idx.θ b * Γ₁ M r θ lam a Idx.r)
```

**Lines 2924-3016**: ❌ `Cancel_right_r_expanded` lemma (FAILING)
- Errors at lines 2960, 2977, 2983, 3003
- Strategic structure is correct, tactical execution has issues

**Lines 3020-3107**: ❌ `Cancel_right_θ_expanded` lemma (FAILING)
- Mirror of Cancel_right_r_expanded with same issues

**Lines 4010-4022**: ✅ `g_times_RiemannBody_comm` helper (COMPILING)
```lean
@[simp] lemma g_times_RiemannBody_comm
    (M r θ : ℝ) (k a b : Idx) :
  g M k b r θ *
    ( dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
    + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
    - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a) )
  =
  RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ := by
  unfold RiemannUp
  ring
```
**Status**: Perfect - compiles cleanly, solves the "tactical blocker" from the false lemma.

**Lines 4027-4156**: ✅ Corrected `regroup_right_sum_to_RiemannUp` (STATEMENT CORRECT, DEPENDS ON CANCEL LEMMAS)
```lean
lemma regroup_right_sum_to_RiemannUp
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) (a b : Idx) :
  sumIdx (fun k => ...)
  =
  g M b b r θ * RiemannUp M r θ b a Idx.r Idx.θ
  + (ExtraRight_r M r θ a b - ExtraRight_θ M r θ a b) := by
  classical
  -- Step 1 (SΓ): Expand ∂g using metric compatibility (both branches)
  have SΓ := ... [uses Cancel_right_r/θ_expanded lemmas]
  -- Step 2 (Sg): Contract metric
  have Sg := ...
  -- Step 3 (E3): Fold RiemannBody into RiemannUp
  have E3 := ... [uses g_times_RiemannBody_comm]
  -- Chain together
  calc ...
```
**Status**: Statement is mathematically correct. Proof skeleton is clean. **Blocked** by failures in `Cancel_right_r/θ_expanded`.

---

## TACTICAL OPTIONS FOR JP

### Option 1: Add Missing General Infrastructure Lemmas

**Add to Riemann.lean** (or to a SumUtils.lean if you prefer):
```lean
lemma sumIdx_mul_left (c : ℝ) (F : Idx → ℝ) :
  sumIdx (fun i => c * F i) = c * sumIdx F := by
  simp [sumIdx_expand]
  ring

lemma sumIdx_mul_right (F : Idx → ℝ) (c : ℝ) :
  sumIdx (fun i => F i * c) = (sumIdx F) * c := by
  simp [sumIdx_expand]
  ring
```

**Then** fix the `Cancel_right_r/θ_expanded` proofs using these lemmas.

---

### Option 2: Rewrite Cancel Lemmas Using Only Existing Infrastructure

Rewrite the proofs without relying on non-existent lemmas. Use:
- `sumIdx_congr_then_fold` instead of `apply sumIdx_congr`
- Direct calc chains with `.trans`
- `funext` + `congr` + `ext` pattern for nested equalities
- Existing lemmas like `Riemann_via_Γ₁_Cancel_r/θ` more directly

**Example fix for LHS_expanded**:
```lean
have LHS_expanded :
  sumIdx (fun k => Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ)
  = ...
  := by
  refine sumIdx_congr_then_fold ?_
  funext k
  simp [compat_r k, mul_add]
```

---

### Option 3: Simplify Strategy Using Existing `Riemann_via_Γ₁_Cancel_r/θ` Directly

**Observation**: The existing lemmas `Riemann_via_Γ₁_Cancel_r` and `Riemann_via_Γ₁_Cancel_θ` (lines 3762, 3801) may already encode the needed relationships, just not in the "expanded" form.

**Alternative**: Instead of proving `Cancel_right_r/θ_expanded` from scratch, **derive them as corollaries** of the existing Cancel lemmas by:
1. Starting from `Riemann_via_Γ₁_Cancel_r`
2. Expanding metric compatibility on one side
3. Isolating the extra term

This might avoid the tactical complexity entirely.

---

### Option 4: Use `sorry` Placeholders for Cancel Lemmas, Document as TODO

If time is limited:
1. Replace the failing proofs in `Cancel_right_r/θ_expanded` with `sorry`
2. Add clear `-- TODO (JP): Prove using ...` comments
3. Verify that the **corrected statement** of `regroup_right_sum_to_RiemannUp` compiles modulo the sorried Cancel lemmas
4. Return to prove the Cancel lemmas once infrastructure is clarified

This would allow:
- ✅ Verification that the **mathematical correction** is complete
- ✅ Confirmation that `g_times_RiemannBody_comm` solves the tactical blocker
- ✅ Green build (with known, isolated sorries)

---

## RECOMMENDED IMMEDIATE ACTION

**For this session**:

**Option 4** (sorry placeholders) is the fastest path to:
1. Confirm the mathematical correction is complete
2. Get a clean build
3. Document exactly what remains to prove

**Implementation**:
1. Replace lines 2936-3016 (`Cancel_right_r_expanded` proof) with `sorry`
2. Replace lines 3036-3107 (`Cancel_right_θ_expanded` proof) with `sorry`
3. Build and verify
4. Document this in a follow-up memo to JP

**For follow-up**:

JP should decide:
- **Option 1**: Add `sumIdx_mul_left/right` infrastructure lemmas
- **Option 2**: Rewrite Cancel proofs using existing patterns
- **Option 3**: Derive Cancel_expanded as corollaries of existing Cancel lemmas

---

## CURRENT BUILD STATUS

**Command Run**:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Result**:
```
error: Lean exited with code 1
Some required targets logged failures:
- Papers.P5_GeneralRelativity.GR.Riemann
error: build failed
```

**Error Count**: 5+ errors, all in `Cancel_right_r/θ_expanded` lemmas

**Sorries**:
- Not yet counted (build fails before completion)
- Expected: Same as before (27) plus 2 new ones if we sorry the Cancel lemmas

---

## CONFIDENCE ASSESSMENT

**Confidence in Mathematical Correction**: **Very High** ✅
- The corrected statement of `regroup_right_sum_to_RiemannUp` is mathematically correct
- Senior Professor's analysis validated
- Extra terms `ExtraRight_r - ExtraRight_θ` properly defined
- `g_times_RiemannBody_comm` solves the tactical blocker cleanly

**Confidence in Tactical Implementation**: **Medium** ⚠️
- JP's code template has the right **strategy**
- Tactical execution needs adjustment for this codebase's lemma inventory
- Infrastructure gaps (`sumIdx_mul_left/right`) need resolution

**Confidence in Quick Fix (Option 4)**: **Very High** ✅
- Sorrying the two Cancel lemmas will allow immediate build success
- This isolates the remaining proof obligations clearly
- Allows verification that the mathematical correction is complete

---

## NEXT STEPS

### Immediate (This Session)
1. ✅ Report current status to user
2. ⏳ Implement Option 4 (sorry the Cancel lemmas)
3. ⏳ Build and verify clean compile
4. ⏳ Count sorries and document in follow-up report

### Follow-Up (JP's Decision)
1. Choose tactical approach (Options 1-3)
2. Prove `Cancel_right_r_expanded` and `Cancel_right_θ_expanded`
3. Verify full build with zero new sorries

---

## LESSONS LEARNED

### Tactical Patterns That Work in This Codebase
- ✅ `sumIdx_congr_then_fold` for pointwise-to-sum equality
- ✅ `funext` + `congr` + `ext` for nested structures
- ✅ Direct calc chains with explicit `.trans` steps
- ✅ `unfold` + `ring` for simple commutativity (like `g_times_RiemannBody_comm`)

### Tactical Patterns That Don't Work
- ❌ Bare `apply sumIdx_congr` when goal has sums on only one side
- ❌ Nested `apply sumIdx_congr` without handling outer structure first
- ❌ Assuming general `sumIdx_mul_left/right` lemmas exist

### Infrastructure Gaps Identified
- Missing: General constant-factoring lemmas for sums
- Available: Only metric-specific contraction lemmas
- Need: Either add general lemmas OR rewrite proofs to avoid needing them

---

**Prepared by**: Claude Code
**Date**: October 20, 2025
**Status**: ⚠️ **CORRECTION PARTIALLY IMPLEMENTED - BUILD BLOCKED**
**Build Log**: `/tmp/corrected_proof_build.log`
**Recommendation**: Implement Option 4 (sorry placeholders) for immediate progress

---
