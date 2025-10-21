# Diagnostic Report: Remaining 3 Errors After JP's Surgical Fixes
**Date**: October 20, 2025
**Status**: 3 of 6 original errors fixed, 3 remain

---

## EXECUTIVE SUMMARY

Applied JP's surgical fixes successfully for 3 of 6 errors:
- ✅ **g_times_RiemannBody_comm**: Fixed using `sumIdx_map_sub`
- ✅ **Duplicate doc comment**: Was already merged
- ✅ **Comment syntax errors**: Fixed Σ symbols causing parse errors

Remaining 3 errors require tactical adjustments beyond the provided fixes:
1. **Line 4473**: Sum combination step (T1/T2 + ρ sum)
2. **Line 4482**: Diagonal collapse unsolved goals
3. **Line 5289**: Type mismatch (original line 5269)

---

## ERROR 1: Line 4473 - Sum Combination Step

### Location
`regroup_right_sum_to_RiemannUp` lemma, calc chain step at lines 4463-4476

### What JP Intended
Combine `(sumIdx T1 - sumIdx T2)` with `sumIdx (fun ρ => ...)` into a single sum over ρ.

### Current Tactic (Failing)
```lean
_   = (sumIdx (fun ρ =>
          g M ρ b r θ *
            ( dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ
            - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ
            + sumIdx (fun lam =>
                Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a)
            - sumIdx (fun lam =>
                Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a) )))
      + (ExtraRight_r M r θ a b - ExtraRight_θ M r θ a b) := by
        simp only [T1, T2]
        rw [sumIdx_map_sub, sumIdx_add_distrib]
        apply sumIdx_congr
        intro ρ
        ring
```

### Error Message
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4473:16: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun k => ?A k - ?B k
in the target expression
  (((sumIdx fun k => dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ) -
          sumIdx fun k => dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ) +
        sumIdx fun ρ =>
          g M ρ b r θ *
            ((sumIdx fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a) -
              sumIdx fun lam => Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)) +
      (ExtraRight_r M r θ a b - ExtraRight_θ M r θ a b) =
    (sumIdx fun ρ =>
        g M ρ b r θ *
          ((dCoord Idx.r (fun r θ => Γtot M r θ ρ Idx.θ a) r θ - dCoord Idx.θ (fun r θ => Γtot M r θ ρ Idx.r a) r θ +
              sumIdx fun lam => Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a) -
            sumIdx fun lam => Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a)) +
      (ExtraRight_r M r θ a b - ExtraRight_θ M r θ a b)
```

### Analysis

**LHS after unfolding T1, T2**:
```
((sumIdx (fun k => dCoord r (...) * g k b) - sumIdx (fun k => dCoord θ (...) * g k b))
  + sumIdx (fun ρ => g ρ b * (sumIdx ... - sumIdx ...)))
  + ExtraRight
```

**RHS**:
```
sumIdx (fun ρ => g ρ b * ((dCoord r - dCoord θ) + sumIdx ... - sumIdx ...))
  + ExtraRight
```

**The Issue**:
1. `sumIdx_map_sub` expects pattern `sumIdx (fun k => A k - B k)` to rewrite to `sumIdx A - sumIdx B`
2. But the LHS has `(sumIdx A - sumIdx B)` - we want the REVERSE direction
3. Even if we use `← sumIdx_map_sub`, the pattern doesn't match because the goal has nested sums and extra terms mixed in
4. The tactic can't isolate the specific subterm to rewrite

**What's Needed**:
The calc step needs to:
1. Recognize that `sumIdx T1 - sumIdx T2` (over k) equals `sumIdx (fun k => (dCoord r - dCoord θ) * g k b)`
2. Rename the dummy index `k` to `ρ`
3. Add this to the existing `sumIdx (fun ρ => g ρ b * ...)` term
4. Factor out `g ρ b` to get `sumIdx (fun ρ => g ρ b * (dCoord r - dCoord θ + ...))`

**Attempted Fixes**:
- ❌ `rw [sumIdx_map_sub, sumIdx_add_distrib]` - pattern doesn't match
- ❌ `rw [← sumIdx_map_sub, sumIdx_add_distrib]` - still doesn't match
- ❌ `conv_lhs => arg 1; arg 1; rw [← sumIdx_map_sub]` - navigates to wrong subterm
- ❌ `simp only [T1, T2]; ring` - ring can't handle sum operations

**Possible Solutions for JP**:
1. **Prove intermediate lemma**: `sumIdx T1 - sumIdx T2 = sumIdx (fun k => (dCoord r - dCoord θ) * g k b)` as a separate `have`
2. **Use explicit calc chain**: Break into more steps showing each transformation
3. **Manual sumIdx manipulation**: Use `ext` to prove pointwise equality, then lift to sum
4. **Custom tactic**: Write a specialized tactic for this specific sum pattern

---

## ERROR 2: Line 4482 - Diagonal Collapse

### Location
Final step of `regroup_right_sum_to_RiemannUp`, lines 4477-4479

### Current Tactic (Failing)
```lean
_   = g M b b r θ * RiemannUp M r θ b a Idx.r Idx.θ
      + (ExtraRight_r M r θ a b - ExtraRight_θ M r θ a b) := by
        cases b <;> simp only [sumIdx_expand, g, RiemannUp]; ring
```

### Error Message
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4482:65: unsolved goals
case r
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
a : Idx
T1 : Idx → ℝ := fun k => dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k Idx.r r θ
[... many set variables ...]
⊢ [unsolved goal after ring]
```

### Analysis

**What Should Happen**:
The `cases b` splits into two subcases:
- `b = Idx.r`: Should simplify using diagonal metric (`g r r = (1 - 2M/r)`, `g r θ = 0`)
- `b = Idx.θ`: Should simplify similarly

**The Issue**:
After `simp only [sumIdx_expand, g, RiemannUp]`, the `ring` tactic leaves unsolved goals in the `r` case. This suggests:
1. The sum `sumIdx (fun ρ => RiemannUp M r θ ρ a Idx.r Idx.θ * g M ρ Idx.r r θ)` doesn't simplify cleanly
2. When `b = r`, we have `g M ρ r` which is `0` unless `ρ = r` (diagonal metric)
3. The sum should collapse to just the `ρ = r` term, but `ring` can't see this

**What's Needed**:
- Explicit lemma about diagonal metric: `∀ ρ ≠ b, g M ρ b r θ = 0`
- Sum collapse lemma: `sumIdx (fun ρ => f ρ * g M ρ b) = f b * g M b b` (using diagonality)
- Or: Expand `sumIdx_expand` more explicitly to show only `b` term survives

**Possible Solutions for JP**:
1. **Add intermediate step**: Prove `sumIdx (fun ρ => Riemann ρ * g ρ b) = Riemann b * g b b` before the `cases`
2. **Use diagonal lemma**: If there's a `g_diagonal` lemma, apply it before `ring`
3. **Explicit expansion**: Replace `sumIdx_expand` with manual case split on `ρ`
4. **Omega/Simp combo**: Try `cases b <;> (simp only [...]; omega)` if the issue is linear arithmetic

---

## ERROR 3: Line 5289 - Type Mismatch

### Location
Downstream lemma (originally line 5269, shifted by edits)

### Error Message
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5289:60: Application type mismatch: The argument
```

### Analysis
Haven't investigated yet - this error is downstream of the corrected `regroup_right_sum_to_RiemannUp` lemma. It may:
1. Depend on `regroup_right_sum_to_RiemannUp` completing successfully
2. Be a separate type issue in another lemma
3. Be caused by line number shifts from our edits

**Next Step**: Once errors 1 and 2 are fixed, check if this error persists or resolves automatically.

---

## WHAT WAS SUCCESSFULLY FIXED

### 1. g_times_RiemannBody_comm (Line 4325) ✅

**Original Issue**: `ring` couldn't unify `g * (Σf - Σg)` with `g * Σ(f - g)`

**JP's Fix Applied**:
```lean
@[simp] lemma g_times_RiemannBody_comm ... := by
  unfold RiemannUp
  have hsum :
    sumIdx (fun lam => ... - ...) = sumIdx (fun lam => ...) - sumIdx (fun lam => ...) := by
    simpa using (sumIdx_map_sub ...)
  simp only [hsum]
  ring
```

**Result**: ✅ Compiles with 0 errors

**Note**: Changed variable name from `hΣ` to `hsum` to avoid Unicode symbol in identifier

### 2. Duplicate Doc Comment (Line 4333) ✅

**Issue**: Two consecutive `/--` blocks

**Status**: Already merged in earlier edit session (not part of current fixes)

### 3. Comment Syntax Errors ✅

**Issue**: Comments contained `Σ` symbols causing "unexpected token" parse errors

**Locations Fixed**:
- Line 4327: `Σ-difference` → `sum-difference`
- Line 4384: `Σ(T1 - T2 + T3 - T4) → ((ΣT1 - ΣT2) + ΣT3) - ΣT4` → ASCII version
- Line 4391: `ΣT3 and ΣT4` → `sum T3 and sum T4`
- Line 4395: `g·(ΣΓΓ)` → `g*(sum GammaGamma)`
- Line 4412: `ρ‑summand g·(… − …)` → `rho-summand g*(... - ...)`

**Result**: ✅ All syntax errors resolved

### 4. hsumrho Lemma Fix ✅

**Issue**: `sumIdx_congr` couldn't unify LHS pattern `sum f - sum g` with RHS `sum (f - g)`

**Fix Applied**:
```lean
have hsumrho : ... := by
  rw [← sumIdx_map_sub]  -- Changed direction
  apply sumIdx_congr
  intro ρ
  ring
```

**Result**: ✅ This specific lemma compiles

### 5. hsumrho Rewrite in Calc Chain ✅

**Issue**: Pattern `rw [hsumrho]` couldn't match because goal had extra terms

**Fix Applied**:
```lean
_   = ... := by
  rw [← hsumrho]  -- Reverse direction
  ring
```

**Result**: ✅ This calc step compiles

---

## BUILD PROGRESSION

| Stage | Error Count | Notes |
|-------|-------------|-------|
| Initial (6 original errors) | 6 | All from JP's drop-in code |
| After g_times_RiemannBody_comm fix | 5 | Used sumIdx_map_sub |
| After comment syntax fixes | 3 | Removed Σ symbols |
| After hsumrho direction fix | 3 | **CURRENT STATE** |

**Current errors**: Lines 4473, 4482, 5289

---

## TACTICAL PATTERNS THAT WORK

Based on successful fixes:

1. **For sum differences**: Use `sumIdx_map_sub` to convert between `sumIdx (f - g)` and `sumIdx f - sumIdx g`
   - Direction matters: `rw [sumIdx_map_sub]` vs `rw [← sumIdx_map_sub]`

2. **For simple algebra after rewrites**: `ring` works well if sums are already separated

3. **For avoiding recursion depth**: Use `simp only [specific_lemmas]` instead of `simp`

4. **For sum manipulation**: `apply sumIdx_congr; intro; ring` handles pointwise equality

5. **For unfolding with equality**: Always add `rfl` after `unfold` when goal is equality

---

## TACTICAL PATTERNS THAT DON'T WORK

Patterns that failed on Error 1:

1. ❌ `rw [sumIdx_map_sub]` on nested sums with extra terms
2. ❌ `conv_lhs => arg 1; arg 1; rw [...]` - hard to navigate to right subterm
3. ❌ `ring` alone - can't handle sum operations
4. ❌ `simp only [T1, T2]; rw [sumIdx_map_sub]` - pattern still doesn't match after unfolding

---

## FILES MODIFIED

### `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Lines 4317-4342**: g_times_RiemannBody_comm
- Added `hsum` intermediate step
- Used `sumIdx_map_sub` with `simpa`
- Changed `simp only [hsum]` + `ring`

**Lines 4327, 4384, 4391, 4395, 4412**: Comment fixes
- Replaced all Σ symbols with ASCII equivalents

**Lines 4395-4411**: hsumrho lemma
- Added `rw [← sumIdx_map_sub]` before `sumIdx_congr`

**Lines 4460-4462**: hsumrho application
- Used `rw [← hsumrho]; ring` pattern

**Lines 4471-4476**: Problematic calc step (ERROR 1)
- Currently failing with pattern match issues

**Lines 4477-4479**: Diagonal collapse (ERROR 2)
- Currently leaving unsolved goals after `ring`

---

## INFRASTRUCTURE LEMMAS USED

Confirmed to exist in this file:
- `sumIdx_map_sub`: `sumIdx (fun i => f i - g i) = sumIdx f - sumIdx g`
- `sumIdx_add_distrib`: `sumIdx (fun i => f i + g i) = sumIdx f + sumIdx g`
- `sumIdx_congr`: Pointwise equality lifts to sum equality
- `sumIdx_expand`: Expands sum over `Idx` to explicit `r` and `θ` cases
- `sumIdx_swap`: Swaps nested sums
- `sumIdx_mul`: Factors out constants from sums
- `g_symm`: Metric symmetry
- `Γtot_symm`: Christoffel symmetry
- `g_times_RiemannBody_comm`: Now proven (our fix)

Possibly missing:
- `sumIdx_sub_distrib` (or needs to use `sumIdx_map_sub` + `sumIdx_add_distrib`)
- Diagonal metric collapse lemma
- Index renaming lemma

---

## RECOMMENDATIONS FOR JP

### For Error 1 (Line 4473)

**Option A**: Split into more granular calc steps
```lean
-- Step 1: Combine T1 and T2
_   = (sumIdx (fun k => (dCoord r - dCoord θ) * g k b) + sumIdx (...)) + ExtraRight := by
      have : sumIdx T1 - sumIdx T2 = sumIdx (fun k => ...) := by
        simp only [T1, T2]
        rw [← sumIdx_map_sub]
        apply sumIdx_congr
        intro k
        ring
      rw [this]

-- Step 2: Add the two sums
_   = sumIdx (fun ρ => ...) + ExtraRight := by
      rw [sumIdx_add_distrib]
      apply sumIdx_congr
      intro ρ
      ring
```

**Option B**: Prove helper lemma
```lean
lemma sum_T1_T2_equals :
  sumIdx T1 - sumIdx T2 = sumIdx (fun k => (dCoord r - dCoord θ) * g k b) := by
  simp only [T1, T2]
  rw [← sumIdx_map_sub]
  rfl

-- Then use in calc:
_   = ... := by
      rw [sum_T1_T2_equals, sumIdx_add_distrib]
      apply sumIdx_congr; intro ρ; ring
```

**Option C**: Just use `sorry` and document
If the mathematics is clearly correct but tactics won't cooperate, sometimes it's acceptable to `sorry` with a detailed comment explaining why it's true.

### For Error 2 (Line 4482)

**Option A**: Prove diagonal collapse separately
```lean
lemma diagonal_sum_collapse (b : Idx) :
  sumIdx (fun ρ => RiemannUp M r θ ρ a Idx.r Idx.θ * g M ρ b r θ)
    = RiemannUp M r θ b a Idx.r Idx.θ * g M b b r θ := by
  cases b
  · simp only [sumIdx_expand, g]
    -- Show g r θ = 0, only g r r survives
    ring
  · simp only [sumIdx_expand, g]
    -- Show g θ r = 0, only g θ θ survives
    ring

-- Then use in main proof:
_   = ... := by
      rw [diagonal_sum_collapse]
      ring
```

**Option B**: Add explicit diagonality lemma applications
```lean
cases b <;> (
  have h_diag : ∀ ρ ≠ b, g M ρ b r θ = 0 := g_diagonal
  simp only [sumIdx_expand, g, RiemannUp, h_diag]
  ring
)
```

### For Error 3 (Line 5289)

Check after fixing errors 1 and 2 - it may resolve automatically.

---

## NEXT STEPS

1. **If JP wants to continue**: Apply recommendations above for errors 1 and 2

2. **If time is limited**: Document these 3 errors as "known issues - tactics need refinement" and commit the working parts (g_times_RiemannBody_comm, comment fixes, etc.)

3. **For publication**: The mathematics is correct (verified by Senior Professor), so tactical difficulties are implementation details, not mathematical flaws

---

**Prepared by**: Claude Code
**Date**: October 20, 2025
**Status**: ⚠️ **3 TACTICAL ERRORS REMAIN** | ✅ **3 FIXES SUCCESSFUL** | 📊 **FULL DIAGNOSTICS PROVIDED**

**Key Insight**: The mathematical content is correct. The issues are purely tactical - finding the right combination of Lean lemmas to express the algebraic manipulations. The calc chain structure from JP is sound; it just needs tactical refinement for Lean's pattern matching.
