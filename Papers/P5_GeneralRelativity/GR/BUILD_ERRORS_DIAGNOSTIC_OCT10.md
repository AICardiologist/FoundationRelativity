# Build Errors Diagnostic - JP's Tactical Patterns
**Date:** October 10, 2025
**Status:** ✅ BUILD SUCCEEDS (with 5 new sorries for tactical issues)

---

## Summary

I implemented your funext+congrArg patterns verbatim, but encountered issues where `ring` doesn't close goals involving `dCoord` expressions. The file now builds successfully with sorries in place of the failing `ring` tactics.

---

## What Works

### ✅ regroup8 (Lines 2555-2607)
**Status:** FULLY WORKING - NO SORRIES

Your funext+congrArg pattern worked perfectly for regroup8:
```lean
have regroup8 := by
  classical
  have hfun : (fun k => 6 terms) = (fun k => (4 terms) + (2 terms)) := by
    funext k; ring  -- ✅ WORKS
  have hh := congrArg (fun f => sumIdx f) hfun
  simpa [sumIdx_add, sumIdx_sub] using hh  -- ✅ WORKS
```

**No timeout, compiles cleanly!**

---

## What Doesn't Work

### ❌ apply_H - 5 sorries for `ring` failures

**All failures have the same root cause:** `funext k; ring` leaves unsolved goals when the expression contains `dCoord`.

---

### Error 1: Step ① hfun (Line 2668)

**Goal after `funext k`:**
```lean
dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
- dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ
+ Γtot M r θ k Idx.θ a * sumIdx (fun lam => Γtot M r θ lam Idx.r k * g M lam b r θ)
- Γtot M r θ k Idx.r a * sumIdx (fun lam => Γtot M r θ lam Idx.θ k * g M lam b r θ)
=
(dCoord Idx.r ... - dCoord Idx.θ ...) * g M k b r θ
+ (Γtot ... * sumIdx ... - Γtot ... * sumIdx ...)
```

**Algebraically:** This should be trivial - it's just `A*g - B*g + C - D = (A-B)*g + (C-D)`

**Issue:** `ring` doesn't recognize `dCoord ... * g - dCoord ... * g = (dCoord ... - dCoord ...) * g`

**Linter suggested:** `ring_nf` instead of `ring`, but that also doesn't help

**Current workaround:** `sorry` at line 2668

---

### Error 2: Step ② hlin (Line 2690)

**Expected:** `simpa [sumIdx_add, sumIdx_sub] using hsplit` should use hsplit to prove hlin via linearity

**Issue:** Type mismatch - `hsplit` doesn't match the expected type after simpa processes it

**Diagnosis:** Since `hfun` has a `sorry`, `hsplit` = `congrArg sumIdx (sorry)` which may not have the right definitional type

**Current workaround:** `sorry` at line 2690

**Possible fix once hfun works:** This step might auto-resolve when hfun is proven

---

### Error 3: Step ③ hH (Line 2708)

**Goal:** Apply H₁ and H₂ to rewrite the Γ·∑g terms

**Expected:** `simpa [H₁, H₂]` or `simp only [H₁, H₂, sub_eq_add_neg]` should pattern-match and rewrite

**Issue:** Pattern matching fails (tactic `assumption` failed)

**Diagnosis:** Since `hlin` has a `sorry`, the expressions in `hH` might not be in the right form for H₁/H₂ to match

**Current workaround:** `sorry` at line 2708

**Possible fix once hlin works:** H₁/H₂ might match correctly after hlin is proven

---

### Error 4: Step ④ hder - inner `this` (Line 2729)

**Goal after `funext k`:**
```lean
(dCoord Idx.r ... - dCoord Idx.θ ...) * g M k b r θ
=
g M k b r θ * (dCoord Idx.r ... - dCoord Idx.θ ...)
```

**Algebraically:** Trivial commutativity

**Issue:** Same as Error 1 - `ring` doesn't handle `dCoord` expressions

**Current workaround:** `sorry` at line 2729

---

### Error 5: Step ⑤ fold (Line 2786)

**Goal after `funext k`:**
```lean
g * (dCoord_r - dCoord_θ) + g * (sumIdx - sumIdx)
=
g * (dCoord_r - dCoord_θ + sumIdx - sumIdx)
```

**Algebraically:** Distributivity `g*A + g*B = g*(A+B)`

**Issue:** Same as Error 1 - `ring` doesn't distribute over `dCoord` and `sumIdx`

**Current workaround:** `sorry` at line 2786

---

### Error 6: Step ⑤ lin (Line 2769)

**Expected:** `simpa [sumIdx_add, sumIdx_sub]` should prove linearity

**Issue:** Type mismatch or pattern matching failure

**Diagnosis:** Same cascade issue - depends on earlier sorries

**Current workaround:** `sorry` at line 2769

---

## Root Cause Analysis

### Why `ring` Fails on `dCoord`

**Hypothesis 1:** `dCoord` is not fully unfolded for `ring`
- `dCoord` might be an opaque definition
- `ring` only works on polynomial expressions in ℝ
- If `dCoord` doesn't reduce to a polynomial, `ring` can't see through it

**Hypothesis 2:** `ring` doesn't handle function applications in binders
- After `funext k`, we're proving an equality at each `k`
- The expression contains `dCoord Idx.r (fun r θ => ...) r θ`
- This is a function application, not a polynomial variable
- `ring` might not know how to treat it as an atomic variable

**Hypothesis 3:** Missing simp lemmas for `dCoord`
- Maybe there are simp lemmas that normalize `dCoord * g` before `ring`?
- Your environment might have these lemmas in scope, ours might not

---

## Questions for You

**Q1:** In your Lean environment, does `funext k; ring` close these `dCoord` goals immediately?

**Q2:** Are there any simp lemmas or tactics you use BEFORE `ring` when dealing with `dCoord` expressions?

**Q3:** What is the definition of `dCoord`? Is it:
- A fully expanded polynomial?
- An opaque constant?
- A function that needs unfolding?

**Q4:** Do you use `ring_nf` instead of `ring` for these goals?

**Q5:** Should we unfold `dCoord` first? E.g.:
```lean
funext k
unfold dCoord  -- or simp [dCoord]?
ring
```

**Q6:** Or should we treat `dCoord` as an atomic variable and use a different tactic?
```lean
funext k
simp only [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]
-- Explicit AC without ring?
```

---

## Current Build Status

✅ **BUILD SUCCEEDS** with the following sorries:

**New sorries (tactical issues):**
1. Line 2668: `hfun` - `funext k; ring` doesn't close for dCoord expressions
2. Line 2690: `hlin` - `simpa using hsplit` type mismatch (cascade from hfun)
3. Line 2708: `hH` - H₁/H₂ pattern matching (cascade from hlin)
4. Line 2729: `hder.this` - `funext k; ring` doesn't close for dCoord commutativity
5. Line 2769: `lin` - linearity simpa fails (cascade)
6. Line 2786: `fold` - `funext k; ring` doesn't close for dCoord distributivity

**Plus baseline sorries:**
- Line 2540: `kk_cancel` (awaiting your guidance on kk_shape vs = 0)
- Line 2754: Final `exact` in `apply_H` (depends on above resolving)
- Line 2795: Proof completion (depends on apply_H)
- Lines 2660, 2672, 2678-2679: Expected baseline sorries (unchanged)

---

## What We Know Works

✅ **regroup8:** Your pattern works perfectly when expressions don't contain `dCoord`

✅ **Build system:** File compiles cleanly with sorries, no syntax errors

✅ **Structure:** The 5-step apply_H structure is correctly implemented according to your recipe

❌ **Blocker:** `ring` tactic doesn't handle `dCoord` expressions in our Lean 4.11.0 environment

---

## Recommended Next Steps

**Option A:** You provide the missing piece about how to handle `dCoord` with `ring`
- Unfold strategy?
- Simp lemmas needed?
- Alternative tactic?

**Option B:** We try brute-force expansion
```lean
funext k
simp only [dCoord]  -- Expand definition
ring  -- Then try ring on expanded form
```

**Option C:** We avoid `ring` entirely and use explicit rewrites
```lean
funext k
rw [mul_comm (dCoord ...), mul_sub, sub_mul]  -- Manual AC rewrites
```

---

## Summary Table

| Step | Line | Status | Issue |
|------|------|--------|-------|
| regroup8 | 2555-2607 | ✅ WORKS | None - compiles perfectly! |
| apply_H Step ① (hfun) | 2668 | ❌ SORRY | `ring` fails on dCoord expressions |
| apply_H Step ② (hlin) | 2690 | ❌ SORRY | Type mismatch (cascade) |
| apply_H Step ③ (hH) | 2708 | ❌ SORRY | H₁/H₂ don't match (cascade) |
| apply_H Step ④ (hder) | 2729 | ❌ SORRY | `ring` fails on dCoord commutativity |
| apply_H Step ⑤ (lin) | 2769 | ❌ SORRY | Linearity simpa fails |
| apply_H Step ⑤ (fold) | 2786 | ❌ SORRY | `ring` fails on dCoord distributivity |

---

**Prepared by:** Claude Code (AI Agent)
**Date:** October 10, 2025
**Build Status:** ✅ SUCCESS (with tactical sorries)
**Core Issue:** `ring` doesn't close goals containing `dCoord` expressions
**Next:** Awaiting your guidance on dCoord handling strategy
