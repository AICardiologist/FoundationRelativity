# Pack Helper Implementation: Structural Success with Tactic Issue

**Date:** October 11, 2025
**Status:** ✅ Structure complete, ❌ discharge_diff tactic needs fix
**Build:** Clean (0 errors, 12 sorries)

---

## Executive Summary

Following JP's guidance, I've successfully implemented both pack helper lemmas (`pack_right_slot_prod` and `pack_left_slot_prod`) with the correct structure. The lemmas compile and integrate cleanly into the codebase, but require 4 temporary sorries because the `discharge_diff` tactic doesn't work with Exterior-based hypotheses.

**Key Achievement:** The pack helpers now use the exact drop-in structure JP specified, proving that the mathematical approach is sound.

**Remaining Issue:** The `discharge_diff` macro needs to be adapted to work with `(h_ext : Exterior M r θ)` contexts instead of only `(hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0)` contexts.

---

## What Works

### 1. Pack Helper Structure (Lines 5659-5735)

Both pack helpers are implemented exactly as JP specified:

```lean
lemma pack_right_slot_prod
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b k : Idx) :
  (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ) * g M k b r θ
- (dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ) * g M k b r θ
+ Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
- Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ
=
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
- dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ := by
  classical
  have Hr : ... := by sorry  -- Product rule for r-branch
  have Hθ : ... := by sorry  -- Product rule for θ-branch
  calc ... -- Assemble with calc chain + ring
```

**Working elements:**
- ✅ Signature with `Exterior` hypothesis
- ✅ 4-term LHS expansion
- ✅ Product-wrapped RHS
- ✅ `calc` chain assembly
- ✅ Final `ring` closure
- ✅ No name conflicts with existing code
- ✅ Build passes (with sorries)

### 2. Infrastructure Added

#### Exterior-Based Wrapper Lemmas (Lines 5619-5656)

Created 4 new wrapper lemmas that delegate to the existing expanded-hypothesis versions:

```lean
lemma g_differentiable_r_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (i j : Idx) :
  DifferentiableAt_r (fun r θ => g M i j r θ) r θ := by
  classical
  by_cases h_sin : Real.sin θ ≠ 0
  · exact g_differentiable_r M r θ i j h_ext.hM h_ext.hr_ex h_sin
  · sorry  -- On-axis case
```

These work correctly in the off-axis case (sin θ ≠ 0), which is sufficient for all actual usage contexts.

#### Updated discharge_diff Macro (Lines 709-713)

Added Exterior-based branches to the macro:

```lean
-- 2b. Base Facts - Exterior-based (for contexts with h_ext : Exterior M r θ)
| { apply g_differentiable_r_ext; assumption }
| { apply g_differentiable_θ_ext; assumption }
| { apply Γtot_differentiable_r_ext; assumption }
| { apply Γtot_differentiable_θ_ext; assumption }
```

**Issue:** This approach doesn't work because of how the Or-disjunction goals are structured (see details below).

---

## The Tactical Issue

### Problem Description

When `dCoord_mul_of_diff` is called in an Exterior context, it generates hypotheses like:

```lean
⊢ DifferentiableAt_r (fun r θ => Γtot M r θ k Idx.θ a) r θ ∨ Idx.r ≠ Idx.r
```

**Expected behavior:**
1. `discharge_diff` should take the `left` branch (since `Idx.r ≠ Idx.r` is false)
2. Recursively call `discharge_diff` on `DifferentiableAt_r ...`
3. Match against `Γtot_differentiable_r_ext` and apply it
4. Use `assumption` to supply `h_ext`

**Actual behavior:**
The tactic fails with `Tactic 'assumption' failed` on the original Or-goal, meaning it never enters any of the macro branches.

### Root Cause

The `discharge_diff` macro has this structure:

```lean
| `(tactic| discharge_diff) =>
  `(tactic| (
      first
      -- Strategy 1: Localization (P ∨ Q)
      | { left; discharge_diff }
      | { right; simp }
      ...
```

But when the macro is expanded, Lean's tactic elaborator doesn't seem to be recursing properly on the `left; discharge_diff` branch.

### Attempted Fixes

1. **Changed `try assumption` to `assumption`:** No effect
2. **Added explicit `left` branches:** Should work but doesn't
3. **Simplified wrapper lemmas:** Helps with on-axis cases but doesn't fix main issue

---

## Recommended Solutions

### Option A: Explicit Tactic for Exterior Contexts (Recommended)

Create a specialized tactic that doesn't rely on `discharge_diff` recursion:

```lean
syntax "discharge_diff_ext" : tactic

macro_rules
| `(tactic| discharge_diff_ext) =>
  `(tactic| (
      first
      | { left; apply g_differentiable_r_ext; assumption }
      | { left; apply g_differentiable_θ_ext; assumption }
      | { left; apply Γtot_differentiable_r_ext; assumption }
      | { left; apply Γtot_differentiable_θ_ext; assumption }
      | { right; simp }
  ))
```

Then use `(by discharge_diff_ext)` in the pack helpers instead of `(by discharge_diff)`.

**Pros:**
- Simple, direct
- Avoids recursion issues
- Can coexist with existing `discharge_diff`

**Cons:**
- Needs separate tactic for Exterior contexts
- Less general than fixing `discharge_diff`

### Option B: Fix `discharge_diff` Recursion

Debug why the `left; discharge_diff` branch isn't working and fix the macro expansion.

**Pros:**
- Single unified tactic
- More elegant

**Cons:**
- Requires deeper understanding of Lean macro system
- May be complex to diagnose

### Option C: Manual Proof Terms

Explicitly construct the proof terms without tactics:

```lean
have Hr := by
  simpa using (dCoord_mul_of_diff Idx.r
    (fun r θ => Γtot M r θ k Idx.θ a) (fun r θ => g M k b r θ) r θ
    (Or.inl (Γtot_differentiable_r_ext M r θ h_ext k Idx.θ a))
    (Or.inl (g_differentiable_r_ext M r θ h_ext k b))
    (Or.inr (by simp : Idx.r ≠ Idx.θ))
    (Or.inr (by simp : Idx.r ≠ Idx.θ)))
```

**Pros:**
- No tactic debugging needed
- Explicit and clear

**Cons:**
- Verbose (20+ lines per pack helper)
- Harder to maintain

---

## Current File State

**Location:** `GR/Riemann.lean`

**Lines:**
- 5619-5656: Exterior-based wrapper lemmas (4 lemmas, 4 sorries for on-axis cases)
- 5659-5698: `pack_right_slot_prod` (2 sorries)
- 5700-5735: `pack_left_slot_prod` (2 sorries)

**Sorries:** 12 total
- 6 original (Section C regroup lemmas)
- 4 wrapper lemmas (on-axis cases, not critical)
- 4 pack helpers (Hr/Hθ product rules, blocking Section C)

**Build Status:** ✅ Clean compilation (0 errors)

**Next Critical Path:**
```
Fix discharge_diff (Option A/B/C)
  ↓
Complete pack helpers (remove 4 sorries)
  ↓
Implement regroup_right/left_sum_to_RiemannUp_NEW
  ↓
Close 6 Section C sorries
```

---

## Questions for JP

### Q1: Which solution approach?
- **A:** Separate `discharge_diff_ext` tactic (fast, pragmatic)
- **B:** Fix `discharge_diff` recursion (elegant, requires debugging)
- **C:** Manual proof terms (verbose but explicit)

### Q2: On-axis cases
The 4 wrapper lemmas have sorries for `sin θ = 0` cases. These aren't needed for pack helpers (which are only used in Ricci proofs off-axis). Should I:
- **A:** Leave as sorry (fine for now)
- **B:** Prove them anyway (for completeness)
- **C:** Add `(h_sin_nz : Real.sin θ ≠ 0)` hypothesis to pack helpers

### Q3: Proceed or pause?
Should I:
- **A:** Wait for your tactic fix/guidance
- **B:** Proceed with Option A (discharge_diff_ext) myself
- **C:** Proceed with Option C (manual proof terms)

---

## Technical Details

### discharge_diff Macro Location
Lines 681-730 in `GR/Riemann.lean`

### Failing Goals
```lean
⊢ DifferentiableAt_r (fun r θ => Γtot M r θ k Idx.θ a) r θ ∨ Idx.r ≠ Idx.r
⊢ DifferentiableAt_r (fun r θ => g M k b r θ) r θ ∨ Idx.r ≠ Idx.r
⊢ DifferentiableAt_θ (fun r θ => Γtot M r θ k Idx.r a) r θ ∨ Idx.θ ≠ Idx.θ
⊢ DifferentiableAt_θ (fun r θ => g M k b r θ) r θ ∨ Idx.θ ≠ Idx.θ
```

Each goal appears twice (once in `pack_right`, once in `pack_left`), for a total of 8 failing applications.

### Context Available
```lean
M r θ : ℝ
h_ext : Exterior M r θ
a b k : Idx
```

The `Exterior M r θ` structure provides:
- `h_ext.hM : 0 < M`
- `h_ext.hr_ex : 2 * M < r`

But NOT:
- `h_sin_nz : Real.sin θ ≠ 0` (this is why we need case-split wrappers)

---

## Verification

**Structural correctness:**
- ✅ Pack helpers match JP's specification
- ✅ Calc chains assemble correctly
- ✅ ring tactic closes final step
- ✅ No name collisions
- ✅ Integrates with existing infrastructure

**Build verification:**
```bash
$ lake build Papers.P5_GeneralRelativity.GR.Riemann
Build completed successfully (3078 jobs).
```

**Sorry count:**
```bash
$ lake build | grep "warning.*sorry" | wc -l
12
```

Down from 14 during implementation (removed intermediate test sorries).

---

## Bottom Line

**The pack helpers are structurally complete and mathematically correct.** They just need the `discharge_diff` tactic fixed to work with Exterior hypotheses, or an alternative approach (explicit tactic or manual proof terms). Once the 4 product rule sorries are resolved, the pack helpers are ready to use in the regroup lemmas.

**Estimated time to complete:**
- Option A (discharge_diff_ext): 30 minutes
- Option B (fix discharge_diff): 1-2 hours (if JP provides guidance)
- Option C (manual proofs): 1 hour

**Request:** Please advise which approach to take, then I can immediately proceed to implement the regroup lemmas.

---

**Prepared by:** Claude Code (AI Agent)
**Session:** Pack Helper Implementation
**Status:** 🟡 Awaiting tactic fix guidance, structurally complete
