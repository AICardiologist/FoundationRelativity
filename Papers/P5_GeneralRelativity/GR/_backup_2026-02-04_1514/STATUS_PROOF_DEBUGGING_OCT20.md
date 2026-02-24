# Status: Implementing JP's Revised `have final` Proof Body
**Date**: October 20, 2025 (Continued)
**Status**: In Progress - Compilation Errors Remain

---

## EXECUTIVE SUMMARY

I've implemented the user's revised proof body for `have final` which uses explicit named equalities and `.trans` chains instead of fragile `calc` blocks. The approach is conceptually correct but we're encountering tactical issues with Lean 4's type checking and term unification.

**Progress**:
✅ Implemented full proof structure with explicit steps
✅ Fixed prod_rule_backwards_sum application using direct instantiation
✅ Fixed rearrangement using `linarith`
⚠️ Errors remain in step0 (pattern matching) and step4 (let-binding unfolding)

---

## CURRENT COMPILATION ERRORS

### Error 1: Line 4684 - Pattern Matching in step0
**Error Message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4684:10: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

**Location**: In `have step0`, line:
```lean
rw [← recog_Tθ, ← recog_Tr, dTθ_r, dTr_θ]
```

**Root Cause**:
- `recog_Tθ` states: `sumIdx (fun ρ => g M a ρ r θ * Γtot M r θ ρ Idx.θ b) = Γ₁ M r θ a Idx.θ b`
- LHS of step0 has: `dCoord Idx.r (fun r θ => sumIdx (fun ρ => g M a ρ r θ * Γtot M r θ ρ Idx.θ b)) r θ`
- The pattern doesn't match because `sumIdx` is inside a lambda argument to `dCoord`
- Need to rewrite *under* the `dCoord` binder

**Possible Fixes**:
1. Use `conv` to navigate into the lambda:
   ```lean
   conv_lhs =>
     arg 1; ext; rw [← recog_Tθ]
   conv_lhs =>
     arg 2; ext 1; arg 2; ext; rw [← recog_Tr]
   ```

2. Or prove intermediate lemmas:
   ```lean
   have : (fun r θ => sumIdx (...)) = (fun r θ => Γ₁ M r θ a Idx.θ b) := by
     ext; simp [recog_Tθ]
   rw [this]
   ```

### Error 2: Line 4724 - Let-binding Unfolding in step4
**Error Message**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:4724:60: unsolved goals
```

**Location**: In `have step4`, specifically in `hfac` at line 4735:
```lean
simp only [f₁, f₂, f₃, f₄]
ring
```

**Root Cause**:
- `simp only [f₁, f₂, f₃, f₄]` should unfold the let-bindings
- But it's not closing the goal
- Possibly the `ring` tactic needs additional context or the simp isn't fully unfolding

**Possible Fixes**:
1. Use `show ... by` to be more explicit:
   ```lean
   show f₁ ρ - f₂ ρ + f₃ ρ - f₄ ρ = ... by
     simp only [f₁, f₂, f₃, f₄]
     ring
   ```

2. Unfold manually instead of using `simp`:
   ```lean
   calc f₁ ρ - f₂ ρ + f₃ ρ - f₄ ρ
     = (g M a ρ r θ * dCoord Idx.r ...) - ... := rfl
     _ = g M a ρ r θ * (...) := by ring
   ```

---

## PROOF STRUCTURE IMPLEMENTED

The user's revised proof structure has been fully implemented:

### 1. **Abbreviations** (Lines 4609-4636)
All let-bindings for A, B, C, D, M_r, M_θ, Extra_r, Extra_θ defined

### 2. **Recognition Lemmas** (Lines 4638-4646)
- `recog_Tθ`: Recognizes `sumIdx (g * Γ) = Γ₁` for θ direction
- `recog_Tr`: Recognizes `sumIdx (g * Γ) = Γ₁` for r direction

### 3. **Product Rule Application** (Lines 4648-4666)
✅ Successfully applied prod_rule_backwards_sum:
```lean
have hA_raw := prod_rule_backwards_sum M r θ h_ext h_θ a Idx.θ Idx.r b
have hA :
  A = dCoord Idx.r (fun r θ => Γ₁ M r θ a Idx.θ b) r θ - C := by
  have : Γ₁ M r θ a Idx.θ b = sumIdx (fun ρ => g M a ρ r θ * Γtot M r θ ρ Idx.θ b) :=
    recog_Tθ.symm
  simp only [A, C, this]
  exact hA_raw
```

### 4. **Rearrangement** (Lines 4668-4675)
✅ Successfully rearranged using `linarith`:
```lean
have dTθ_r :
  dCoord Idx.r (fun r θ => Γ₁ M r θ a Idx.θ b) r θ = A + C := by
  linarith [hA]
```

### 5. **Remaining Steps** (Lines 4677-4767)
- step0 ⚠️ (has error - see Error 1)
- step1-step2 ✅ (likely work once step0 fixed)
- step3 ✅ (uses `.symm ▸ rfl` pattern)
- step4 ⚠️ (has error - see Error 2)
- step5-step6 ✅ (chain through with `.trans`)
- Final `simpa [Extra_r, Extra_θ] using almost` ✅

---

## WHAT WORKS

1. ✅ **prod_rule_backwards_sum application**
   - Fixed by directly instantiating the lemma
   - Using `simp only [...]` and `exact` to match types

2. ✅ **eq_sub_iff_add_eq rearrangement**
   - Fixed by using `linarith [hA]` instead of `.mp hA.symm`

3. ✅ **Cancel lemma application**
   - Using `.symm ▸ rfl` pattern works

4. ✅ **Overall proof architecture**
   - Explicit named equalities approach is sound
   - `.trans` chaining is correct

---

## WHAT DOESN'T WORK YET

1. ❌ **Rewriting under binders** (step0)
   - Need `conv` or function extensionality

2. ❌ **Let-binding unfolding in nested context** (step4/hfac)
   - `simp only [f₁, ...]` not sufficient
   - May need explicit unfolding or different approach

---

## RECOMMENDED NEXT STEPS

### Option A: Fix Tactical Issues (Recommended)
1. Fix step0 using `conv` or extensionality
2. Fix step4/hfac using explicit calc or show
3. Build and verify remaining steps work

### Option B: Simplify Approach
1. Instead of rewriting `sumIdx = Γ₁` under `dCoord`, directly prove:
   ```lean
   have : dCoord Idx.r (fun r θ => sumIdx (...)) r θ
        = dCoord Idx.r (fun r θ => Γ₁ M r θ a Idx.θ b) r θ := by
     simp [recog_Tθ]
   ```
2. Use this equality instead of trying to rewrite

---

## FILES MODIFIED

### `Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Lines 4598-4767**: Complete revised `have final` proof body

**Key Changes from User's Template**:
- Lines 4652-4666: Fixed prod_rule application (was `simpa [A, C, recog_Tθ] using ...`)
- Lines 4669-4675: Fixed rearrangement (was `eq_sub_iff_add_eq.mp hA.symm`)
- Line 4684: Attempted fix for step0 (currently failing)
- Line 4735: Changed `simp [...]` to `simp only [...]` (still failing)

---

## COMPARISON TO USER'S TEMPLATE

The user provided a complete proof body that should work. The issues we're encountering are:

1. **Type matching precision**: Lean 4's unification is strict about matching patterns under binders
2. **Let-binding scope**: The `let` bindings aren't unfolding in all contexts where we need them

These are tactical issues, not conceptual ones. The proof logic is sound.

---

## BUILD COMMANDS

**Current Build**:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Build Logs**:
- `/tmp/riemann_revised_build.log` - First attempt with user's template
- `/tmp/riemann_fixed_build.log` - After fixing prod_rule
- `/tmp/riemann_linarith_build.log` - After fixing linarith
- `/tmp/riemann_rw_build.log` - Current state (step0 and step4 errors)

---

## REMAINING SORRY COUNT

Once this proof is completed, the file will have:
- ⚠️ Line 4598-4767: `have final` - **IN PROGRESS** (2 tactical errors)
- ⚠️ Line 3814: `regroup_right_sum_to_RiemannUp` (simpler version) - TODO
- ⚠️ Line 4324: `regroup_left_sum_to_RiemannUp` (mirror version) - TODO
- ⚠️ Lines 7650, 7672, 7708, 7776, 7808, 7825: Other lemmas - TODO

Total: 1 in progress + 8 remaining sorries

---

## CONCLUSION

We're very close! The proof structure is correct and matches the user's revised template. We just need to:
1. Fix the pattern matching in step0 (rewriting under dCoord binder)
2. Fix the let-unfolding in step4/hfac

Both are tactical issues with known solutions. The proof logic is sound.

**Estimated Time to Completion**: 15-30 minutes once tactical fixes are applied

---

**Prepared by**: Claude Code
**Date**: October 20, 2025
**Status**: In Progress - 2 tactical errors remaining
**Build Log**: `/tmp/riemann_rw_build.log`
