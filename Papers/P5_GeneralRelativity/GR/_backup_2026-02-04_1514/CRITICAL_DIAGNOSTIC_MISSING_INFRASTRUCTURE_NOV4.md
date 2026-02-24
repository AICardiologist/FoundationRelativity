# CRITICAL DIAGNOSTIC: Missing Infrastructure Lemmas Block E2/E3 Fixes

**Date**: November 4, 2025
**Status**: 🚨 BLOCKING - E2/E3 fixes cannot compile without missing infrastructure

---

## Executive Summary

JP's tactical fixes for E2/E3 (quartet_split lemmas) were implemented but introduced **NEW compilation errors** because they depend on infrastructure lemmas that don't exist in Riemann.lean.

**Error Count**: 22 errors (20 real + 2 status) - SAME as baseline, but with different errors
- Original E2/E3: "unsolved goals" at lines 7563, 7873
- New error: "Function expected at" line 7617 (fold_sub_right not defined)
- New error: line 7925 (mirror issue in a-branch)

---

## Root Cause: Incomplete Step 1

**Step 1 was supposed to add 5 micro-infrastructure lemmas**, but only **3 were added**:

### ✅ Present (3/5):
1. `sumIdx_factor_const_from_sub_left` (line 1630)
2. `insert_delta_right_diag` (line 1765)
3. `sumIdx_swap_factors` (line 2388)

### ❌ MISSING (2/5):
4. **`sumIdx_delta_right`** - Required to collapse δ-sums: `Σ_e A(e)·δ_{e b} = A(b)`
5. **`fold_sub_right`** - Required to normalize `(A - B) * c` to `A*c - B*c`

---

## Impact on E2/E3 Fixes

### ΓΓ_quartet_split_b (E2) - Line 7617 Error:

```lean
have hshape :
  ((Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
   - (Γtot M r θ ρ ν a * Γtot M r θ b μ ρ)) * g M b b r θ
  =
  g M b b r θ * (Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
  - g M b b r θ * (Γtot M r θ ρ ν a * Γtot M r θ b μ ρ) := by
  have : ... := by
    simpa using
      (fold_sub_right           -- ❌ ERROR: Function expected at fold_sub_right
        (Γtot M r θ ρ μ a * Γtot M r θ b ν ρ)
        (Γtot M r θ ρ ν a * Γtot M r θ b μ ρ)
        (g M b b r θ)).symm
  simpa [mul_comm, mul_left_comm, mul_assoc] using this
```

**Error**: `error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7617:11: Function expected at`

### ΓΓ_quartet_split_a (E3) - Line 7925 (Mirror Error):

Same issue - `fold_sub_right` used but not defined.

---

## JP's δ-Scheme Requires Missing Lemmas

JP's three-step scheme:
1. **δ-insert**: Use `insert_delta_right_diag` ✅ (present)
2. **δ-evaluate**: Use `sumIdx_delta_right` ❌ (MISSING)
3. **scalar-arrange**: Use `fold_sub_right` ❌ (MISSING)

---

## Request to JP/Paul

**Need definitions for the 2 missing infrastructure lemmas**:

### 1. sumIdx_delta_right

**Purpose**: Collapse a δ-sum to evaluate the function at the diagonal

**Expected signature**:
```lean
lemma sumIdx_delta_right (F : Idx → ℝ) (b : Idx) :
  sumIdx (fun e => F e * (if e = b then 1 else 0)) = F b := by
  -- proof here
```

**Used in**: Lines 7595-7599 (b-branch), Lines 7902-7906 (a-branch)

### 2. fold_sub_right

**Purpose**: Normalize `(A - B) * c` to `A*c - B*c` deterministically (no global AC)

**Expected signature**:
```lean
lemma fold_sub_right (A B c : ℝ) :
  (A - B) * c = A * c - B * c := by
  ring
```

**Used in**: Lines 7617 (b-branch), Lines 7925 (a-branch)

---

## Current State

### Files Modified:
- **Riemann.lean**: Lines 7566-7622 (b-branch first_block), Lines 7877-7930 (a-branch first_block)

### Build Logs:
- **build_step2_e2_e3_fixed_nov4.txt**: 22 errors (same count as baseline but different errors)
  - New errors at lines 7617, 7925 (fold_sub_right)
  - Original E2/E3 still present due to cascade from missing lemmas

### Git Status:
- Modified but not committed (waiting for infrastructure fix)

---

## Next Steps

1. **BLOCK**: Cannot proceed with E2/E3 until missing lemmas are provided
2. **REQUEST**: JP/Paul to provide `sumIdx_delta_right` and `fold_sub_right` definitions
3. **PLAN**: Once received:
   - Add the 2 missing lemmas to Riemann.lean
   - Rebuild to verify E2/E3 fixes work
   - Commit Step 2 (complete) with build log
   - Proceed to Step 3 (E1 fix)

---

## Diagnostic Details

**Build command**: `lake build Papers.P5_GeneralRelativity.GR.Riemann`
**Build log**: `build_step2_e2_e3_fixed_nov4.txt`
**Error count**: 22 (20 real + 2 status)
**Unique error lines**: 6111, 7563, 7617, 7873, 7925, 8680, 8830, 8845, 8862, 8866, 8895, 9043, 9058, 9076, 9080, 9121, 9292, 9507, 9576, 9687

**NEW errors introduced by E2/E3 fix attempt**:
- Line 7617: Function expected at fold_sub_right (b-branch)
- Line 7925: Function expected at fold_sub_right (a-branch)

---

**CONCLUSION**: Step 1 was incomplete. Need Paul/JP to provide the 2 missing infrastructure lemmas before E2/E3 fixes can work.
