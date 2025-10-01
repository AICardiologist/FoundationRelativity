# Progress Toward TRUE LEVEL 3 (Zero Axioms, Zero Sorries)

**Date:** September 30, 2025
**Status:** Priority 1 Complete, Priority 2 In Progress

---

## ✅ COMPLETED

### Priority 1: Delete Stage2_mu_t_preview namespace
- **Status:** ✅ COMPLETE
- **Time:** 5 minutes
- **Result:** 1 sorry eliminated (line 1953)
- **Build:** Passing after deletion

---

## ⚠️ IN PROGRESS

### Priority 2: Delete dCoord_add/sub/mul and refactor

**Status:** 3 sorries deleted, but ~15 call sites need refactoring

**What Was Done:**
1. ✅ Deleted `dCoord_add/sub/mul` (lines 709-725) - 3 sorries eliminated
2. ✅ Refactored `dCoord_add4` to use `_of_diff` with differentiability hypotheses
3. ✅ Refactored `dCoord_add4_flat` to propagate hypotheses
4. ✅ Refactored `dCoord_sumIdx` to require differentiability proofs

**Current Build Errors:** ~15 locations need fixes

---

## Build Errors to Fix

### Category A: Syntax/Proof Errors (3 errors)

**1. Line 707: Doc comment syntax error**
```
error: unexpected token '/--'; expected 'lemma'
```
**Fix:** Change `/--` to `/-` for block comment

**2. Line 722: dCoord_add4 proof doesn't work**
```
error: `simp` made no progress
```
**Fix:** Need better proof strategy for applying `dCoord_add_of_diff` three times

**3. Line 794: dCoord_sumIdx hypothesis discharge**
```
error: unsolved goals
```
**Fix:** Better tactical pattern for discharging `∀ i` hypotheses

### Category B: Missing Hypotheses (4 errors)

**Lines 760, 1590, 1631, 1684:** Type mismatches from `dCoord_add4_flat` calls
- Missing differentiability hypotheses for functions A, B, C, D
- **Fix:** Use professor's "Automated Hypothesis Discharge" pattern:
  ```lean
  apply dCoord_add4_flat
  all_goals {
    try {
      simp only [DifferentiableAt_r, DifferentiableAt_θ]
      discharge_diff  -- Or manual application of .add, .mul tactics
    }
    try { simp }  -- For direction mismatch
  }
  ```

### Category C: Deleted Lemma References (8+ errors)

**Lines 928, 1466:** Uses of `dCoord_sub` in `simp` calls
- `RiemannUp_swap_mu_nu` (line 928)
- `nabla_g_antisymmetry` (line 1466)
- **Fix:** Remove from simp list - simp will use `@[simp]` versions automatically

**Lines 1584, 1625, 1677, etc.:** Uses of `dCoord_mul`
- Stage1 LHS lemmas
- **Fix:** Replace with `dCoord_mul_of_diff` + provide differentiability proofs

---

## Detailed Fix Plan

### Step 1: Fix Syntax and Proof Errors (30 min)

**Fix line 707 doc comment:**
```lean
/- Legacy lemmas dCoord_add/sub/mul DELETED per professor mandate (2025-10-01).
   These were unsound (used sorry for arbitrary function differentiability).
   All uses refactored to use axiom-free _of_diff versions. -/
```

**Fix line 722 dCoord_add4 proof:**
```lean
lemma dCoord_add4 (μ : Idx) (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hA_r : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r)
    (hB_r : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r)
    (hC_r : DifferentiableAt_r C r θ ∨ μ ≠ Idx.r)
    (hD_r : DifferentiableAt_r D r θ ∨ μ ≠ Idx.r)
    (hA_θ : DifferentiableAt_θ A r θ ∨ μ ≠ Idx.θ)
    (hB_θ : DifferentiableAt_θ B r θ ∨ μ ≠ Idx.θ)
    (hC_θ : DifferentiableAt_θ C r θ ∨ μ ≠ Idx.θ)
    (hD_θ : DifferentiableAt_θ D r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ =
  dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ := by
  -- Apply dCoord_add_of_diff three times sequentially
  rw [dCoord_add_of_diff (f := fun r θ => A r θ + B r θ + C r θ) (g := D)]
  · rw [dCoord_add_of_diff (f := fun r θ => A r θ + B r θ) (g := C)]
    · rw [dCoord_add_of_diff (f := A) (g := B)]
      · assumption
      · assumption
      · assumption
      · assumption
    · all_goals { try { assumption }; try { simp only [dCoord_add_of_diff]; assumption } }
    [... continue pattern ...]
  · all_goals { assumption }
```

**Fix line 794 dCoord_sumIdx:**
```lean
@[simp] lemma dCoord_sumIdx (μ : Idx) (F : Idx → ℝ → ℝ → ℝ) (r θ : ℝ)
    (hF_r : ∀ i, DifferentiableAt_r (F i) r θ ∨ μ ≠ Idx.r)
    (hF_θ : ∀ i, DifferentiableAt_θ (F i) r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => sumIdx (fun i => F i r θ)) r θ =
  sumIdx (fun i => dCoord μ (fun r θ => F i r θ) r θ) := by
  simp only [sumIdx_expand, dCoord_add_of_diff]
  all_goals {
    -- Discharge each goal (one per index t/r/θ/φ and per function parameter r/θ)
    try { apply hF_r }
    try { apply hF_θ }
  }
```

### Step 2: Fix simp Calls (15 min)

**Line 928 - RiemannUp_swap_mu_nu:**
```lean
-- Before:
simp [sumIdx, Finset.sum_sub_distrib, dCoord_sub, dCoord_add, ...]

-- After (remove deleted lemmas):
simp [sumIdx, Finset.sum_sub_distrib, sub_eq_add_neg, add_comm, ...]
```

**Line 1466 - nabla_g_antisymmetry:**
```lean
-- Before:
simp only [nabla_g_eq_dCoord_sub_C, dCoord_sub]

-- After:
simp only [nabla_g_eq_dCoord_sub_C]
-- The @[simp] dCoord_sub_of_diff will be used automatically
```

### Step 3: Fix dCoord_mul Uses (2-3 hours)

**Pattern for each fix (Lines 1584, 1625, 1677, etc.):**

**Before:**
```lean
have hPt_push :
  dCoord c (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ) r θ =
    ... := by
  simpa using dCoord_mul c
    (fun r θ => Γtot M r θ Idx.t d a)
    (fun r θ => g M Idx.t b r θ) r θ
```

**After:**
```lean
have hPt_push :
  dCoord c (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ) r θ =
    ... := by
  simpa using dCoord_mul_of_diff c
    (fun r θ => Γtot M r θ Idx.t d a)
    (fun r θ => g M Idx.t b r θ) r θ
    (by discharge_diff)  -- Prove Γtot differentiable
    (by discharge_diff)  -- Prove Γtot differentiable
    (by discharge_diff)  -- Prove g differentiable
    (by discharge_diff)  -- Prove g differentiable
```

Or using automated discharge:
```lean
apply dCoord_mul_of_diff
all_goals {
  try { discharge_diff }
  try { simp }
}
```

---

## Estimated Remaining Time

**Step 1 (Syntax/proofs):** 30-60 min
**Step 2 (simp calls):** 15-30 min
**Step 3 (dCoord_mul uses):** 2-3 hours

**Total:** 3-4 hours for Priority 2

---

## After Priority 2: Priority 3 (Riemann_alternation)

Once Priority 2 is complete, we proceed to Priority 3:

**Optimize and Activate Riemann_alternation** (line 2010)
- Uncomment proof scaffold (lines 2012-2614)
- Add `set_option maxHeartbeats 2000000`
- Apply professor's "Controlled Rewriting Sequence":
  1. `abel_nf` - canonicalize additive structure
  2. `simp only [regrouping lemmas]` - structural transforms
  3. `ring_nf` - final arithmetic normalization

**Estimated:** 4-8 hours (depends on performance debugging)

---

## Current Sorry Count

- **Before:** 5 active sorries
- **After Priority 1:** 4 active sorries (deleted Stage2 preview)
- **After Priority 2:** 1 active sorry (deleted 3 legacy lemmas)
- **After Priority 3:** 0 sorries - **TRUE LEVEL 3 ACHIEVED** ✅

---

## Next Steps

1. **Fix syntax error** (line 707)
2. **Fix dCoord_add4 proof** (line 722)
3. **Fix dCoord_sumIdx proof** (line 794)
4. **Remove dCoord_sub/add from simp calls** (lines 928, 1466)
5. **Replace ~8 dCoord_mul uses** with _of_diff versions
6. **Build and test**
7. **Proceed to Priority 3**

---

**Status:** Ready to continue Priority 2 refactoring

**Estimated Time to TRUE LEVEL 3:** 7-12 hours total
- Priority 2: 3-4 hours
- Priority 3: 4-8 hours
