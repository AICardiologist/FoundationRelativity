# Deep Analysis: `alternation_dC_eq_Riem` Lemma

**Date:** October 4, 2025
**Status:** 🔍 **CRITICAL FINDING** - Found the main bottleneck

---

## Executive Summary

The `alternation_dC_eq_Riem` lemma (lines 2466-3870) contains **40+ `simpa` calls**, each triggering expensive simp searches. This is THE major bottleneck causing compilation timeouts.

**Fixes Applied So Far:**
1. Line 1856: `simp [sumIdx_add]` → `simp only [sumIdx_add]` ✅
2. Lines 2516, 2521, 2526, 2531: `simpa using dCoord_g_via_compat_ext` → `exact` ✅
3. Lines 2643-2755: 12 instances of `simpa using dCoord_mul` → `exact` ✅

**Remaining:** 14+ `simpa using dCoord_add` and other expensive simp calls

---

## Lemma Structure

**Location:** Lines 2466-3870 (1404 lines!)
**Section:** `noncomputable section RicciInfrastructure` (lines 1823-3870)

**Signature:**
```lean
lemma alternation_dC_eq_Riem (M r θ : ℝ) (a b c d : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  ( dCoord c (fun r θ => ContractionC M r θ d a b) r θ
  - dCoord d (fun r θ => ContractionC M r θ c a b) r θ )
  = ( Riemann M r θ a b c d + Riemann M r θ b a c d )
```

**Proof Strategy:** 6-step mechanical plan (per comment at line 2471)

---

## Bottleneck #3: `simpa using dCoord_mul` (12 instances)

**Lines:** 2643, 2653, 2663, 2673, 2684, 2694, 2704, 2714, 2725, 2735, 2745, 2755

**Pattern:**
```lean
have hpush_ct₁ :
  dCoord c (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ) r θ =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * g M Idx.t b r θ +
    (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ := by
  simpa using dCoord_mul c  ← PROBLEM
    (fun r θ => Γtot M r θ Idx.t d a)
    (fun r θ => g M Idx.t b r θ) r θ
```

**Problem:** `simpa` applies simp before using the lemma. Since the goal and `dCoord_mul` result match exactly, `exact` suffices.

**Fix Applied:** Replace `simpa using` with `exact`

**Example:**
```lean
have hpush_ct₁ :
  dCoord c (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ) r θ =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * g M Idx.t b r θ +
    (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ := by
  exact dCoord_mul c  ← FIXED
    (fun r θ => Γtot M r θ Idx.t d a)
    (fun r θ => g M Idx.t b r θ) r θ
```

---

## Bottleneck #4: `simpa using dCoord_add` (14 instances) - **NOT YET FIXED**

**Relative lines in lemma:** 385, 389, 453, 457, 518, 522, 587, 591, 985, 989, 1051, 1055, 1107, 1112
**Absolute lines:** 2851, 2855, 2919, 2923, 2984, 2988, 3053, 3057, 3451, 3455, 3517, 3521, 3573, 3578

**Pattern:**
```lean
have hAB :
  dCoord c (fun r θ => P_t r θ + P_r r θ) r θ
    = dCoord c P_t r θ + dCoord c P_r r θ := by
  simpa using dCoord_add c P_t P_r r θ  ← PROBLEM
```

**Same Issue:** `simpa` is unnecessary - `exact` suffices.

**Recommended Fix:** Replace all 14 instances:
```lean
have hAB :
  dCoord c (fun r θ => P_t r θ + P_r r θ) r θ
    = dCoord c P_t r θ + dCoord c P_r r θ := by
  exact dCoord_add c P_t P_r r θ  ← FIXED
```

---

## Bottleneck #5: Additional `simpa` calls - **NOT YET FIXED**

**Line 2824 (relative 358):**
```lean
simpa using (Stage2_mu_t_preview.mu_t_component_eq M r θ a b c d).symm
```

**Lines with complex `simpa [...] using`:**
```lean
Line 2861: simpa [add_comm, add_left_comm, add_assoc] using dCoord_add c ...
Line 2869: simpa [add_comm, add_left_comm, add_assoc] using hABCD
Line 2879: simpa [hPt] using dCoord_mul c ...
```

These use simp with rewrite lemmas, which is more expensive than bare `exact`.

---

## Bottleneck #6: Broad `simp` calls - **NOT YET FIXED**

**Line 2819-2823:**
```lean
simp [hμt_rw,
      add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]
```

**Line 2826-2830:**
```lean
simp_all [add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc,
          nabla_g_zero, dCoord_const, dCoord_zero_fun,
          regroup₂, regroup_same_right]
```

**Problem:** These `simp` calls have MANY lemmas (9-11 each) and search through large algebraic expressions.

**Recommendation:**
1. Replace with manual `rw` steps if possible
2. Or use `simp only [...]` with minimal lemma set
3. Or restructure proof to avoid needing these

---

## Total Expensive Tactic Calls in Lemma

| Tactic Type | Count | Status |
|------------|-------|--------|
| `simpa using dCoord_g_via_compat_ext` | 4 | ✅ FIXED |
| `simpa using dCoord_mul` | 12 | ✅ FIXED |
| `simpa using dCoord_add` | 14 | ⏳ READY TO FIX |
| `simpa` (other) | 10+ | ⏳ NEEDS ANALYSIS |
| `simp [...]` (broad) | 2 | ⏳ NEEDS OPTIMIZATION |
| **TOTAL** | **40+** | **~40% FIXED** |

---

## Compilation Impact

**Before any fixes:**
- Full file: TIMEOUT (120+ seconds)

**After Fix #1 (nabla_g_eq_dCoord_sub_C):**
- Line 2000: 7.9s (simp 16.3s)

**After Fixes #2+#3 (16 simpa calls):**
- Line 2500: 10.2s (simp 28.6s)
- Line 2600: TIMEOUT

**Hypothesis:** The remaining 14 `simpa using dCoord_add` calls + 2 broad `simp` calls are causing the timeout.

---

## Recommended Fix Strategy

### Immediate (Low-Risk):
Replace all 14 `simpa using dCoord_add` with `exact dCoord_add`:

```bash
sed -i '' \
  -e '2851s/simpa using dCoord_add/exact dCoord_add/' \
  -e '2855s/simpa using dCoord_add/exact dCoord_add/' \
  -e '2919s/simpa using dCoord_add/exact dCoord_add/' \
  -e '2923s/simpa using dCoord_add/exact dCoord_add/' \
  -e '2984s/simpa using dCoord_add/exact dCoord_add/' \
  -e '2988s/simpa using dCoord_add/exact dCoord_add/' \
  -e '3053s/simpa using dCoord_add/exact dCoord_add/' \
  -e '3057s/simpa using dCoord_add/exact dCoord_add/' \
  -e '3451s/simpa using dCoord_add/exact dCoord_add/' \
  -e '3455s/simpa using dCoord_add/exact dCoord_add/' \
  -e '3517s/simpa using dCoord_add/exact dCoord_add/' \
  -e '3521s/simpa using dCoord_add/exact dCoord_add/' \
  -e '3573s/simpa using dCoord_add/exact dCoord_add/' \
  -e '3578s/simpa using dCoord_add/exact dCoord_add/' \
  GR/Riemann.lean
```

### Medium-Risk:
Replace `simpa [add_comm, ...] using` with `simp only [...]; exact`:

```lean
-- Before:
simpa [add_comm, add_left_comm, add_assoc] using hABCD

-- After:
simp only [add_comm, add_left_comm, add_assoc]
exact hABCD
```

### Higher-Risk (Requires Understanding Proof):
Optimize the two broad `simp` calls (lines 2819, 2826) by:
1. Breaking into smaller steps
2. Using `simp only` with minimal lemma set
3. Replacing with manual `rw` or `ring`

---

## Alternative: Modularize the Lemma

If optimizing tactics doesn't work, consider:

1. **Break into helper lemmas**: Split the 1404-line proof into 10-20 smaller lemmas
2. **Factor out patterns**: The 12 `dCoord_mul` and 14 `dCoord_add` calls suggest repetitive structure
3. **Use automation smartly**: Perhaps a custom tactic that does `exact dCoord_mul ...` without simp

---

## Questions for Junior Professor

### Q1: Are the `simpa` → `exact` replacements safe?

We've replaced 16 `simpa using` with `exact` based on the observation that the goals match the lemma conclusions exactly. Is this transformation always safe, or are there edge cases where `simpa` does necessary normalization?

### Q2: Can we simplify the proof strategy?

The lemma is 1404 lines with 40+ expensive tactic calls. Is there a more direct proof strategy that avoids so much expansion and re-simplification?

### Q3: Should we modularize before or after fixing tactics?

Would it be better to:
- **Option A:** Fix all remaining `simpa` calls first, then test
- **Option B:** Break the lemma into smaller pieces first, then optimize each piece

### Q4: What's the expected compilation time?

With all fixes applied, what's a reasonable compilation time for this lemma? If it's inherently expensive (say, 30-60 seconds), maybe we should just add a warning comment rather than trying to optimize further.

---

## Files Modified

**`GR/Riemann.lean`:**
- Line 1856: `simp [sumIdx_add]` → `simp only [sumIdx_add]`
- Lines 2516, 2521, 2526, 2531: `simpa using dCoord_g_via_compat_ext` → `exact`
- Lines 2643, 2653, 2663, 2673, 2684, 2694, 2704, 2714, 2725, 2735, 2745, 2755: `simpa using dCoord_mul` → `exact`

**Backups:**
- `Riemann.lean.simpa_fix3` - Before fixing dCoord_mul calls

---

## Next Steps

**Immediate:**
1. Apply fix for 14 `simpa using dCoord_add` calls
2. Test compilation time
3. If still slow, analyze the 2 broad `simp` calls

**If Still Slow:**
1. Profile the specific lemma with `set_option profiler true in`
2. Identify which specific tactic call is taking the most time
3. Apply targeted optimization

**Long-term:**
1. Consider modularizing this 1404-line lemma
2. Document why certain tactics are expensive
3. Add comments warning future developers about performance-sensitive sections

---

## Summary for User

We've identified that **`alternation_dC_eq_Riem`** is a massive 1404-line lemma with **40+ expensive `simpa` calls**. We've fixed 16 of them (40%), which improved compilation up to line 2500, but the file still times out.

**14 more `simpa using dCoord_add` calls** remain unfixed, plus 2 very broad `simp` calls with 9-11 lemmas each. These are likely causing the remaining timeout.

**Recommended:** Apply the immediate fix for the 14 `dCoord_add` calls and retest.
