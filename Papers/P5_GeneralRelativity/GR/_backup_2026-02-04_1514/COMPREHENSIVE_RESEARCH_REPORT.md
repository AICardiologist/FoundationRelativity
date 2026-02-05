# Comprehensive Research Report: Compilation Timeout Investigation

**Date:** October 4, 2025
**To:** Junior Professor
**From:** Research Assistant
**Re:** Deep analysis of `alternation_dC_eq_Riem` bottleneck and all applied fixes

---

## Executive Summary

We've successfully identified and fixed **30 expensive `simpa` calls** in the `alternation_dC_eq_Riem` lemma, but **the file still times out after 4+ minutes**. This indicates there are additional bottlenecks beyond the tactical optimizations we've applied. This report provides comprehensive details for further investigation.

---

## I. All Fixes Applied

### Fix #1: `nabla_g_eq_dCoord_sub_C` (Line 1856)

**Problem:** Broad `simp [sumIdx_add]` triggered expensive search after unfolding

**Before:**
```lean
lemma nabla_g_eq_dCoord_sub_C (M r θ : ℝ) (d a b : Idx) :
  nabla_g M r θ d a b = dCoord d (fun r θ => g M a b r θ) r θ - ContractionC M r θ d a b := by
  unfold nabla_g ContractionC
  simp [sumIdx_add]  -- ❌ Broad search
  ring
```

**After:**
```lean
lemma nabla_g_eq_dCoord_sub_C (M r θ : ℝ) (d a b : Idx) :
  nabla_g M r θ d a b = dCoord d (fun r θ => g M a b r θ) r θ - ContractionC M r θ d a b := by
  unfold nabla_g ContractionC
  simp only [sumIdx_add]  -- ✅ Narrow search
  ring
```

**Impact:** Line 2000 compiles in 7.9s (was timeout)

---

### Fix #2: `simpa using dCoord_g_via_compat_ext` (4 instances)

**Lines:** 2516, 2521, 2526, 2531

**Problem:** `simpa` invokes simp before exact, but goal matches lemma exactly

**Pattern (repeated 4 times):**
```lean
-- Before:
have hcompat_c_kb : ∀ k, dCoord c (fun r θ => g M k b r θ) r θ =
    sumIdx (fun m => Γtot M r θ m c k * g M m b r θ) +
    sumIdx (fun m => Γtot M r θ m c b * g M k m r θ) := by
  intro k; simpa using dCoord_g_via_compat_ext M r θ hExt c k b  -- ❌

-- After:
have hcompat_c_kb : ∀ k, dCoord c (fun r θ => g M k b r θ) r θ =
    sumIdx (fun m => Γtot M r θ m c k * g M m b r θ) +
    sumIdx (fun m => Γtot M r θ m c b * g M k m r θ) := by
  intro k; exact dCoord_g_via_compat_ext M r θ hExt c k b  -- ✅
```

**Impact:** Partial improvement, line 2500 compiles in 10.2s

---

### Fix #3: `simpa using dCoord_mul` (12 instances)

**Lines:** 2643, 2653, 2663, 2673, 2684, 2694, 2704, 2714, 2725, 2735, 2745, 2755

**Problem:** Same as Fix #2 - unnecessary simp before exact

**Pattern (repeated 12 times):**
```lean
-- Before:
have hpush_ct₁ :
  dCoord c (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ) r θ =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * g M Idx.t b r θ +
    (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ := by
  simpa using dCoord_mul c  -- ❌
    (fun r θ => Γtot M r θ Idx.t d a)
    (fun r θ => g M Idx.t b r θ) r θ

-- After:
have hpush_ct₁ :
  dCoord c (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ) r θ =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * g M Idx.t b r θ +
    (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ := by
  exact dCoord_mul c  -- ✅
    (fun r θ => Γtot M r θ Idx.t d a)
    (fun r θ => g M Idx.t b r θ) r θ
```

**Impact:** Further improvement, but still times out after line 2600

---

### Fix #4: `simpa using dCoord_add` (14 instances)

**Lines:** 2850, 2854, 2918, 2922, 2983, 2987, 3052, 3056, 3450, 3454, 3516, 3520, 3572, 3577

**Problem:** Same pattern - unnecessary simp

**Pattern (repeated 14 times):**
```lean
-- Before:
have hAB :
  dCoord c (fun r θ => P_t r θ + P_r r θ) r θ
    = dCoord c P_t r θ + dCoord c P_r r θ := by
  simpa using dCoord_add c P_t P_r r θ  -- ❌

-- After:
have hAB :
  dCoord c (fun r θ => P_t r θ + P_r r θ) r θ
    = dCoord c P_t r θ + dCoord c P_r r θ := by
  exact dCoord_add c P_t P_r r θ  -- ✅
```

**Impact:** File still times out after 4+ minutes

---

## II. Total Fixes Summary

| Fix # | Tactic Type | Count | Lines | Status |
|-------|-------------|-------|-------|--------|
| 1 | `simp [...]` → `simp only [...]` | 1 | 1856 | ✅ APPLIED |
| 2 | `simpa using dCoord_g_via_compat_ext` → `exact` | 4 | 2516-2531 | ✅ APPLIED |
| 3 | `simpa using dCoord_mul` → `exact` | 12 | 2643-2755 | ✅ APPLIED |
| 4 | `simpa using dCoord_add` → `exact` | 14 | 2850-3577 | ✅ APPLIED |
| **TOTAL** | | **31** | | **100% APPLIED** |

---

## III. Remaining Expensive Tactics (NOT Fixed)

### 1. `simpa [add_comm, ...]` with dCoord_add (2 instances)

**Line 3262:**
```lean
simpa [add_comm, add_left_comm, add_assoc]
  using dCoord_add c
    (fun r θ => P_t  r θ + P_r  r θ + P_θ  r θ + P_φ  r θ)
    (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ
```

**Line 3322:**
```lean
simpa [add_comm, add_left_comm, add_assoc]
  using dCoord_add d
    (fun r θ => Q_t  r θ + Q_r  r θ + Q_θ  r θ + Q_φ  r θ)
    (fun r θ => Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ) r θ
```

**Why not fixed:** These require associativity normalization because the goal has different grouping than `dCoord_add`'s conclusion. Cannot simply use `exact`.

**Potential fix:** Use `simp only [add_comm, add_left_comm, add_assoc]; exact dCoord_add ...`

---

### 2. Broad `simp` call (Line 2819)

```lean
simp [hμt_rw,
      add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]  -- 7 lemmas
```

**Problem:** Applies 7 associativity/commutativity lemmas to large algebraic expression

**Potential fix:** Replace with manual `rw` steps or `ring`

---

### 3. Very broad `simp_all` call (Line 2826)

```lean
simp_all [add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc,
          nabla_g_zero, dCoord_const, dCoord_zero_fun,
          regroup₂, regroup_same_right]  -- 11 lemmas
```

**Problem:** `simp_all` with 11 lemmas on huge expression

**Potential fix:** Break into smaller steps, or use targeted rewrites

---

## IV. Diagnostic Findings

### Profiler Evidence (cumulative at line 2500):

```
simp                     28.6s  ← Still growing!
tactic execution         6.5s
typeclass inference      5.51s
ring                     305ms
```

**Observation:** Simp time grew from 16.3s (line 2000) to 28.6s (line 2500) **even after fixing 16 simpa calls**. This suggests the remaining bottlenecks are very expensive.

---

### Lemma Structure

**`alternation_dC_eq_Riem`:**
- **Location:** Lines 2466-3870 (1404 lines!)
- **Purpose:** Prove `dCoord c (ContractionC d a b) - dCoord d (ContractionC c a b) = Riemann a b c d + Riemann b a c d`
- **Strategy:** 6-step mechanical plan involving expansion, linearity, product rule, and reassembly

**Why it's expensive:**
1. **Size:** 1404 lines is massive for a single lemma
2. **Repetition:** Contains 40+ `simpa` calls (30 fixed, ~10 remain)
3. **Large expressions:** Manipulates sums of products of Γ and g terms
4. **Multiple simp passes:** Each `simp` call re-elaborates the entire context

---

## V. Hypotheses for Remaining Timeout

### Hypothesis A: The 2 `simpa [add_comm, ...]` calls (lines 3262, 3322)

These apply associativity lemmas to expressions with 8 addends each. Simp may be trying many permutations.

**Test:** Replace with:
```lean
simp only [add_comm, add_left_comm, add_assoc]
exact dCoord_add ...
```

---

### Hypothesis B: The 2 broad `simp`/`simp_all` calls (lines 2819, 2826)

These have 7-11 lemmas each and operate on large algebraic expressions.

**Test:** Replace with manual `rw` steps or `ring`

---

### Hypothesis C: Elaboration cascade

The 1404-line lemma may be causing Lean to re-elaborate downstream lemmas repeatedly.

**Test:** Break `alternation_dC_eq_Riem` into 5-10 helper lemmas

---

### Hypothesis D: Ring tactic on huge expressions

The final `ring` call may be operating on a massive expanded expression.

**Test:** Check if `ring` is hanging by adding `set_option trace.Meta.Tactic.ring true`

---

## VI. Recommended Next Steps

### Immediate (Low-Risk):

1. **Fix the 2 `simpa [add_comm, ...]` calls:**
   ```bash
   sed -i.fix5 -e '3262s/simpa \[add_comm, add_left_comm, add_assoc\]/simp only [add_comm, add_left_comm, add_assoc]; exact/' GR/Riemann.lean
   sed -i.fix5 -e '3322s/simpa \[add_comm, add_left_comm, add_assoc\]/simp only [add_comm, add_left_comm, add_assoc]; exact/' GR/Riemann.lean
   ```

2. **Test compilation** - if still slow, proceed to medium-risk

---

### Medium-Risk:

3. **Profile the specific lemma:**
   ```lean
   set_option profiler true in
   lemma alternation_dC_eq_Riem ...
   ```
   This will show exactly which tactic is hanging.

4. **Optimize the broad simp calls** (lines 2819, 2826):
   - Try replacing with manual `rw` or `ring`
   - Or use `simp only` with minimal lemma set

---

### Higher-Risk (Requires Understanding Proof Strategy):

5. **Modularize the lemma:**
   - Break into 5-10 helper lemmas for each stage
   - This reduces context size for each proof step

6. **Alternative proof strategy:**
   - Is there a more direct way to prove the alternation property without expanding all the sums?

---

## VII. Files Modified

**`GR/Riemann.lean`:**
- Line 1856: `simp [sumIdx_add]` → `simp only [sumIdx_add]`
- Lines 2516, 2521, 2526, 2531: `simpa using dCoord_g_via_compat_ext` → `exact`
- Lines 2643-2755 (12): `simpa using dCoord_mul` → `exact`
- Lines 2850-3577 (14): `simpa using dCoord_add` → `exact`

**Backups:**
- `Riemann.lean.bottleneck2` - Before Fix #2
- `Riemann.lean.simpa_fix3` - Before Fix #3
- `Riemann.lean.simpa_fix4_correct` - Before Fix #4

**Reports Created:**
- `ALTERNATION_LEMMA_ANALYSIS.md` - Detailed analysis of the lemma
- `BINARY_SEARCH_RESULTS.md` - Binary search methodology and findings
- `FIX4_IMPLEMENTATION_REPORT.md` - Fix #4 details
- `COMPREHENSIVE_RESEARCH_REPORT.md` - This document

---

## VIII. Questions for Junior Professor

### Q1: Should we continue tactical optimizations or restructure the proof?

We've fixed 30/40 expensive tactic calls, but the file still hangs. Should we:
- **Option A:** Fix the remaining 2 `simpa [add_comm, ...]` calls and 2 broad simp calls?
- **Option B:** Restructure the proof by modularizing the 1404-line lemma?

---

### Q2: What is the expected compilation time for this lemma?

With all tactical optimizations, what's a reasonable target? If it's inherently expensive (30-60s), maybe we should just document it rather than optimize further.

---

### Q3: Is there a simpler proof strategy for `alternation_dC_eq_Riem`?

The current proof:
1. Expands ContractionC into sumIdx of products
2. Applies linearity to split sums
3. Uses product rule on each term
4. Reassembles

Is there a more direct approach using higher-level lemmas about Christoffel symbols or covariant derivatives?

---

### Q4: Should we profile with per-declaration timing?

Would it help to add:
```lean
set_option profiler true in
set_option trace.profiler.output "alternation_dC_eq_Riem.prof" in
lemma alternation_dC_eq_Riem ...
```

This would show exactly which tactic inside the lemma is hanging.

---

## IX. Summary for User

**Work Completed:**
1. ✅ Applied 31 tactical optimizations (1 `simp only`, 30 `simpa` → `exact`)
2. ✅ Created comprehensive documentation of all findings
3. ✅ Identified remaining bottlenecks (2 `simpa [add_comm, ...]`, 2 broad `simp` calls)
4. ✅ Tested compilation - still times out after 4+ minutes

**Key Finding:**
The `alternation_dC_eq_Riem` lemma (1404 lines, 40+ expensive tactic calls) is the main bottleneck. We've fixed 75% of the expensive calls, but the file still doesn't compile within reasonable time.

**Conclusion:**
Further optimization requires either:
- Fixing the remaining 4 expensive tactic calls (low-risk)
- Modularizing the 1404-line lemma (higher-risk, better long-term)
- Profiling to identify if there's an unexpected bottleneck we haven't found

**Next Step:**
Awaiting Junior Professor's guidance on which approach to take.

---

**Status:** Research complete, awaiting direction.
