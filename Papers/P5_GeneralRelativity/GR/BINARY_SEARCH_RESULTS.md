# Binary Search Results - Compilation Bottlenecks

**Date:** October 4, 2025
**Status:** 🔍 **IN PROGRESS** - Found 2 bottlenecks, more remain

---

## Summary

Successfully applied binary search and found **2 major bottlenecks**, applied fixes, but **full file still times out**. There are likely more bottlenecks remaining.

---

## Bottleneck #1: `nabla_g_eq_dCoord_sub_C` (Line 1852)

**Discovery:**
- Line 1783: 7.3s (simp 13s)
- Line 1850: 7.4s (simp 13.1s)
- Line 1870: TIMEOUT (2+ minutes)
- **Culprit:** Lines 1852-1857

**Original Code:**
```lean
lemma nabla_g_eq_dCoord_sub_C (M r θ : ℝ) (d a b : Idx) :
  nabla_g M r θ d a b = dCoord d (fun r θ => g M a b r θ) r θ - ContractionC M r θ d a b := by
  unfold nabla_g ContractionC
  simp [sumIdx_add]  ← PROBLEM: Broad simp search
  ring
```

**Problem:** After unfolding `nabla_g` and `ContractionC`, `simp [sumIdx_add]` expands massive `sumIdx` expressions involving Γ and g terms, causing simp to search through huge expression spaces.

**Fix Applied:**
```lean
lemma nabla_g_eq_dCoord_sub_C (M r θ : ℝ) (d a b : Idx) :
  nabla_g M r θ d a b = dCoord d (fun r θ => g M a b r θ) r θ - ContractionC M r θ d a b := by
  unfold nabla_g ContractionC
  simp only [sumIdx_add]  ← FIXED: Narrow search
  ring
```

**Result:** Line 2000 now compiles in 7.9s (vs timeout before)

---

## Bottleneck #2: `alternation_dC_eq_Riem` - `simpa` calls (Lines 2516, 2521, 2526, 2531)

**Discovery:**
- Line 2000: 7.9s (simp 16.3s) after fix #1
- Line 2125: 7.8s (simp 20.1s)
- Line 2250: TIMEOUT
- Line 2218: 8.2s (simp 24.9s)

**Original Code (4 instances):**
```lean
have hcompat_c_kb : ∀ k, dCoord c (fun r θ => g M k b r θ) r θ =
    sumIdx (fun m => Γtot M r θ m c k * g M m b r θ) +
    sumIdx (fun m => Γtot M r θ m c b * g M k m r θ) := by
  intro k; simpa using dCoord_g_via_compat_ext M r θ hExt c k b
```

**Problem:** `simpa` invokes simp before `exact`, which is unnecessary since the goal and the lemma match exactly. Each `simpa` call triggers expensive simp search.

**Fix Applied:**
```lean
have hcompat_c_kb : ∀ k, dCoord c (fun r θ => g M k b r θ) r θ =
    sumIdx (fun m => Γtot M r θ m c k * g M m b r θ) +
    sumIdx (fun m => Γtot M r θ m c b * g M k m r θ) := by
  intro k; exact dCoord_g_via_compat_ext M r θ hExt c k b
```

**Lines fixed:** 2516, 2521, 2526, 2531

**Result:** Partial improvement, but **line 2600 still times out**.

---

## Remaining Problem

**Current Status:**
- Line 2500: 10.2s (simp 28.6s)
- Line 2600: TIMEOUT
- Full file: TIMEOUT (3+ minutes)

**Hypothesis:** The lemma `alternation_dC_eq_Riem` itself (lines 2467-???) is still too expensive, likely due to:
1. Other `simp` calls with broad search inside the proof
2. Large algebraic goals being passed to `ring`
3. Repeated applications of expensive lemmas

The lemma is several hundred lines long and contains complex algebraic manipulations with `sumIdx`, `Γtot`, and `g`.

---

## Profiler Evidence

### After Fix #1 (line 2000):
```
simp                     16.3s
tactic execution         5.85s
typeclass inference      4.72s
ring                     342ms
```

### After Fix #2 (line 2500):
```
simp                     28.6s  ← Still increasing!
tactic execution         6.5s
typeclass inference      5.51s
ring                     305ms
```

Simp time is still growing by ~12 seconds between lines 2000-2500, suggesting more expensive simp calls in that range.

---

## Questions for Junior Professor

### Q1: Is `alternation_dC_eq_Riem` the expected bottleneck?

This lemma starts at line 2467 and appears to be very long. You mentioned it uses `simpa using dCoord_g_via_compat_ext` which we've now fixed. But the lemma still causes timeouts.

**Should we:**
1. Replace this lemma entirely with a simpler proof strategy?
2. Break it into smaller helper lemmas?
3. Look for more `simp` calls inside the proof and narrow them?

### Q2: What is the expected proof strategy for `alternation_dC_eq_Riem`?

The lemma appears to be proving:
```lean
lemma alternation_dC_eq_Riem (M r θ : ℝ) (a b c d : Idx)
    (hExt : Exterior M r θ) :
  dCoord c (dCoord d (fun r θ => g M a b r θ) r θ) r θ -
  dCoord d (dCoord c (fun r θ => g M a b r θ) r θ) r θ
    = Riemann M r θ a b c d
```

Is there a more direct way to prove this without expanding all the sumIdx and Γ terms?

### Q3: Should we profile this specific lemma?

Would it help to add `set_option profiler true in` before `alternation_dC_eq_Riem` to see exactly which tactic inside it is slow?

### Q4: Are there other known expensive lemmas after line 2600?

Once we fix `alternation_dC_eq_Riem`, are there other lemmas we should be aware of that might cause similar issues?

---

## Next Steps (Awaiting Guidance)

**Option A: Continue Binary Search**
- Narrow down exactly which part of `alternation_dC_eq_Riem` is slow
- Apply targeted fixes to individual simp calls

**Option B: Refactor `alternation_dC_eq_Riem`**
- If you have a simpler proof strategy, we can replace the whole lemma
- Break into smaller helper lemmas to reduce elaboration complexity

**Option C: Profile the Specific Lemma**
- Add per-declaration profiling to see which tactic is expensive
- Might reveal whether it's simp, ring, or something else

---

## Files Modified

**`GR/Riemann.lean`:**
- Line 1856: `simp [sumIdx_add]` → `simp only [sumIdx_add]`
- Lines 2516, 2521, 2526, 2531: `simpa using` → `exact`

**Backups:**
- `Riemann.lean.bottleneck2` - Before fix #2
- `Riemann.lean.bisect4` - Various bisection points

---

## Request

Please advise on how to proceed with `alternation_dC_eq_Riem` or point us to other bottlenecks we should address first.

Thank you!
