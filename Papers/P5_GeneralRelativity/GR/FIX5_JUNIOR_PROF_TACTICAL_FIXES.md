# Fix #5: Junior Professor's Tactical Optimizations

**Date:** October 4, 2025
**Status:** ✅ ALL APPLIED - Testing in progress

---

## Summary

Applied all tactical optimizations recommended by Junior Professor to eliminate the three independent causes of compilation timeout:

1. ✅ Global profiler removed
2. ✅ AC-heavy `simpa` calls optimized (3 instances)
3. ✅ Broad `simp`/`simp_all` calls replaced with targeted tactics
4. ✅ `sumIdx_expand` disabled locally in `alternation_dC_eq_Riem`

---

## Fixes Applied

### Fix #5a: Remove Global Profiler (Line 24)

**Before:**
```lean
namespace Schwarzschild
open Idx

set_option profiler true  -- TRIAGE: Profile to find slow declarations
```

**After:**
```lean
namespace Schwarzschild
open Idx

-- REMOVED global profiler - use `set_option profiler true in` per-declaration only
-- set_option profiler true  -- TRIAGE: Profile to find slow declarations
```

**Impact:** Eliminates cumulative profiler overhead across entire file.

---

### Fix #5b: Add Local Profiler + Disable sumIdx_expand (Line 2467)

**Before:**
```lean
lemma alternation_dC_eq_Riem (M r θ : ℝ) (a b c d : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  ...
  := by
  -- Following junior professor's 6-step mechanical plan
```

**After:**
```lean
set_option profiler true in
lemma alternation_dC_eq_Riem (M r θ : ℝ) (a b c d : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  ...
  := by
  -- Disable sumIdx expansion for this lemma (prevents goal explosion)
  local attribute [-simp] sumIdx_expand sumIdx2_expand

  -- Following junior professor's 6-step mechanical plan
```

**Impact:**
- Confines profiling to this specific lemma only
- Prevents `simp` from expanding sums into 4 branches repeatedly

---

### Fix #5c: Fix `simpa using .symm` (Line 2821)

**Before:**
```lean
have hμt_rw :
  g M a Idx.t r θ * RiemannUp M r θ Idx.t b c d
  + g M b Idx.t r θ * RiemannUp M r θ Idx.t a c d
  =
  (Stage2_mu_t_preview.LHS_mu_t_chunk M r θ a b c d) := by
  -- Use the preview lemma in reverse direction:
  simpa using (Stage2_mu_t_preview.mu_t_component_eq M r θ a b c d).symm
```

**After:**
```lean
have hμt_rw :
  g M a Idx.t r θ * RiemannUp M r θ Idx.t b c d
  + g M b Idx.t r θ * RiemannUp M r θ Idx.t a c d
  =
  (Stage2_mu_t_preview.LHS_mu_t_chunk M r θ a b c d) := by
  -- Use the preview lemma in reverse direction:
  exact (Stage2_mu_t_preview.mu_t_component_eq M r θ a b c d).symm
```

**Impact:** Avoids unnecessary simp before exact.

---

### Fix #5d: Replace Broad simp/simp_all (Lines 2824-2832)

**Before:**
```lean
-- Rewrite the μ=t pair in-place. `simp [hμt_rw, ...]` will find it inside the big sum.
simp [hμt_rw,
      add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc]  -- structure only (no re-expansion)

-- Now normalize add/mul structure with regrouping helpers
simp_all [add_comm, add_left_comm, add_assoc,
          mul_comm, mul_left_comm, mul_assoc,
          nabla_g_zero, dCoord_const, dCoord_zero_fun,
          regroup₂, regroup_same_right]
```

**After:**
```lean
-- Rewrite the μ=t pair in-place, then normalize
rw [hμt_rw]
simp only [nabla_g_zero, dCoord_const, dCoord_zero_fun,
           regroup₂, regroup_same_right]
ring_nf
```

**Impact:**
- Deterministic `rw` instead of expensive AC search
- `simp only` with 5 specific lemmas instead of 11 lemmas + AC
- `ring_nf` once at the end instead of multiplicative AC in simp

---

### Fix #5e: AC-heavy simpa #1 (Lines 3267-3270)

**Before:**
```lean
+ dCoord c (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ := by
  -- single application of binary linearity
  simpa [add_comm, add_left_comm, add_assoc]
    using dCoord_add c
      (fun r θ => P_t  r θ + P_r  r θ + P_θ  r θ + P_φ  r θ)
      (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ
```

**After:**
```lean
+ dCoord c (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ := by
  -- single application of binary linearity (AC normalization then exact)
  simp only [add_comm, add_left_comm, add_assoc]
  exact dCoord_add c
    (fun r θ => P_t  r θ + P_r  r θ + P_θ  r θ + P_φ  r θ)
    (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ
```

**Impact:** Separates AC normalization from lemma application; reduces search space.

---

### Fix #5f: AC-heavy simpa #2 (Lines 3327-3330)

**Before:**
```lean
+ dCoord d (fun r θ => Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ) r θ := by
  simpa [add_comm, add_left_comm, add_assoc]
    using dCoord_add d
      (fun r θ => Q_t  r θ + Q_r  r θ + Q_θ  r θ + Q_φ  r θ)
```

**After:**
```lean
+ dCoord d (fun r θ => Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ) r θ := by
  simp only [add_comm, add_left_comm, add_assoc]
  exact dCoord_add d
    (fun r θ => Q_t  r θ + Q_r  r θ + Q_θ  r θ + Q_φ  r θ)
```

**Impact:** Same as #5e.

---

## Total Fixes in Session

| Session | Fix Description | Count | Status |
|---------|----------------|-------|--------|
| **Previous** | `simp [...]` → `simp only [...]` | 1 | ✅ |
| **Previous** | `simpa using dCoord_g_via_compat_ext` → `exact` | 4 | ✅ |
| **Previous** | `simpa using dCoord_mul` → `exact` | 12 | ✅ |
| **Previous** | `simpa using dCoord_add` → `exact` | 14 | ✅ |
| **Fix #5** | Remove global profiler | 1 | ✅ |
| **Fix #5** | Disable sumIdx_expand locally | 1 | ✅ |
| **Fix #5** | `simpa using .symm` → `exact` | 1 | ✅ |
| **Fix #5** | Broad simp/simp_all → rw + simp only + ring_nf | 2 | ✅ |
| **Fix #5** | AC-heavy `simpa` → `simp only` + `exact` | 2 | ✅ |
| **TOTAL** | | **38** | **100%** |

---

## Why These Fixes Matter

### 1. Global Profiler (10-30s overhead)
The global profiler adds overhead to *every* declaration in the file cumulatively. For a 5900-line file, this can add 10-30 seconds of pure overhead.

### 2. sumIdx_expand (Exponential explosion)
When `sumIdx_expand` is in the simp set, any `simp` call may expand finite sums:
```lean
sumIdx f  →  f Idx.t + f Idx.r + f Idx.θ + f Idx.φ
```
In a lemma with nested sums, this causes exponential goal growth.

### 3. AC in simp (Combinatorial explosion)
With `add_comm`, `add_left_comm`, `add_assoc` in simp, Lean tries many permutations to match patterns. For expressions with 8+ addends, this is exponential.

### 4. Broad simp/simp_all (Large search space)
`simp` with 11 lemmas on a massive expression tree searches through many rewrite possibilities. Using `rw` for known rewrites and `ring_nf` once at the end is much faster.

---

## Expected Outcome

With all fixes applied:
- **Global profiler overhead:** ~10-30s → 0s
- **sumIdx expansion:**  Multiple expansions → None
- **AC normalization:** Expensive simp search → Targeted `simp only`
- **Broad simp calls:** 11-lemma search → Deterministic `rw` + 5-lemma `simp only` + `ring_nf`

**Expected total compilation time:** 10-30 seconds (vs 4+ minute timeout before)

---

## Backups

- `Riemann.lean.simpa_fix4_correct` - Before Fix #5

---

## Testing

Build started at 21:42 (approx):
```bash
cd /Users/quantmann/FoundationRelativity && \
  time lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | \
  tee /tmp/fix5_all_tactical_fixes_build.txt | tail -100
```

**Status:** Testing...

---

**Next:** If successful, document final results. If still slow, consider modularizing the 1404-line lemma.
