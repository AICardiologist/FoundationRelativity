# Fix #4 Implementation Report - dCoord_add Fixes

**Date:** October 4, 2025
**Status:** ✅ APPLIED - Testing in progress

---

## Summary

Applied Fix #4: Replaced 14 `simpa using dCoord_add` calls with `exact dCoord_add` in the `alternation_dC_eq_Riem` lemma.

---

## Lines Fixed

All 14 instances successfully replaced:

| Line | Before | After |
|------|--------|-------|
| 2850 | `simpa using dCoord_add c P_t P_r r θ` | `exact dCoord_add c P_t P_r r θ` |
| 2854 | `simpa using dCoord_add c P_θ P_φ r θ` | `exact dCoord_add c P_θ P_φ r θ` |
| 2918 | `simpa using dCoord_add c P2_t P2_r r θ` | `exact dCoord_add c P2_t P2_r r θ` |
| 2922 | `simpa using dCoord_add c P2_θ P2_φ r θ` | `exact dCoord_add c P2_θ P2_φ r θ` |
| 2983 | `simpa using dCoord_add d Q_t Q_r r θ` | `exact dCoord_add d Q_t Q_r r θ` |
| 2987 | `simpa using dCoord_add d Q_θ Q_φ r θ` | `exact dCoord_add d Q_θ Q_φ r θ` |
| 3052 | `simpa using dCoord_add d Q2_t Q2_r r θ` | `exact dCoord_add d Q2_t Q2_r r θ` |
| 3056 | `simpa using dCoord_add d Q2_θ Q2_φ r θ` | `exact dCoord_add d Q2_θ Q2_φ r θ` |
| 3450 | `simpa using dCoord_add c RC_t RC_r r θ` | `exact dCoord_add c RC_t RC_r r θ` |
| 3454 | `simpa using dCoord_add c RC_θ RC_φ r θ` | `exact dCoord_add c RC_θ RC_φ r θ` |
| 3516 | `simpa using dCoord_add d RD_t RD_r r θ` | `exact dCoord_add d RD_t RD_r r θ` |
| 3520 | `simpa using dCoord_add d RD_θ RD_φ r θ` | `exact dCoord_add d RD_θ RD_φ r θ` |
| 3572 | `simpa using dCoord_add μ A B r θ` | `exact dCoord_add μ A B r θ` |
| 3577 | `simpa using dCoord_add μ C D r θ` | `exact dCoord_add μ C D r θ` |

---

## Remaining `simpa [...]` Calls

### Two instances with associativity normalization (NOT fixed):

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

**Note:** These use `simpa` with associativity lemmas because the goal likely has a different associative grouping than `dCoord_add`'s conclusion. Cannot simply replace with `exact`.

---

## Backups

- `Riemann.lean.simpa_fix4_failed` - Initial attempt with wrong line numbers
- `Riemann.lean.simpa_fix4_correct` - Before applying corrected fix

---

## Testing

Build started at 21:35 (approx):
```bash
cd /Users/quantmann/FoundationRelativity && \
  time lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | \
  tee /tmp/fix4_correct_build.txt | tail -100
```

**Expected outcome:**
- If successful: Compilation time should improve significantly
- If still slow: Remaining bottlenecks are the 2 `simpa [add_comm, ...]` calls or other simp-heavy tactics

---

## Total Fixes Applied So Far

| Fix | Description | Lines | Status |
|-----|-------------|-------|--------|
| #1 | `nabla_g_eq_dCoord_sub_C`: `simp [sumIdx_add]` → `simp only [sumIdx_add]` | 1856 | ✅ |
| #2 | `simpa using dCoord_g_via_compat_ext` → `exact` | 2516, 2521, 2526, 2531 | ✅ |
| #3 | `simpa using dCoord_mul` → `exact` | 2643-2755 (12 lines) | ✅ |
| #4 | `simpa using dCoord_add` → `exact` | 2850-3577 (14 lines) | ✅ |
| **Total** | | **31 expensive tactic calls fixed** | **✅** |

---

## Next Steps

1. **If build succeeds quickly (<30s):** SUCCESS! Document and report.
2. **If build still times out:** Investigate lines 3262 and 3322, or look for other expensive calls.
3. **Profile specific sections** if needed to pinpoint remaining bottlenecks.

---

**Status:** Awaiting build results...
