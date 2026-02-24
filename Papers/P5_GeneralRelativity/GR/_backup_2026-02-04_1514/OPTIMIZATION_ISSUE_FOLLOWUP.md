# Optimization Implementation Issue - Follow-up

**Date:** October 4, 2025
**Status:** 🔴 **STILL NOT COMPILING**
**To:** Junior Professor

---

## Summary

We implemented your dispatcher pattern optimization exactly as specified:

1. ✅ Added `compat_r_tt_chart` with localized `field_simp` (lines 1743-1751)
2. ✅ Added `compat_r_rr_chart` with localized `field_simp` (lines 1754-1762)
3. ✅ Replaced `dCoord_g_via_compat_chart` body with match dispatcher (lines 1768-1773)

**Result:** Still timing out after 3-5 minutes (same as before).

---

## What We Implemented

### Atomic Lemma 1 (lines 1743-1751):
```lean
@[simp] lemma compat_r_tt_chart
    (M r θ : ℝ) (hC : Chart M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.t Idx.t r θ) r θ
    = 2 * Γtot M r θ Idx.t Idx.r Idx.t * g M Idx.t Idx.t r θ := by
  classical
  have hf' : deriv (fun s => - f M s) r = -(2 * M / r^2) := by
    simpa using (f_hasDerivAt M r hC.hr |>.neg).deriv
  simp [dCoord_r, g, Γtot, Γ_t_tr, hf', one_div, inv_pow]
  field_simp [hC.hr, hC.hf]
```

### Atomic Lemma 2 (lines 1754-1762):
```lean
@[simp] lemma compat_r_rr_chart
    (M r θ : ℝ) (hC : Chart M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.r Idx.r r θ) r θ
    = 2 * Γtot M r θ Idx.r Idx.r Idx.r * g M Idx.r Idx.r r θ := by
  classical
  have hf' : deriv (f M) r = 2 * M / r^2 := by
    simpa using (f_hasDerivAt M r hC.hr).deriv
  simp [dCoord_r, g, Γtot, Γ_r_rr, hf', one_div, inv_pow]
  field_simp [hC.hr, hC.hf]
```

### Dispatcher (lines 1764-1773):
```lean
lemma dCoord_g_via_compat_chart (M r θ : ℝ) (hC : Chart M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ) := by
  match x, a, b with
  | Idx.r, Idx.t, Idx.t => simp only [compat_r_tt_chart M r θ hC, sumIdx_expand, g, Γtot]; ring
  | Idx.r, Idx.r, Idx.r => simp only [compat_r_rr_chart M r θ hC, sumIdx_expand, g, Γtot]; ring
  | _, _, _ =>
      -- All other 62 cases are zero or trivial
      sorry
```

Note: We sorryed the catchall to test if the atomic lemmas compile. **They don't.**

---

## Debugging Results

**Test 1:** Atomic lemmas + sorry catchall → **TIMEOUT** (3+ minutes)
**Test 2:** Full Route A implementation → **TIMEOUT** (100+ minutes)

**Conclusion:** The bottleneck is in `compat_r_tt_chart` and/or `compat_r_rr_chart` themselves.

---

## Potential Issues

### Issue 1: Missing `Γ_r_rr` Definition?

In `compat_r_rr_chart`, we use:
```lean
simp [dCoord_r, g, Γtot, Γ_r_rr, hf', one_div, inv_pow]
```

We found references to `Γ_r_rr` in the backup files (`.route_a_full`) but couldn't locate a definition in the current codebase. **Question:** Does `Γ_r_rr` need to be defined? Or is it supposed to unfold via `Γtot`?

### Issue 2: `field_simp` Still Too Expensive?

Even though we only call `field_simp [hC.hr, hC.hf]` **once** in each atomic lemma (instead of 64 times), it's still hanging. **Question:** Is `field_simp` inherently too slow for this context?

### Issue 3: The `@[simp]` Attribute

We marked both atomic lemmas with `@[simp]`. **Question:** Could this be causing simp to loop or try to apply them in unwanted contexts?

---

## Questions

1. **Is `Γ_r_rr` supposed to exist as a standalone definition?** If so, where should we define it?

2. **Should we use a different tactic than `field_simp`?** Perhaps `norm_num` or manual `rw` steps?

3. **Is the `@[simp]` attribute correct for these lemmas?** Or should they only be called explicitly?

4. **Did we miss a prerequisite step?** For example, do we need to prove differentiability lemmas for the atomic cases first?

---

## Current State

**Files:**
- `GR/Riemann.lean` - Has the atomic lemmas + dispatcher with catchall sorryed
- `GR/Riemann.lean.route_a_full` - Backup of full Route A implementation
- Build status: **TIMEOUT** (no compilation errors, just hangs)

**Next Steps:** Awaiting your guidance on which issue to address.

---

**Priority:** URGENT - Blocking all progress
**Response needed:** ASAP

Thank you!
