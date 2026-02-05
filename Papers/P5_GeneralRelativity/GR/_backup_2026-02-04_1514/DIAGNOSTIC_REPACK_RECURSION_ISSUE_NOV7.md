# DIAGNOSTIC: Repack Step Causes Recursion Depth Errors

**Date**: November 7, 2025
**Status**: 🔴 **Critical blocker - helpers hit HasDistribNeg ℝ + recursion depth**

---

## Problem Summary

After applying Paul's fixes (adding `rw [hb_pack]` / `rw [ha_pack]` at the start of helpers), the build has **29 errors** (vs. baseline 18, target 17).

**Root cause**: The `rw [hb_pack]` step transforms the LHS from three separate `sumIdx` terms into a single `sumIdx` with a complex integrand. When the subsequent calc chain uses `ring` tactics, they hit recursion depth on the larger term.

**Error at line 8906**:
```
failed to synthesize
  HasDistribNeg ℝ
maximum recursion depth has been reached
```

---

## The Architectural Mismatch

### Original `hb` Structure (lines 8955-9154)

```lean
have hb :
  (sumIdx B_b)                                   -- Three separate sumIdx
  - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
=
  - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) := by
  classical

  -- NO use of hb_pack here
  simp only [nabla_g, RiemannUp, sub_eq_add_neg]   -- Expands on unpacked form

  have payload_cancel : ... := by
    have h : ∀ ρ, ... := by intro ρ; ring   -- ring works fine on unpacked form
```

**Key observation**: Original `hb` does NOT use `hb_pack`. It starts with three separate `sumIdx` terms and expands them with `simp only`. The `ring` tactics work because the terms are not nested under a large outer `sumIdx`.

### Helper `hb_plus` Structure (lines 8747-8952)

```lean
have hb_plus :
  (sumIdx B_b)                                   -- Same LHS
  - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
  + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
=
  - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
  + rho_core_b := by                           -- Different RHS (with + rho_core_b)
  classical

  rw [hb_pack]  -- ← Paul's fix: packs into single sumIdx
  -- After this step, LHS is:
  --   sumIdx (fun ρ => B_b ρ - ... + ...)

  simp only [nabla_g, sub_eq_add_neg]   -- Expands on PACKED form (large term)

  have payload_cancel : ... := by
    have h : ∀ ρ, ... := by intro ρ; ring   -- ← FAILS: recursion depth on large term
```

**Problem**: After `rw [hb_pack]`, the LHS becomes a single `sumIdx` with a complex integrand. When `simp only` expands it, the term gets very large. Then `ring` under the `intro ρ` explodes because it's working under a big outer `sumIdx`.

---

## Paul's Guidance vs. Reality

### What Paul Said (Nov 6 message)

> "Your helpers didn't start by re‑packing the LHS. The LHS of each helper is
>     ((sumIdx B_b - Cμa) + Cνa)
> which is exactly the splay you want to expose. But the calc you copied from hb/ha expects the packed pointwise form
>     sumIdx (fun ρ => B_b ρ - Cμa_term ρ + Cνa_term ρ)
> The first line of each helper must be
>     rw [hb_pack] / rw [ha_pack],
> to transform the LHS from the splay form the helper declares into the packed pointwise form the ΓΓ-block chain expects."

### What I Observe

The calc I copied from `hb` does NOT expect the packed form - it expects the unpacked form (three separate `sumIdx`). The original `hb` never uses `hb_pack`.

**Question**: Did Paul mean something different by "the calc you copied"? Or is there a different version of the calc that works on the packed form?

---

## Possible Solutions

### Option A: Don't Use `rw [hb_pack]` in Helpers

**Rationale**: The helper's LHS already matches the original `hb`'s LHS (three separate `sumIdx`). Just copy the calc as-is without repacking.

**Issue**: Paul explicitly said "The first line of each helper must be rw [hb_pack] / rw [ha_pack]". But this conflicts with the observation that the calc doesn't work on the packed form.

### Option B: Rewrite the Calc to Work on Packed Form

**Rationale**: Transform the calc to work on `sumIdx (fun ρ => B_b ρ - ... + ...)` instead of three separate `sumIdx`.

**Issue**: This requires understanding the mathematical steps and rewriting ~200 lines of proof. Not clear if this is feasible or if I'll introduce new errors.

### Option C: Use Two-Stage Approach

**Rationale**:
1. First, use the original `hb` calc to prove `LHS_unpacked = RHS_no_rho`
2. Then, add a small calc step to extend to `LHS_unpacked = RHS_with_rho`
3. Finally, apply `hb_pack` backward to get `LHS_packed = RHS_with_rho`

**Issue**: Unclear if this avoids the type mismatch issue Paul identified in the first place.

### Option D: Ask Paul for Clarification

**Question to ask**: "The calc inside the original `hb` works on the unpacked form (three separate sumIdx). After `rw [hb_pack]`, we have a single packed sumIdx, and the calc hits recursion depth on `ring` tactics. Should the helpers:
1. NOT use `rw [hb_pack]` and just copy the calc as-is?
2. Use a different calc chain that works on the packed form?
3. Use some other approach?"

---

## Error Distribution

**29 errors total**:

**Inside `hb_plus` helper** (lines 8747-8952): 6 errors
- 8906, 8921, 8927, 8938, 8942, 8960

**Inside `ha_plus` helper** (lines 9170-9372): 6 errors
- 9327, 9342, 9348, 9360, 9364, 9382

**Outside helpers** (baseline + shifted): 17 errors
- 9110, 9125, 9142, 9146 (original `hb`)
- 9530, 9545, 9563, 9567 (original `ha`)
- 9607, 9612, 9853 (`branches_sum` and nearby)
- 10054, 10068, 10137, 10248 (downstream)

**Pattern**: 12 new errors in the helpers themselves, plus baseline errors shifted by the code additions.

---

## Sample Error

**Line 8906**: `simpa [neg_mul_right₀] using this`

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8906:6: failed to synthesize
  HasDistribNeg ℝ
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
```

This is inside the `h_insert_delta_for_b` section, which uses `insert_delta_right_diag`. The error is the classic "HasDistribNeg ℝ + recursion depth" that Paul warned about when using `ring` under binders.

---

## Request for Guidance

**Questions**:

1. **Should helpers use `rw [hb_pack]` at all?**
   The original `hb` doesn't use it, and adding it causes recursion depth errors.

2. **If yes, how should the calc be adapted?**
   The current calc assumes unpacked form (three separate `sumIdx`). Does a packed-form version exist?

3. **Alternative approach?**
   Is there a simpler way to expose the "with-ρ" forms without duplicating the entire calc chain?

**Build log**: `build_step9_paul_fixes_nov6.txt` (29 errors, 12 in helpers)

---

**Status**: Blocked - need guidance on whether to use `rw [hb_pack]` and how to adapt the calc if we do.
