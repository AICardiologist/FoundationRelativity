# R_tθtθ Component Lemma Implementation Report - Algebraic Closure Issue

**Date:** October 5, 2025
**Context:** Phase 2 Component Lemmas - Iterating on Single Case (R_tθtθ)
**Status:** BLOCKED on algebraic closure tactic

---

## Executive Summary

Following user guidance to "iterate a single case to make sure one case work first," I focused exclusively on implementing the R_tθtθ component lemma. The structural expansion steps work correctly, but the proof is **blocked on a pure algebraic closure** that neither `ring`, `nlinarith`, nor manual rewrites can solve.

**Current state:** R_tθtθ proof reduces to a single algebraic equation in ℝ that should be provable but cannot be closed with available tactics.

---

## Implementation Approach

### Current R_tθtθ Implementation (GR/Riemann.lean:4934-4954)

```lean
/-- Component: R_tθtθ = M·f(r)/r -/
lemma Riemann_tθtθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M * f M r / r := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  -- Contract and expand
  rw [Riemann_contract_first M r θ Idx.t Idx.θ Idx.t Idx.θ]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_θ, sumIdx_expand]
  simp only [Γtot]
  simp only [g]

  -- Kill derivative of constant and expand Γ symbols
  simp only [deriv_const', Γ_t_tr, Γ_r_θθ]

  -- Expand f, normalize, and close
  simp only [f, div_eq_mul_inv]
  field_simp [hr_nz]
  sorry  -- BLOCKED: Cannot close algebraic goal
```

---

## The Algebraic Closure Problem

### Goal After `field_simp [hr_nz]`

```lean
⊢ -(r * M ^ 2 * (r - M * 2)⁻¹ * 4) + r ^ 2 * M * (r - M * 2)⁻¹ + M ^ 3 * (r - M * 2)⁻¹ * 4 = r * M - M ^ 2 * 2
```

**Context:**
- `M r θ : ℝ`
- `hM : 0 < M`
- `hr_ex : 2 * M < r`
- `hr_nz : r ≠ 0`
- `hf_nz : f M r ≠ 0`

### Mathematical Analysis

This is a **pure algebraic equation in ℝ** that should be provable by:
1. Factoring out `(r - M*2)⁻¹` from LHS:
   ```
   LHS = (-4rM² + r²M + 4M³) / (r - M*2)
   RHS = rM - 2M²
   ```

2. Multiplying both sides by `(r - M*2)`:
   ```
   -4rM² + r²M + 4M³ = (rM - 2M²)(r - M*2)
                     = r²M - rM·M·2 - 2M²r + 2M²·M·2
                     = r²M - 2rM² - 2M²r + 4M³
                     = r²M - 4rM² + 4M³
   ```
   ✓ Checks out algebraically

---

## Tactics Attempted (All Failed)

### 1. Direct `ring` ❌
```lean
field_simp [hr_nz]
ring
```
**Error:** `unsolved goals` - `ring` cannot handle the `(r - M*2)⁻¹` terms

---

### 2. `ring_nf` + `norm_num` + `ring` ❌
```lean
field_simp [hr_nz]
ring_nf
norm_num
ring
```
**Error:** `unsolved goals` - normalization doesn't help

---

### 3. Manual rewrite of `2*M` to `M*2` ❌
```lean
simp only [f, div_eq_mul_inv]
rw [show 2 * M = M * 2 by ring]  -- Try to normalize before field_simp
field_simp [hr_nz]
ring
```
**Error:** `unsolved goals` - the rewrite is in the wrong direction (goal already has `M*2`)

---

### 4. `nlinarith` with hints ❌
```lean
field_simp [hr_nz]
nlinarith [sq_nonneg r, sq_nonneg M, mul_comm M 2]
```
**Error:** `linarith failed to find a contradiction` - not linear enough

---

### 5. Using helper lemma `r_mul_f` ❌

**Available helper:**
```lean
lemma r_mul_f (M r : ℝ) (hr_nz : r ≠ 0) : r * f M r = r - 2 * M
```

**Problem:** After expanding `f := 1 - 2*M/r` and running `field_simp`, the goal contains `(r - M*2)⁻¹`, but `r_mul_f` produces `r - 2*M`. Ring normalizes `2*M` to `M*2`, breaking pattern matching.

Attempted:
```lean
field_simp [hr_nz]
rw [←r_mul_f M r hr_nz]  -- Try to substitute back
ring
```
**Error:** `Did not find an occurrence of the pattern r - 2*M` (because goal has `r - M*2`)

---

## Root Cause Analysis

### The Commutativity Trap

1. **Expand f:** `f M r = 1 - 2*M/r`
2. **Expand div:** `= 1 - 2*M * r⁻¹`
3. **field_simp normalization:** Lean's `ring` tactic normalizes multiplication:
   - `2 * M` → `M * 2` (canonical form puts constants on right)
4. **Pattern mismatch:** Helper lemmas use `r - 2*M`, but goal has `r - M*2`
5. **Ring can't recognize equivalence** when terms are under division: `(r - 2*M)⁻¹` ≠ `(r - M*2)⁻¹` for pattern matching purposes

---

## What Should Work (But Doesn't)

The equation is mathematically trivial:
```
-(r*M²*(r-M*2)⁻¹*4) + r²*M*(r-M*2)⁻¹ + M³*(r-M*2)⁻¹*4 = r*M - M²*2
```

**Expected closure:** `field_simp` should clear denominators, then `ring` should solve the polynomial equation. But this **does not happen**.

---

## Specific Questions for Junior Professor

### Q1: Is there a tactic I'm missing?

After `field_simp [hr_nz]`, what tactic closes goals of this form?
- Tried: `ring`, `ring_nf`, `nlinarith`, manual rewrites
- Is there a `polyrith`, `omega`, or other numeric solver that would work?

### Q2: Should I avoid expanding f(r) entirely?

Your original guidance said "expand f LATE." But perhaps for this case, should I:
- Keep `f M r` symbolic throughout?
- Work directly with `M * f M r / r` on RHS?
- Use `r_mul_f` earlier in the proof chain?

### Q3: Is the component lemma statement itself wrong?

**Current statement:**
```lean
lemma Riemann_tθtθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M * f M r / r
```

Should it be stated differently to avoid this algebraic closure issue? For example:
```lean
-- Alternative: Keep f symbolic in RHS?
Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M / r - 2 * M ^ 2 / r ^ 2
```

### Q4: Concrete Working Example Request

Could you provide a **complete, compilable proof** of R_tθtθ showing exactly how to handle this algebraic closure? Even if it uses tactics I haven't tried (e.g., `decide`, `norm_cast`, `simp_all`, etc.), seeing a working example would clarify the approach.

---

## Build Validation

All testing done with **`lake build`** (authoritative), not `lake env lean`.

**Current error count:** 14 errors (baseline was 9)
- 3 pre-existing infrastructure errors
- 1 R_tθtθ error (line 4936) ← **THIS ONE**
- 5 other component lemma errors (lines 4911, 4959, 4981, 5003, 5041)
- 4 diagonal Ricci case errors (lines 5088, 5138, 5177, 5209)
- 1 "No goals" error (line 5048)

---

## Files Modified

### `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Phase 1 Helpers (lines 4899-4905):** ✅ Compile successfully
```lean
lemma r_mul_f (M r : ℝ) (hr_nz : r ≠ 0) : r * f M r = r - 2 * M
lemma one_minus_f (M r : ℝ) : 1 - f M r = 2 * M / r
```

**R_tθtθ (lines 4934-4954):** ❌ BLOCKED on algebraic closure

**Other 5 component lemmas:** ❌ Not yet debugged (waiting for R_tθtθ pattern to work)

---

## Alternative Paths Forward

### Option A: Skip R_tθtθ, Try Simpler Case

Move to R_trtr (uses derivative calculators - different pattern) and see if it closes more easily.

**Pros:** May bypass this specific algebraic issue
**Cons:** R_trtr is the most complex case (needs derivative calculators)

---

### Option B: Prove Intermediate Algebraic Lemma

Create a standalone lemma proving the algebraic identity:
```lean
lemma rthetatheta_algebra (M r : ℝ) (hM : 0 < M) (hr : 2 * M < r) (hr_nz : r ≠ 0) :
    -(r * M ^ 2 * (r - M * 2)⁻¹ * 4) + r ^ 2 * M * (r - M * 2)⁻¹ + M ^ 3 * (r - M * 2)⁻¹ * 4
    = r * M - M ^ 2 * 2 := by
  -- HOW TO PROVE THIS?
```

Then use it in R_tθtθ proof.

**Pros:** Isolates the problem
**Cons:** Still need to know the tactic to prove it

---

### Option C: Use calc Block with Explicit Steps

```lean
field_simp [hr_nz]
calc -(r * M ^ 2 * (r - M * 2)⁻¹ * 4) + r ^ 2 * M * (r - M * 2)⁻¹ + M ^ 3 * (r - M * 2)⁻¹ * 4
    = ((-4) * r * M ^ 2 + r ^ 2 * M + 4 * M ^ 3) * (r - M * 2)⁻¹ := by ring
  _ = (r ^ 2 * M - 4 * r * M ^ 2 + 4 * M ^ 3) * (r - M * 2)⁻¹ := by ring
  _ = (r * M - 2 * M ^ 2) * (r - M * 2) * (r - M * 2)⁻¹ := by ring  -- ← THIS STEP FAILS
  _ = (r * M - 2 * M ^ 2) * 1 := by field_simp [...]
  _ = r * M - M ^ 2 * 2 := by ring
```

**Pros:** Step-by-step breakdown
**Cons:** The key step `(r²M - 4rM² + 4M³) = (rM - 2M²)(r - M*2)` still needs `ring` to recognize the factorization, which it doesn't

---

## Request

**Most helpful response:** A complete working proof of R_tθtθ showing the exact sequence of tactics to close the algebraic goal after `field_simp`. This would serve as a template for all other component lemmas.

**Alternative helpful response:** Clarification on whether the component lemma approach is fundamentally flawed for this use case, and if so, what alternative proof structure would work better.

---

## Current Code State

**Latest commit:** Working directory has R_tθtθ with `sorry` at line 4954
**Baseline:** c173658 (9 errors with lake build)
**Current status:** 14 errors (regression due to incomplete component lemma implementations)

**Recommendation:** Do not commit current state until R_tθtθ proof completes successfully.

---

**Generated:** October 5, 2025
**Author:** Claude Code
**Purpose:** Request tactical guidance on algebraic closure for R_tθtθ component lemma
**Priority:** HIGH - Blocking all other component lemma implementations
