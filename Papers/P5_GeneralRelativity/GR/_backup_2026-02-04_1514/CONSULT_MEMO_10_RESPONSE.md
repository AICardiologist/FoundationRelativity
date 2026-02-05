# Response to Professor's Architectural Correction

**Date:** September 30, 2025
**Re:** Implementation of Exterior Domain architecture per professor's guidance
**Status:** 31 errors (same as before), architectural shift complete, proof work remains

## Executive Summary

Following the professor's **mandatory architectural correction** in their consultation memo, I have:

1. ✅ **Created `Exterior` structure** defining the valid domain (r > 2M)
2. ✅ **Implemented structural stubs** for `dCoord_g_via_compat_ext` and `nabla_g_zero_ext`
3. ✅ **Documented the mathematical issue** - unconditional lemmas are false at f(r)=0 due to Lean's 1/0=0
4. ⚠️ **Hit timeout issue** - the Unified REPP with bulk `simp` on 64 cases exceeds heartbeat limit

**Error count:** 31 (unchanged from before architectural shift)
**Sorries:** 3 working simple lemmas + 64 cases in unified lemma + legacy placeholder = ~68 total

## Part 1: Professor's Key Insight

### The Mathematical Failure

At the event horizon where f(r) = 0:
- **LHS:** `∂_r g_tt = -(2M/r²)` ≠ 0 (generally)
- **RHS:** `Γ^t_{rt} = M/(r²·f(r)) = M/(r²·0)` evaluates to **0** in Lean (since 1/0=0)
- **Contradiction:** The equation requires `-(2M/r²) = 0`, which is false

**Conclusion:** The compatibility equations are mathematically unsound at the event horizon under Lean's total function convention.

### The Mandatory Fix

**Must restrict to Exterior Domain** where:
- `0 < M` (positive mass)
- `2M < r` (outside event horizon)
- **Implies:** `r ≠ 0` and `f(r) ≠ 0`

## Part 2: What Was Implemented

### 1. Exterior Structure (Lines 19-34)

```lean
structure Exterior (M r θ : ℝ) : Prop where
  hM : 0 < M
  hr_ex : 2 * M < r

namespace Exterior

lemma r_ne_zero {M r θ : ℝ} (h : Exterior M r θ) : r ≠ 0 :=
  r_ne_zero_of_exterior M r h.hM h.hr_ex

lemma f_ne_zero {M r θ : ℝ} (h : Exterior M r θ) : f M r ≠ 0 :=
  ne_of_gt (f_pos_of_hr M r h.hM h.hr_ex)

end Exterior
```

### 2. Unified Compatibility Lemma (Lines 593-613)

```lean
lemma dCoord_g_via_compat_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ) := by
  cases x <;> cases a <;> cases b
  all_goals {
    classical
    have hr_ne := Exterior.r_ne_zero h_ext
    have hf_ne := Exterior.f_ne_zero h_ext
    dsimp only [g]
    sorry -- TODO: Apply Unified REPP with targeted simp
  }
```

**Status:** Structural skeleton in place, but proof incomplete due to timeout.

### 3. Metric Compatibility on Exterior (Lines 615-620)

```lean
lemma nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (c a b : Idx) :
  nabla_g M r θ c a b = 0 := by
  simp only [nabla_g]
  rw [dCoord_g_via_compat_ext M r θ h_ext]
  abel
```

**Status:** Proof is trivial once `dCoord_g_via_compat_ext` is proven.

## Part 3: The Timeout Problem

### What the Professor Prescribed

The Unified REPP script:
```lean
classical
have hr_ne := Exterior.r_ne_zero h_ext
have hf_ne := Exterior.f_ne_zero h_ext
dsimp only [g]
have hf' := f_hasDerivAt M r hr_ne
have h_deriv_neg_f : deriv (fun s => -f M s) r = -(2 * M / r^2) := by simpa using (hf'.neg).deriv
have h_deriv_inv_f : deriv (fun s => (f M s)⁻¹) r = -(2 * M / r^2) / (f M r)^2 := by simpa using (hf'.inv hf_ne).deriv
simp only [dCoord_r, dCoord_θ, ..., sumIdx, Γtot, ...] -- COMPREHENSIVE
field_simp [hr_ne, hf_ne, pow_two, sq]
try ring
```

### What Happened

When applied to all 64 cases with `all_goals`, the massive `simp only` call **times out** even with `maxHeartbeats 2000000`.

**Root cause:** The bulk `simp only` with ~30 lemmas applied to sumIdx expansions across 64 goals is too expensive.

### Attempted Solutions

1. **Increased heartbeats to 2M** - Still timed out
2. **Removed `sumIdx_expand`** from simp list - Still timed out
3. **Used `all_goals` instead of semicolon chaining** - Still timed out

### The Real Solution (Not Yet Implemented)

Per your reminder: **"don't use simple simp. usually we need to restrict the simp"**

The 64 cases need to be proven **individually** or in small groups with **case-specific simp lemmas**, not a universal blast. For example:

- **Case `x=r, a=θ, b=θ`:** Only needs `dCoord_r`, `Γ_θ_rθ`, `deriv_pow_two_at`
- **Case `x=r, a=t, b=t`:** Needs `dCoord_r`, `Γ_t_tr`, `h_deriv_neg_f`, `f`
- **Case `x=θ, a=φ, b=φ`:** Needs `dCoord_θ`, `Γ_φ_θφ`, `deriv_sin_sq_at`

Each case needs its own tailored simp list, not the union of all possible lemmas.

## Part 4: What Remains

### Immediate Work (for future sessions)

1. **Implement 64 cases individually** using pattern from working lemmas:
   ```lean
   case t, t, t => classical; dsimp only [g]; simp only [specific lemmas]; field_simp [hr_ne, hf_ne]; ring
   case t, t, r => ...
   -- etc for all 64
   ```

2. **Or use conv/rw for surgical application** instead of simp

3. **Once `dCoord_g_via_compat_ext` works**, `nabla_g_zero_ext` will follow trivially

### Downstream Impact

Many Stage-2 Riemann proofs depend on `nabla_g_zero`. Once the Exterior version works, those should cascade to completion (or need Exterior hypotheses added).

## Part 5: Comparison to Previous Approach

### What Changed

| Aspect | Before (Unconditional) | After (Exterior) |
|--------|------------------------|------------------|
| **Scope** | All (r, θ) | r > 2M only |
| **Soundness** | False at f=0 | Mathematically valid |
| **Hypotheses** | None | Exterior M r θ |
| **Sorries** | 13 (for singular cases) | 64 (for proof work) |
| **Architecture** | Individual compat_* lemmas | Unified exhaustive lemma |

### What Stayed the Same

- **Binder opacity solution:** `dsimp only [g]` still critical
- **Simple lemmas work:** compat_r_θθ, compat_r_φφ, compat_θ_φφ remain fully proven
- **Error count:** 31 (architectural shift didn't break anything)

## Part 6: Key Takeaways

1. **The professor was absolutely right** - the unconditional approach was mathematically unsound
2. **The Exterior restriction is mandatory** - not optional
3. **The Unified REPP script is correct in principle** - but needs case-by-case application, not bulk simp
4. **The binder opacity fix was real progress** - `dsimp only [g]` works and is essential
5. **"Don't use simple simp"** - restrict simp to exactly what each case needs

## Part 7: Recommendation for Next Session

**Option A: Incremental Implementation**
- Pick 5-10 simple cases (θ-θ, φ-φ, off-diagonal zeros)
- Prove them with targeted simp
- Build confidence in the pattern
- Gradually expand to all 64

**Option B: Ask Professor for Tactic Guidance**
- The bulk simp timeout might be a known issue
- Professor may have a preferred tactic sequence
- Or a lemma factorization that avoids the explosion

**Option C: Hybrid Approach**
- Use `dCoord_g_via_compat_ext` for simple cases only
- Keep individual helper lemmas for complex f(r) cases
- Reduces from 64 to ~20 cases

## Conclusion

The architectural shift to Exterior domain is **mandatory and correct**. The structural implementation is complete. The remaining work is **purely tactical** - applying the Unified REPP to 64 cases with appropriately restricted simp calls.

The error count (31) is unchanged, meaning the refactor was clean. We're now on sound mathematical footing and ready for the case-by-case proof work.