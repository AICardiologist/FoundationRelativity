# Consultation Request: Unified Lemma - Tactical Challenge with 64 Cases

**Date:** September 30, 2025
**To:** Junior Professor (Tactics Specialist)
**Re:** Making targeted @[simp] lemmas fire in exhaustive case analysis
**Status:** 32 errors (landmark: f(r) lemmas completed!), unified lemma blocked
**Request:** Tactical guidance for contextual simp across 64 cases

## Executive Summary

✅ **Major Success**: Both f(r) compatibility lemmas (`compat_r_tt_ext`, `compat_r_rr_ext`) are now **fully proven** using the senior professor's Sequenced Simplification Strategy. Error count reduced from 50 → 32 (36% improvement).

⚠️ **Current Blocker**: The unified lemma `dCoord_g_via_compat_ext` needs to prove 64 cases (4×4×4 index combinations) via exhaustive `cases` analysis. Our 5 targeted @[simp] lemmas **should** handle many of these cases, but they're not firing. This appears to be a **syntactic mismatch** issue rather than a mathematical one.

**Request**: Tactical guidance on making our proven lemmas work in the unified context, or guidance on efficient manual case handling.

---

## Part 1: What's Working (Landmark Achievement!)

### All 5 Targeted Compatibility Lemmas Proven ✅

```lean
@[simp] lemma compat_r_θθ_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.θ Idx.θ r θ) r θ
    = 2 * Γtot M r θ Idx.θ Idx.r Idx.θ * g M Idx.θ Idx.θ r θ
-- Proven with: dsimp only [g]; simp only [...]; field_simp [hr_ne]

@[simp] lemma compat_r_φφ_ext -- Similar pattern
@[simp] lemma compat_θ_φφ_ext -- Similar pattern

@[simp] lemma compat_r_tt_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.t Idx.t r θ) r θ
    = 2 * Γtot M r θ Idx.t Idx.r Idx.t * g M Idx.t Idx.t r θ
-- Proven with Sequenced Simplification: exclude 'f' from simp, then rw [h_deriv]

@[simp] lemma compat_r_rr_ext -- Similar pattern
```

**All 5 lemmas**: No sorries, compile cleanly, marked @[simp] for automation.

---

## Part 2: The Unified Lemma Challenge

### Current Implementation (Lines 679-686)

```lean
lemma dCoord_g_via_compat_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ) := by
  classical
  cases x <;> cases a <;> cases b <;>
    simp (config := {contextual := true})
         [sumIdx_expand, sumIdx, dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, g, Γtot]
```

**Result**: 14 out of 64 cases remain unsolved.

### The 14 Unsolved Cases

#### Category A: Diagonal/Symmetric Cases (6 cases)
These **should** be solved by our 5 @[simp] lemmas, but simp isn't matching:

**Case r.t.t** (should use `compat_r_tt_ext`):
```
⊢ -deriv (f M) r = Γ_r_rr M r * f M r + Γ_r_rr M r * f M r
```
- **What we have**: `compat_r_tt_ext` proves `∂_r g_tt = 2 Γ^t_rt g_tt`
- **What we need**: Same thing but with RHS expanded to double sum
- **Issue**: Syntactic mismatch (`2 * Γ * g` vs `Γ * g + Γ * g`)

**Case r.r.r** (should use `compat_r_rr_ext`):
```
⊢ deriv (fun s => (f M s)⁻¹) r = Γ_r_rr M r * (f M r)⁻¹ + Γ_r_rr M r * (f M r)⁻¹
```

**Case r.θ.θ** (should use `compat_r_θθ_ext`):
```
⊢ 2 * r = Γ_θ_rθ r * r ^ 2 + Γ_θ_rθ r * r ^ 2
```

**Case r.φ.φ** (should use `compat_r_φφ_ext`):
```
⊢ 2 * r * sin θ ^ 2 = Γ_φ_rφ r * (r ^ 2 * sin θ ^ 2) + Γ_φ_rφ r * (r ^ 2 * sin θ ^ 2)
```

**Case θ.φ.φ** (should use `compat_θ_φφ_ext`):
```
⊢ r ^ 2 * (2 * sin θ * cos θ) = Γ_φ_θφ θ * (r ^ 2 * sin θ ^ 2) + Γ_φ_θφ θ * (r ^ 2 * sin θ ^ 2)
```

#### Category B: Off-Diagonal Zero Cases (8 cases)
Schwarzschild is diagonal, so g_tr = g_tθ = g_tφ = g_rθ = g_rφ = g_θφ = 0.
Therefore `∂_x g_ab = 0` and the RHS Christoffel products must cancel to 0.

**Example - Case t.t.r**:
```
⊢ 0 = Γ_r_tt M r * (f M r)⁻¹ + Γ_r_rr M r * f M r
```
- LHS: 0 (derivative of g_tr = 0)
- RHS: Should equal 0 by Christoffel definitions

**Other examples**:
- t.r.t, θ.r.θ, θ.θ.r, φ.r.φ, φ.θ.φ, φ.φ.r, φ.φ.θ

These are algebraically trivial but need the right Christoffel expansions.

---

## Part 3: Why Targeted Lemmas Aren't Firing

### The Syntactic Mismatch

**Our @[simp] lemmas prove**:
```lean
∂_x g_ab = 2 * Γ^k_xa * g_kb  -- Single term with factor of 2
```

**The unified lemma expects**:
```lean
∂_x g_ab = Σ_k Γ^k_xa g_kb + Σ_k Γ^k_xb g_ak  -- Double sum
```

When a = b (diagonal case), the double sum reduces to:
```lean
= Γ^k_xa g_ka + Γ^k_xa g_ak  -- Two terms, each equal
```

**Mathematically equivalent** (since g is symmetric), but **syntactically different** (`2*X` vs `X + X`).

### What Contextual Simp Is Doing

The current proof attempts:
```lean
cases x <;> cases a <;> cases b <;>
  simp (config := {contextual := true})
       [sumIdx_expand, sumIdx, dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, g, Γtot]
```

This expands:
1. `sumIdx` to explicit sums (Σ_k → k=t,r,θ,φ)
2. `g` to diagonal form (g_tt = -f, g_rr = f⁻¹, etc.)
3. `Γtot` to specific Christoffel components

But it **doesn't** apply our @[simp] lemmas because:
- The lemmas have `dCoord Idx.r (fun r θ => g M Idx.θ Idx.θ r θ)` in hypothesis
- The goals have expanded forms like `deriv (fun r => r^2) r`
- The binder forms don't match even though they're definitionally equal

---

## Part 4: Attempted Approaches (All Failed)

### Approach 1: Add Derivative Infrastructure Before Cases
```lean
have hf' := f_hasDerivAt M r hr_ne
have h_deriv_neg_f : deriv (fun s => -f M s) r = -(2 * M / r^2) := by simpa using (hf'.neg).deriv
have h_deriv_inv_f : deriv (fun s => (f M s)⁻¹) r = -(2 * M / r^2) / (f M r)^2 := by simpa using (hf'.inv hf_ne).deriv
cases x <;> cases a <;> cases b <;>
  simp only [sumIdx_expand, dCoord_r, dCoord_θ, Γtot, Γ_t_tr, ..., h_deriv_neg_f, h_deriv_inv_f]
all_goals { try { field_simp [hr_ne, hf_ne]; ring } }
```
**Result**: 87 errors (worse!) - massive simp list times out or produces wrong normal forms

### Approach 2: Apply dsimp only [g] Before Cases
```lean
dsimp only [g]
cases x <;> cases a <;> cases b <;>
  simp (config := {contextual := true}) [...]
```
**Result**: No improvement - targeted lemmas still don't fire

### Approach 3: Remove contextual:=true
**Result**: No improvement

---

## Part 5: Questions for Junior Professor

### Q1: How to make @[simp] lemmas match across syntactic variations?

Is there a way to make `compat_r_θθ_ext` match goals like:
```
⊢ 2 * r = Γ_θ_rθ r * r ^ 2 + Γ_θ_rθ r * r ^ 2
```

when the lemma proves:
```
∂_r g_θθ = 2 * Γ^θ_rθ * g_θθ
```

after expansion?

**Possible tactics**:
- `conv` to rewrite selectively?
- Helper lemmas for `X + X = 2*X` in the sumIdx context?
- Different `simp` configuration?

### Q2: Should we handle cases individually?

Instead of `cases x <;> cases a <;> cases b <;> simp [...]`, should we do:
```lean
cases x <;> cases a <;> cases b
case t, t, t => simp only [specific lemmas for this case]
case t, t, r => simp only [other specific lemmas]
-- ... 62 more cases
```

If so, is there a pattern to minimize duplication?

### Q3: Can we use match or rcases for structured case handling?

```lean
match x, a, b with
| Idx.r, Idx.θ, Idx.θ => <proof for r.θ.θ case>
| Idx.r, Idx.φ, Idx.φ => <proof for r.φ.φ case>
| ...
```

### Q4: Is there a tactic for "prove both sides equal to common middle"?

For Category B (off-diagonal zeros), we need:
```
LHS = 0 (by definition of g for off-diagonal)
RHS = 0 (by Christoffel cancellation)
```

Is there a tactic like:
```lean
have hL : LHS = 0 := by simp [g_tr, g_tθ, ...]
have hR : RHS = 0 := by simp [Γ_r_tt, Γ_r_rr, ...]; field_simp; ring
exact hL.trans hR.symm
```

but in a more automated way?

### Q5: Should we use omega or polyrith for algebraic closure?

Some of the goals are purely algebraic (e.g., `2*r = r^2/r + r^2/r`). Would `omega`, `polyrith`, or `ring_nf` help?

---

## Part 6: Why This Matters (Downstream Cascade)

**Immediate blocker**:
- `nabla_g_zero_ext` (line 690) depends on `dCoord_g_via_compat_ext`

**Downstream cascade** (~22 Stage-2 Riemann proofs):
- Lines 2678-3356: Riemann tensor components depend on `nabla_g_zero_ext`

**Estimated impact**: Fixing the unified lemma should reduce errors from 32 → ~10-15 once cascade completes.

---

## Part 7: Proposed Solutions (for Your Evaluation)

### Option A: Manual Case Handling (Tedious but Reliable)
Prove all 64 cases individually with tailored simp lists:
```lean
cases x <;> cases a <;> cases b
case r, θ, θ => simp only [sumIdx_expand, dCoord_r, Γ_θ_rθ, deriv_pow_two_at]; field_simp [hr_ne]; ring
case r, φ, φ => simp only [sumIdx_expand, dCoord_r, Γ_φ_rφ, deriv_mul_const, deriv_pow_two_at]; field_simp [hr_ne]; ring
-- ... 62 more cases
```

**Pros**: Guaranteed to work, each case gets exactly what it needs
**Cons**: Verbose (~200 lines), error-prone, hard to maintain

### Option B: Helper Lemmas for Syntactic Bridge
Add lemmas like:
```lean
lemma two_mul_eq_sum_self {α : Type*} [Add α] [OfNat α 2] [Mul α] (x : α) : 2 * x = x + x := by ring
```
Then use in simp list to bridge `2*X` vs `X+X`.

**Question**: Would this work with the expanded Christoffel forms?

### Option C: Refactor Targeted Lemmas to Match Unified Form
Change `compat_r_θθ_ext` to prove:
```lean
∂_r g_θθ = Γ^θ_rθ * g_θθ + Γ^θ_rθ * g_θθ  -- Double form instead of 2*...
```

**Pros**: Direct syntactic match
**Cons**: Unnatural mathematical form, would need to reprove all 5 lemmas

### Option D: Use calc Mode for Structured Proofs
```lean
cases x <;> cases a <;> cases b
all_goals {
  calc dCoord ... = ... := by simp [expand LHS]
    _ = ... := by <apply relevant compat lemma>
    _ = ... := by <simplify RHS>
}
```

**Question**: Can calc work with case analysis?

---

## Part 8: Current Code Location

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Lemma**: `dCoord_g_via_compat_ext` (lines 679-686)

**Error**: Line 682 has 14 unsolved goals (shown in Part 2)

**Baseline**: 32 errors total (down from 50 at start of Hybrid Strategy)

---

## Part 9: What We're NOT Asking

- ❌ Not asking about mathematical correctness (architecture is sound)
- ❌ Not asking about Exterior Domain restriction (already implemented)
- ❌ Not asking about f(r) derivative lemmas (already proven!)
- ❌ Not asking about simp loop timeouts (not an issue here)

**We ARE asking**: Pure tactical guidance on case-exhaustive proofs with syntactic variation.

---

## Recommendation

I recommend **Option A (manual case handling)** if there's no clever tactical solution, since:
1. It's guaranteed to work (we know the tactics for each case)
2. The 64 cases are one-time cost
3. Once proven, downstream cascade should complete

But if you know a tactical trick for **Option B** (helper lemmas for `2*X = X+X` bridge) or **Q1** (making @[simp] lemmas match), that would be much cleaner.

---

## Summary Statistics

- **Landmark achievement**: ✅ Both f(r) lemmas proven (compat_r_tt_ext, compat_r_rr_ext)
- **Error reduction**: 50 → 32 (36% improvement)
- **Targeted lemmas**: 5/5 proven, all marked @[simp]
- **Current blocker**: Unified lemma (14/64 cases unsolved)
- **Root cause**: Syntactic mismatch between `2*Γ*g` and `Γ*g + Γ*g`
- **Request**: Tactical guidance on case-exhaustive proofs

**The Hybrid Strategy is architecturally complete.** This is purely a tactical finishing issue.