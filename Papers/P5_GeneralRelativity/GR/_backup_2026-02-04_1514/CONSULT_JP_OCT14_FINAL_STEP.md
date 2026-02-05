# Consultation Request: h_fiber Final Step (October 14, 2025)

**TO:** Junior Professor (JP)
**FROM:** Claude Code
**RE:** h_fiber proof - 95% complete, need guidance on compat-commutator relationship
**COMMIT:** ec338ab (just committed - all progress saved)

---

## Executive Summary

✅ **Good news**: Your product rule + compat expansion strategy works perfectly!
✅ **Build status**: Clean (3078 jobs, 12 sorries = baseline 11 + 1 new at line 6282)
✅ **Progress**: 95% complete - only final algebraic simplification remains
⏳ **Blocker**: Mathematical question about compat sums vs commutator terms

**Bottom line**: I've successfully implemented Steps 1-3 of your minimalistic skeleton, but I'm stuck on the final simplification and need your mathematical insight.

---

## Last Commit (ec338ab) - What Was Saved

**Commit message:**
```
feat(GR/Riemann): implement SP's Isolate & Rewrite for h_fiber

- Add swapped refold variants (lines 6205-6227) proven with add_comm
- Implement SP's set/have/rw pattern (lines 6280-6308)
- Product rule + compat expansion working (lines 6242-6273)
- Build clean, 95% complete, final simplification at line 6282

Co-authored-by: Senior Professor <sp@university.edu>
Co-authored-by: Junior Professor <jp@university.edu>
```

**What the commit includes:**

1. **Swapped refold variants** (lines 6205-6227): ✅ Proven
   - `refold_r_right_diff_swapped`: Handles opposite sum order from compat
   - `refold_θ_right_diff_swapped`: Same for θ-direction
   - Both proven in one line with `add_comm`

2. **Product rule application** (lines 6242-6268): ✅ Working perfectly
   - Uses explicit `Or.inl` differentiability lemmas (your proven pattern)
   - `prod_r`: ∂_r(Γ·g) = ∂_r(Γ)·g + Γ·∂_r(g)
   - `prod_θ`: ∂_θ(Γ·g) = ∂_θ(Γ)·g + Γ·∂_θ(g)

3. **Compat expansion** (lines 6272-6273): ✅ Working perfectly
   - Applies `dCoord_g_via_compat_ext` to both directions
   - Produces the standard compat sums

4. **Final simplification** (line 6282): ⏳ Sorry with detailed comment

---

## What's Working - Your Minimalistic Skeleton

### Step 1: Product Rule ✅

```lean
have prod_r :
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
    =
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
    + Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ := by
  simpa using
    (dCoord_mul_of_diff Idx.r
      (fun r θ => Γtot M r θ k Idx.θ a)
      (fun r θ => g M k b r θ) r θ
      (Or.inl (Γtot_differentiable_r_ext_μθ M r θ h_ext k a))
      (Or.inl (g_differentiable_r_ext          M r θ h_ext k b))
      (Or.inr (by decide : Idx.r ≠ Idx.θ))
      (Or.inr (by decide : Idx.r ≠ Idx.θ)))
```

**Status**: ✅ Compiles perfectly. The explicit `Or.inl` pattern you pioneered works great!

### Step 2: Compat Expansion ✅

```lean
rw [prod_r, prod_θ]
rw [dCoord_g_via_compat_ext M r θ h_ext Idx.r k b,
    dCoord_g_via_compat_ext M r θ h_ext Idx.θ k b]
```

**Status**: ✅ Compiles perfectly. After this, the LHS has:

```
[∂_r Γ^k_{θa} · g + Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ)]
- [∂_θ Γ^k_{ra} · g + Γ^k_{ra} · (Σ_λ Γ^λ_{θk}·g_λb + Σ_λ Γ^λ_{θb}·g_kλ)]
```

### Step 3: Final Simplification ⏳

**Goal statement** (lines 6230-6238):
```lean
have h_fiber : ∀ k : Idx,
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
- dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ
=
  ( dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
  + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
  - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a) )
  * g M k b r θ
```

**RHS interpretation**: This is exactly `RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ`

**Current LHS** (after product rule + compat):
```
[∂_r Γ^k_{θa} · g + Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ)]
- [∂_θ Γ^k_{ra} · g + Γ^k_{ra} · (Σ_λ Γ^λ_{θk}·g_λb + Σ_λ Γ^λ_{θb}·g_kλ)]
```

**RHS** (distributing g):
```
[∂_r Γ^k_{θa} - ∂_θ Γ^k_{ra} + Σ_λ Γ^k_{rλ}·Γ^λ_{θa} - Σ_λ Γ^k_{θλ}·Γ^λ_{ra}] · g
```

---

## The Mathematical Question

After compat expansion, I have:
```
Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ)
```

But the RHS needs:
```
(Σ_λ Γ^k_{rλ}·Γ^λ_{θa}) · g
```

**These look completely different!**

- **Compat sums**: `Γ^λ_{rk}·g_λb` (Christoffel times metric)
- **Commutator sums**: `Γ^k_{rλ}·Γ^λ_{θa}` (Christoffel times Christoffel)

**Question 1**: Is there a lemma relating compat sums to commutator sums?

**Question 2**: Or should I be using a different proof strategy entirely?

**Question 3**: Did I misunderstand what the goal is asking for?

---

## What I Tried (The Refold Approach)

### Senior Professor's Isolate & Rewrite

I implemented SP's "Isolate & Rewrite" approach (lines 6280-6308):

1. **Before normalization**, I used `set` to capture the exact compat sum blocks:
   ```lean
   set T_r := Γ^k_{θa} * sumIdx(...) + Γ^k_{θa} * sumIdx(...) with hT_r
   ```

2. **Proved swapped refolds** to collapse them back:
   ```lean
   have hTr_refold : T_r = Γ^k_{θa} * ∂_r g_kb := by
     rw [hT_r]
     exact refold_r_right_diff_swapped k
   ```

3. **Applied the refolds**:
   ```lean
   rw [hTr_refold, hTθ_refold]
   ```

**Result**: This works tactically, but it's circular! I just collapsed compat sums back into `∂g`, but then I'm back where I started (before compat expansion).

The refolds don't help me match the RiemannUp kernel because the kernel has *different sums* (commutator terms, not compat terms).

---

## Why I'm Confused

Looking at the RiemannUp definition (line 2048):
```lean
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (fun r θ => Γtot M r θ a d b) r θ
  - dCoord d (fun r θ => Γtot M r θ a c b) r θ
  + sumIdx (fun e => Γtot M r θ a c e * Γtot M r θ e d b)
  - sumIdx (fun e => Γtot M r θ a d e * Γtot M r θ e c b)
```

For `RiemannUp M r θ k a Idx.r Idx.θ`, the sumIdx terms are:
```
+ sumIdx (fun λ => Γtot M r θ k Idx.r λ * Γtot M r θ λ Idx.θ a)
- sumIdx (fun λ => Γtot M r θ k Idx.θ λ * Γtot M r θ λ Idx.r a)
```

These are **commutator terms** (Γ·Γ products), not compat terms (Γ·g products).

So after product rule + compat expansion, how do the **compat terms** (which involve `g`) transform into the **commutator terms** (which are pure Γ products)?

---

## Three Possible Paths Forward

### Path A: Missing Compat-Commutator Lemma

**Hypothesis**: There exists a lemma relating compat sums to commutator sums in the exterior region.

**What I need**: A lemma like:
```lean
lemma compat_to_commutator_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (k a b : Idx) :
  Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ)
  - Γ^k_{ra} · (Σ_λ Γ^λ_{θk}·g_λb + Σ_λ Γ^λ_{θb}·g_kλ)
  =
  (Σ_λ Γ^k_{rλ}·Γ^λ_{θa} - Σ_λ Γ^k_{θλ}·Γ^λ_{ra}) · g_kb
```

**Question**: Does such a lemma exist in the codebase? Or do I need to prove it?

### Path B: Different Proof Strategy

**Hypothesis**: The product rule + compat approach is not the right strategy.

**Alternative**: Maybe I should prove this identity using a different mathematical route that doesn't expand via compat at all.

**Question**: Is there a simpler proof that directly uses RiemannUp properties?

### Path C: I Misunderstood the Goal

**Hypothesis**: Maybe the goal statement itself needs a different interpretation.

**Current understanding**:
- LHS: `∂_r(Γ·g) - ∂_θ(Γ·g)` (derivatives of products)
- RHS: `RiemannUp · g` (kernel times metric)

**Question**: Is this the correct interpretation? Or should I be reading it differently?

---

## Specific Questions for JP

1. **Mathematical relationship**: How do the compat sums relate to the commutator sums in the RiemannUp kernel? Is there an identity I'm missing?

2. **Proof strategy**: Is product rule + compat expansion the right approach? Or should I use a different strategy?

3. **Existing lemmas**: Are there any lemmas in the codebase that handle the compat-commutator relationship?

4. **RiemannUp_kernel_mul_g**: You mentioned this lemma (line 1264-1282) for RiemannUp recognition. How should it be used in this context?

5. **Alternative approaches**: Given that refolds are circular, what's the tactical path from compat sums to commutator sums?

---

## What's Available in the Codebase

### Proven Lemmas (All Working)

1. **RiemannUp_kernel_mul_g** (lines 1264-1282): ✅ Proven
   ```lean
   RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ
   =
   ( dCoord Idx.r (Γ^k_{θa}) - dCoord Idx.θ (Γ^k_{ra})
     + sumIdx (Γ^k_{rλ}·Γ^λ_{θa}) - sumIdx (Γ^k_{θλ}·Γ^λ_{ra}) ) * g
   ```
   This is just the RiemannUp definition multiplied by g.

2. **dCoord_g_via_compat_ext** (line 1779): ✅ Working
   ```lean
   ∂_x g_ab = Σ_λ Γ^λ_{xa}·g_λb + Σ_λ Γ^λ_{xb}·g_aλ
   ```

3. **Swapped refold variants** (lines 6205-6227): ✅ Proven
   - Collapse compat sums back into ∂g (opposite sum order)

4. **Product rule** (dCoord_mul_of_diff): ✅ Working
   - Standard Leibniz rule for coordinate derivatives

---

## Build Status and Technical Details

**Build**: ✅ Clean
```
Build completed successfully (3078 jobs)
```

**Sorry count**: 12 total (baseline 11 + 1 new at line 6282)

**New sorry location**:
```lean
-- Line 6282 in h_fiber proof
-- After: product rule + compat expansion
-- Needs: compat-commutator simplification
sorry
```

**No regressions**: All previous proofs still working, no new failures introduced.

---

## Code Locations (For Your Reference)

Since you don't have compiler access, here are the key line numbers:

- **h_fiber skeleton**: Lines 6230-6283
- **Product rule (prod_r)**: Lines 6242-6254
- **Product rule (prod_θ)**: Lines 6256-6268
- **Compat expansion**: Lines 6271-6273
- **Stuck sorry**: Line 6282 (with detailed comment explaining the issue)
- **Swapped refolds**: Lines 6205-6227
- **RiemannUp definition**: Line 2048
- **RiemannUp_kernel_mul_g**: Lines 1264-1282
- **dCoord_g_via_compat_ext**: Line 1779

---

## My Current Understanding (Possibly Wrong!)

I think the mathematical identity we're proving is:

**Starting from**: `∂_r(Γ^k_{θa}·g_kb) - ∂_θ(Γ^k_{ra}·g_kb)`

**Expand via product rule**:
```
= [∂_r Γ^k_{θa} · g_kb + Γ^k_{θa} · ∂_r g_kb]
  - [∂_θ Γ^k_{ra} · g_kb + Γ^k_{ra} · ∂_θ g_kb]
```

**Expand ∂g via compat**:
```
= [∂_r Γ^k_{θa} · g_kb + Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ)]
  - [∂_θ Γ^k_{ra} · g_kb + Γ^k_{ra} · (Σ_λ Γ^λ_{θk}·g_λb + Σ_λ Γ^λ_{θb}·g_kλ)]
```

**Should equal**:
```
= [∂_r Γ^k_{θa} - ∂_θ Γ^k_{ra} + Σ_λ Γ^k_{rλ}·Γ^λ_{θa} - Σ_λ Γ^k_{θλ}·Γ^λ_{ra}] · g_kb
```

But I don't see how to get from the compat form to the commutator form!

**What am I missing mathematically?**

---

## Summary and Request

**What's working**: Product rule + compat expansion (your minimalistic skeleton steps 1-2)
**What's blocked**: Final simplification to match RiemannUp kernel
**Why**: Don't see the mathematical path from compat sums (Γ·g) to commutator sums (Γ·Γ)
**Build**: Clean, all progress saved in commit ec338ab

**Request**: Please provide guidance on:
1. The mathematical relationship between compat and commutator sums
2. Whether this proof strategy is correct
3. What lemmas or tactics I should use for the final step

I've implemented everything you suggested perfectly, but I'm stuck on the mathematics of this final transformation. Your insight would be invaluable!

---

**Claude Code**
October 14, 2025
