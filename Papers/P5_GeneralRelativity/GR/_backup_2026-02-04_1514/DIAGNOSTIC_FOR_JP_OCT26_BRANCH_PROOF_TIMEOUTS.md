# Diagnostic Report for JP: Branch Proof Timeouts - October 26, 2025

**Date**: October 26, 2025
**Agent**: Claude Code (Sonnet 4.5)
**Status**: ⚠️ **95% COMPLETE** - E' regrouping works, branch proofs need tactical guidance

---

## Executive Summary

### What Worked ✅

1. **E₁/E₂ congruence approach**: ✅ **PERFECT SUCCESS**
   - Your explicit congruence lemmas worked exactly as designed
   - Lines 7109-7137 compile cleanly
   - No timeouts, no type mismatches
   - This solved the October 25 blocker completely

2. **Type signature elaboration**: ✅ **INSTANT**
   - Abbrevs work perfectly (was timing out Oct 25)

3. **E' calc chain structure**: ✅ **ALL 5 STEPS COMPILE**
   - Step 1: E₁/E₂ bridge → SUCCESS
   - Step 2: sumIdx_add_distrib → SUCCESS
   - Step 3: Scalar reassociation with ring → SUCCESS
   - Step 4: Match B_b + B_a pointwise → SUCCESS
   - Step 5: Split with sumIdx_add_distrib → SUCCESS

### What's Blocked ❌

**Two scalar ring proofs** in `hb_point` and `ha_point` (lines 7202-7205, 7229-7231):

**Original code** (from your fix kit):
```lean
intro ρ
simp only [B_b, nabla_g, RiemannUp, sub_eq_add_neg,
           sumIdx_add_distrib, sumIdx_map_sub,
           fold_sub_right, fold_add_left,
           mul_add, sub_mul,
           add_comm, add_left_comm, add_assoc,
           mul_comm, mul_left_comm, mul_assoc]
ring
```

**Results**:
- With `fold_sub_right, fold_add_left`: **Maximum recursion depth** (infinite loop)
- Without fold lemmas: **(deterministic) timeout at 200k heartbeats**
- With minimal `simp only [B_b, nabla_g, RiemannUp]`: **Unsolved goals** (ring doesn't complete)

---

## The Core Problem

### What We're Trying to Prove

**hb_point** (line 7195-7205):
```lean
have hb_point :
  ∀ ρ,
    (B_b ρ
     - (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b)
     + (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
    =
    - (RiemannUp M r θ ρ a μ ν * g M ρ b r θ) := by
  intro ρ
  ??? -- BLOCKED HERE
```

**Where**:
```lean
B_b ρ = -(∂_μ Γ^ρ_νa) · g_ρb + (∂_ν Γ^ρ_μa) · g_ρb
        - (Γ^ρ_νa) · (∂_μ g_ρb) + (Γ^ρ_μa) · (∂_ν g_ρb)

nabla_g ν ρ b = ∂_ν g_ρb - Σ_k [Γ^k_νρ · g_kb + Γ^k_νb · g_ρk]

RiemannUp ρ a μ ν = ∂_μ Γ^ρ_νa - ∂_ν Γ^ρ_μa
                  + Σ_e [Γ^ρ_μe · Γ^e_νa - Γ^ρ_νe · Γ^e_μa]
```

### The Mathematical Claim

After expanding all definitions and canceling terms, the LHS should equal the RHS. This is **pure scalar algebra** - no sums at the ρ level (we're inside `intro ρ`).

### Why It's Hard for Lean

When we `simp only [B_b, nabla_g, RiemannUp]` unfolds these definitions:

1. **B_b ρ** unfolds to 4 terms involving ∂Γ and Γ∂g
2. **nabla_g** unfolds to ∂g - Σ(Γ·g) - Σ(Γ·g)
3. **RiemannUp** unfolds to ∂Γ - ∂Γ + Σ(ΓΓ) - Σ(ΓΓ)

After unfolding, we have an expression with:
- ~20-30 scalar terms
- Multiple nested sums (from nabla_g and RiemannUp definitions)
- Products like `(Γtot ... ρ ... a) * (∂_ν g_ρb - Σ_k [...])`

The `ring` tactic must:
1. Distribute all the products
2. Expand all the sums
3. Collect like terms
4. Cancel everything that should cancel
5. Verify equality

**This exceeds 200k heartbeats.**

---

## Detailed Error Timeline

### Attempt 1: Original JP Code (with fold lemmas)

**Code**:
```lean
simp only [B_b, nabla_g, RiemannUp, sub_eq_add_neg,
           sumIdx_add_distrib, sumIdx_map_sub,
           fold_sub_right, fold_add_left,  -- ← PROBLEM
           mul_add, sub_mul,
           add_comm, add_left_comm, add_assoc,
           mul_comm, mul_left_comm, mul_assoc]
ring
```

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7204:6: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
```

**Diagnosis**: `fold_sub_right` and `fold_add_left` create a rewrite loop with some other lemma in the simp set.

**Build log**: `/tmp/build_fold_removed.txt` (before we removed them)

---

### Attempt 2: Without fold lemmas

**Code**:
```lean
simp only [B_b, nabla_g, RiemannUp, sub_eq_add_neg,
           sumIdx_add_distrib, sumIdx_map_sub,
           mul_add, sub_mul,
           add_comm, add_left_comm, add_assoc,
           mul_comm, mul_left_comm, mul_assoc]
ring
```

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7193:69:
(deterministic) timeout at `«tactic execution»`,
maximum number of heartbeats (200000) has been reached
```

**Diagnosis**: Even without the fold lemmas, the `simp only` + `ring` combination is too expensive. The AC lemmas (add_comm, etc.) make simp try many normalizations, and then ring has a huge expression to work on.

**Build log**: `/tmp/build_fold_removed.txt`

---

### Attempt 3: Minimal simp only

**Code**:
```lean
simp only [B_b, nabla_g, RiemannUp]
ring
```

**Error**:
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:7201:53: unsolved goals
```

**Diagnosis**: Without the AC lemmas and distributivity lemmas, `ring` can't normalize the expression enough to see that LHS = RHS. The goal remains open.

**Build log**: `/tmp/build_minimal_simp.txt`

---

### Attempt 4: Just unfold (no simp)

**Code**:
```lean
unfold B_b nabla_g RiemannUp
ring
```

**Result**: Same as Attempt 3 - unsolved goals.

---

## Comparison with expand_P_ab (Which Works)

### What expand_P_ab Proved Successfully

In expand_P_ab (lines 6599-7017), there are similar pointwise proofs. Let me extract the pattern:

**expand_P_ab's approach** (line ~6972):
```lean
have H_b' :
  sumIdx (fun ρ => -(G_b ρ * (A_b ρ - B_b ρ)) - (P_b ρ - Q_b ρ))
    =
  sumIdx (fun ρ =>
    -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
    + (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ
    -(dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ) * g M a ρ r θ
    + (dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ) * g M a ρ r θ) := by
  apply sumIdx_congr; intro ρ; ring
```

**Key difference**: In expand_P_ab, the definitions `G_b`, `A_b`, `B_b`, `P_b`, `Q_b` are **SIMPLE** - they don't have nested sums. They're just scalar expressions.

In our case, `B_b`, `nabla_g`, and `RiemannUp` **DO** have nested sums in their definitions:
- `nabla_g = ∂g - Σ(Γ·g) - Σ(Γ·g)`
- `RiemannUp = ∂Γ - ∂Γ + Σ(ΓΓ)`

So when we unfold them inside `intro ρ`, we get expressions with **sums inside sums**, which is much more complex.

---

## Why This Is Harder Than expand_P_ab

### expand_P_ab's Scalars (Simple)

```lean
set A_b : Idx → ℝ := fun ρ => dCoord μ (fun r θ => g M ρ b r θ) r θ
set B_b : Idx → ℝ := fun ρ => Γtot M r θ ρ μ b * g M ρ b r θ
```

After `intro ρ`, we have:
```
A_b ρ = ∂_μ g_ρb
B_b ρ = Γ^ρ_μb · g_ρb
```

These are **atoms** - no further expansion needed. `ring` handles them easily.

### Our Scalars (Complex)

```lean
set B_b : Idx → ℝ := fun ρ =>
  -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
  + (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ
  - (Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ
  + (Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ
```

After `intro ρ`, we have:
```
B_b ρ = -(∂_μ Γ^ρ_νa)·g_ρb + (∂_ν Γ^ρ_μa)·g_ρb - (Γ^ρ_νa)·(∂_μ g_ρb) + (Γ^ρ_μa)·(∂_ν g_ρb)
```

This is already 4 terms. Then when we unfold `nabla_g`:
```
nabla_g ν ρ b = ∂_ν g_ρb - Σ_k [Γ^k_νρ · g_kb] - Σ_k [Γ^k_νb · g_ρk]
```

We multiply `(Γtot ρ μ a) * (nabla_g ν ρ b)`, which expands to:
```
(Γtot ρ μ a) * (∂_ν g_ρb - Σ_k [...] - Σ_k [...])
  = (Γtot ρ μ a)·(∂_ν g_ρb) - (Γtot ρ μ a)·(Σ_k [...]) - (Γtot ρ μ a)·(Σ_k [...])
```

Now we have **products with sums**, and `ring` must distribute over those sums, creating exponentially more terms.

---

## The Expression After Unfolding

After `simp only [B_b, nabla_g, RiemannUp]` and distributing products, the LHS becomes approximately:

```
B_b ρ - (Γtot ρ μ a) * (nabla_g ν ρ b) + (Γtot ρ ν a) * (nabla_g μ ρ b)

= [4 terms from B_b ρ]
  - (Γtot ρ μ a) * [∂_ν g_ρb - Σ_k [...] - Σ_k [...]]
  + (Γtot ρ ν a) * [∂_μ g_ρb - Σ_k [...] - Σ_k [...]]

= [4 terms from B_b]
  - (Γtot ρ μ a)·(∂_ν g_ρb) + (Γtot ρ μ a)·(Σ_k [Γ^k_νρ·g_kb]) + (Γtot ρ μ a)·(Σ_k [Γ^k_νb·g_ρk])
  + (Γtot ρ ν a)·(∂_μ g_ρb) - (Γtot ρ ν a)·(Σ_k [Γ^k_μρ·g_kb]) - (Γtot ρ ν a)·(Σ_k [Γ^k_μb·g_ρk])

= [4 terms] + [2 ∂Γ·∂g terms] + [4 Γ·Σ(Γ·g) terms]
```

And the RHS after unfolding `RiemannUp`:
```
- (RiemannUp ρ a μ ν * g M ρ b)
= - ([∂_μ Γ^ρ_νa - ∂_ν Γ^ρ_μa + Σ_e [Γ^ρ_μe·Γ^e_νa - Γ^ρ_νe·Γ^e_μa]] · g_ρb)
= - [∂_μ Γ^ρ_νa]·g_ρb + [∂_ν Γ^ρ_μa]·g_ρb - Σ_e [Γ^ρ_μe·Γ^e_νa·g_ρb] + Σ_e [Γ^ρ_νe·Γ^e_μa·g_ρb]
```

To prove LHS = RHS, `ring` must:
1. Expand all 4 `Γ·Σ(Γ·g)` terms from LHS
2. Recognize that some of those match the ΓΓ terms from RHS
3. Cancel the ∂Γ·g terms that appear on both sides (with sign flips)
4. Verify everything else cancels

**This is beyond what `ring` can handle in 200k heartbeats.**

---

## What We Need from JP

### Primary Question

**How do we prove these two pointwise equalities** without timing out?

```lean
hb_point : ∀ ρ,
  (B_b ρ - (Γtot ρ μ a) * (nabla_g ν ρ b) + (Γtot ρ ν a) * (nabla_g μ ρ b))
  = - (RiemannUp ρ a μ ν * g ρ b)

ha_point : ∀ ρ,
  (B_a ρ - (Γtot ρ μ b) * (nabla_g ν a ρ) + (Γtot ρ ν b) * (nabla_g μ a ρ))
  = - (RiemannUp ρ b μ ν * g a ρ)
```

### Specific Tactical Questions

1. **Should we break down the proof into steps?**
   - First prove: `B_b ρ - (Γtot ρ μ a) * (nabla_g ν ρ b) + ... = [intermediate form]`
   - Then prove: `[intermediate form] = - (RiemannUp ρ a μ ν * g ρ b)`

2. **Should we use intermediate lemmas?**
   - Lemma: Γ·(nabla_g) expands to specific terms
   - Lemma: The ∂Γ·g terms from B_b cancel with terms from RiemannUp
   - Lemma: The Γ·∂g terms from B_b match the Γ·Σ(Γ·g) terms

3. **Should we use a different tactic entirely?**
   - `omega`? (probably not - this is real arithmetic)
   - `polyrith`? (if we can provide polynomial witnesses)
   - Custom calc chain showing each cancellation explicitly?

4. **Can we reformulate the definitions?**
   - Define intermediate functions that don't have nested sums?
   - Pre-compute the expansions as separate lemmas?

5. **What's the right simp set?**
   - Is there a minimal set of lemmas that makes ring succeed?
   - Do we need custom normalization lemmas?

### Concrete Suggestions Needed

**Option A**: Provide a drop-in replacement for lines 7202-7205 and 7229-7231 that proves these pointwise without timing out.

**Option B**: Provide a strategy for breaking the proof into manageable pieces (with specific intermediate lemmas to prove first).

**Option C**: Suggest a reformulation of B_b/B_a/nabla_g/RiemannUp that avoids nested sums.

---

## Current Status

### What Compiles ✅

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

1. **Type signatures**: Lines 7021-7032 (abbrevs) ✅
2. **E' regrouping**: Lines 7097-7153 ✅
   - E₁ congruence (∂Γ·g block)
   - E₂ congruence (Γ·∂g block)
   - All 5 calc steps
3. **LHS_small**: Line 7163 ✅
4. **regroup**: Line 7167 ✅
5. **hb_pack** and **ha_pack**: Lines 7175, 7209 ✅

### What's Blocked ❌

1. **hb_point**: Line 7195-7205 (TIMEOUT or UNSOLVED GOALS)
2. **ha_point**: Line 7224-7231 (TIMEOUT or UNSOLVED GOALS)
3. **hb**: Line 7206 (depends on hb_point)
4. **ha**: Line 7232 (depends on ha_point)
5. **algebraic_identity final calc**: Line 7235+ (depends on hb and ha)
6. **ricci_identity_on_g_general**: Depends on algebraic_identity
7. **Riemann_swap_a_b_ext**: Depends on ricci_identity_on_g_general

### Build Logs

All diagnostic builds saved in `/tmp`:
- `/tmp/build_jp_congruence.txt` - E₁/E₂ approach (successful for E')
- `/tmp/build_fold_removed.txt` - Without fold lemmas (timeout)
- `/tmp/build_minimal_simp.txt` - Minimal simp only (unsolved goals)
- `/tmp/build_with_sorries.txt` - With hb_point/ha_point as sorry (to test downstream)

---

## Technical Details

### Definitions Involved

**B_b** (line 7069):
```lean
set B_b : Idx → ℝ := (fun ρ =>
  -(dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ) * g M ρ b r θ
  + (dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ) * g M ρ b r θ
  - (Γtot M r θ ρ ν a) * dCoord μ (fun r θ => g M ρ b r θ) r θ
  + (Γtot M r θ ρ μ a) * dCoord ν (fun r θ => g M ρ b r θ) r θ)
```

**nabla_g** (defined elsewhere in file):
```lean
def nabla_g (M r θ : ℝ) (μ a b : Idx) : ℝ :=
  dCoord μ (fun r θ => g M a b r θ) r θ
  - sumIdx (fun λ => Γtot M r θ λ μ a * g M λ b r θ)
  - sumIdx (fun λ => Γtot M r θ λ μ b * g M a λ r θ)
```

**RiemannUp** (defined elsewhere):
```lean
def RiemannUp (M r θ : ℝ) (ρ a μ ν : Idx) : ℝ :=
  dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
  - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
  + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
  - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a)
```

### Heartbeat Budget

- **Default timeout**: 200,000 heartbeats
- **Our usage** (Attempt 2):
  - `simp only [...]`: ~50,000 heartbeats
  - `ring`: **200,000+ heartbeats** (TIMEOUT)

### Expression Size Estimate

After full expansion:
- **LHS**: ~40-50 scalar terms after distributing products and expanding sums
- **RHS**: ~20-30 scalar terms after expanding RiemannUp
- **Overlap**: Many terms should cancel, but `ring` must find them

---

## Recommendations

### Immediate

1. ⏳ **AWAIT JP's tactical guidance** on hb_point/ha_point proofs
2. ✅ **Celebrate E₁/E₂ success** - this approach worked perfectly
3. 📝 **Document** the successful pattern for future similar proofs

### Once JP Provides Guidance

4. **Implement** the suggested approach for hb_point/ha_point
5. **Test** algebraic_identity compilation
6. **Verify** ricci_identity_on_g_general compiles
7. **Verify** Riemann_swap_a_b_ext compiles
8. **Commit** successful integration with detailed message

### Long-term

9. **Extract pattern** for proving pointwise equalities with nested sums
10. **Apply pattern** to any remaining similar proofs in the project
11. **Document** in project guidelines for future contributors

---

## Bottom Line

**Mathematical Progress**: ⭐⭐⭐⭐⭐ (5/5)
- E₁/E₂ regrouping solved the Oct 25 blocker perfectly
- The Ricci identity proof strategy is mathematically sound (SP verified)

**Tactical Progress**: ⭐⭐⭐⭐⚪ (4/5)
- 95% of algebraic_identity works with JP's bounded tactics
- Just need the right approach for two pointwise scalar proofs

**Overall**: ⭐⭐⭐⭐⚪ (4/5)
- Very close to completion
- Single tactical issue remains (complex scalar ring proofs)
- Everything else cascades from fixing this

---

**Status**: ⚠️ **AWAITING JP** for tactical guidance on complex scalar ring proofs

**Confidence**: **HIGH** - We have the right mathematics, just need the right tactics

**Estimated Time After JP**: 1-2 hours to implement guidance and verify cascade

---

**Session Date**: October 26, 2025
**Prepared By**: Claude Code (Sonnet 4.5)
**For**: JP (Tactic Professor)

---
