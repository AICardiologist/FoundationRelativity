# Action Plan: Fixing the Riemann Tensor Formalization - October 16, 2025

## Executive Summary

**Problem Identified**: The h_fiber lemma attempts to prove a pointwise identity that is mathematically FALSE (confirmed by senior professor's counterexample).

**Solution**: Delete h_fiber entirely and prove the identity **only at the sum level** where it is likely mathematically correct.

---

## Immediate Actions

### 1. Delete h_fiber Proof (Lines ~6257-6427)

**What to delete:**
- The entire `have h_fiber : ∀ k, ...` proof including:
  - Product rule application (prod_r, prod_θ)
  - Diagonal/off-diagonal case split
  - All of JP's patches (PATCH A-D) applied to h_fiber
  - The `by_cases k = b` logic
  - All 120+ lines of the proof

**What to keep:**
- Lines 6429-6445: The sum-level lifting logic
  - `have h_pt : (fun k => ...) = (fun k => ...)`
  - `have h_sum := congrArg ...`
  - `simpa [RiemannUp_kernel_mul_g] using h_sum`

**Why**: h_fiber proves a false statement. The sum-level proof doesn't need it.

---

### 2. Implement Direct Sum-Level Proof

The lemma `regroup_right_sum_to_RiemannUp_NEW` currently relies on h_fiber. We need to prove it directly.

**Current structure (lines 5938-6445):**
```lean
lemma regroup_right_sum_to_RiemannUp_NEW ... := by
  -- Part 1: Product rule (KEEP - already working)
  have h_pt : ... pack_right_slot_prod ...  [lines 5955-5965]
  have h_sum_linearized : ... [lines 5968-5980]

  -- Part 2: Metric compatibility expansion (MISSING - need to add)
  -- This is where h_fiber was supposed to help, but it's false

  -- Part 3: Recognize RiemannUp (KEEP - already working)
  simpa [RiemannUp_kernel_mul_g] using h_sum  [line 6445]
```

**New structure needed:**
```lean
lemma regroup_right_sum_to_RiemannUp_NEW ... := by
  -- Part 1: Product rule (✅ KEEP)
  have h_pt_prod : (fun k =>
    ∂_r(Γ·g) - ∂_θ(Γ·g)) = (fun k =>
    (∂_r Γ)·g + Γ·(∂_r g) - ((∂_θ Γ)·g + Γ·(∂_θ g)))
  := by funext k; exact pack_right_slot_prod ...

  -- Part 2: Expand ∂g via metric compatibility (❌ NEW - TO IMPLEMENT)
  have expand_dg : ∀ k,
    Γ^k_θa · ∂_r g_kb - Γ^k_ra · ∂_θ g_kb
    = Σλ [Γ^k_θa · (Γ^λ_rk·g_λb + Γ^λ_rb·g_kλ)]
      - Σλ [Γ^k_ra · (Γ^λ_θk·g_λb + Γ^λ_θb·g_kλ)]
  := by ...

  -- Part 3: Sum over k and apply Fubini (❌ NEW - TO IMPLEMENT)
  have fubini_step :
    Σₖ Σλ [...] = Σλ Σₖ [...]
  := by ...

  -- Part 4: Relabel indices and match (❌ NEW - TO IMPLEMENT)
  have relabel :
    Σλ Σₖ [Γ^k_θa · Γ^λ_rk · g_λb]
    = Σₖ [Σλ (Γ^k_rλ · Γ^λ_θa) · g_kb]  [after λ↔k swap]
  := by ...

  -- Part 5: Recognize RiemannUp (✅ KEEP)
  simpa [RiemannUp_kernel_mul_g] using ...
```

---

## Detailed Implementation Steps

### Step 2.1: Prove Metric Compatibility Expansion

**Lemma needed:**
```lean
lemma dCoord_g_via_compat_expanded
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ k b : Idx) :
  dCoord μ (fun r θ => g M k b r θ) r θ
  = sumIdx (fun λ => Γtot M r θ λ μ k * g M λ b r θ)
  + sumIdx (fun λ => Γtot M r θ λ μ b * g M k λ r θ)
:= by
  -- Use existing dCoord_g_via_compat_ext, but need to show
  -- the negative sums equal the positive form via metric symmetry
  sorry  -- TODO: implement
```

**This is the key missing piece!** The existing `dCoord_g_via_compat_ext` gives:
```lean
∂_μ g_kb = -(Σ Γ·g) - (Σ Γ·g)
```

But we need it in the **positive form** with explicit indices for substitution.

---

### Step 2.2: Substitute and Distribute

**Lemma needed:**
```lean
have substitute_dg : ∀ k,
  Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
  - Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ
  =
  sumIdx (fun λ => Γtot M r θ k Idx.θ a * Γtot M r θ λ Idx.r k * g M λ b r θ)
  + sumIdx (fun λ => Γtot M r θ k Idx.θ a * Γtot M r θ λ Idx.r b * g M k λ r θ)
  - sumIdx (fun λ => Γtot M r θ k Idx.r a * Γtot M r θ λ Idx.θ k * g M λ b r θ)
  - sumIdx (fun λ => Γtot M r θ k Idx.r a * Γtot M r θ λ Idx.θ b * g M k λ r θ)
:= by
  intro k
  rw [dCoord_g_via_compat_expanded, dCoord_g_via_compat_expanded]
  ring
```

---

### Step 2.3: Apply Fubini to Swap Sums

**Lemma needed:**
```lean
have fubini_swap :
  sumIdx (fun k => sumIdx (fun λ => Γtot M r θ k Idx.θ a * Γtot M r θ λ Idx.r k * g M λ b r θ))
  =
  sumIdx (fun λ => sumIdx (fun k => Γtot M r θ k Idx.θ a * Γtot M r θ λ Idx.r k * g M λ b r θ))
:= by
  simp only [sumIdx_swap_comm]
```

This should be straightforward - just commutativity of finite sums.

---

### Step 2.4: Relabel and Match

After swapping, relabel the first dummy index from λ to k and the second from k to λ:

```lean
  sumIdx (fun λ => sumIdx (fun k => Γ^k_θa · Γ^λ_rk · g_λb))
= sumIdx (fun k => sumIdx (fun λ => Γ^λ_θa · Γ^k_rλ · g_kb))  [swap k↔λ names]
= sumIdx (fun k => sumIdx (fun λ => Γ^k_rλ · Γ^λ_θa · g_kb))  [mul_comm]
```

This matches the first ΓΓ term in RiemannUp!

Similarly process the other 3 sums to get all 4 ΓΓ terms.

---

## Infrastructure Lemmas Needed

### A. sumIdx_swap_comm (Might already exist)
```lean
lemma sumIdx_swap_comm {f : Idx → Idx → ℝ} :
  sumIdx (fun i => sumIdx (fun j => f i j))
  = sumIdx (fun j => sumIdx (fun i => f i j))
```

### B. dCoord_g_via_compat_positive (New)
```lean
lemma dCoord_g_via_compat_positive
    (M r θ : ℝ) (h_ext : Exterior M r θ) (μ k b : Idx) :
  dCoord μ (fun r θ => g M k b r θ) r θ
  = sumIdx (fun λ => Γtot M r θ λ μ k * g M λ b r θ)
  + sumIdx (fun λ => Γtot M r θ λ μ b * g M k λ r θ)
```

### C. Index relabeling lemmas (Standard)
```lean
lemma sumIdx_relabel {f g : Idx → ℝ} (h : ∀ i, f i = g i) :
  sumIdx f = sumIdx g
```

---

## Expected Proof Length

**Estimated**: 150-250 lines for the complete sum-level proof, broken down as:
- Metric compatibility expansion: 40-60 lines
- Substitution and distribution: 30-50 lines
- Fubini swaps (4 terms): 40-60 lines
- Index relabeling and matching: 40-80 lines

---

## Timeline Estimate

**With correct infrastructure**: 2-4 hours
**Including debugging**: 4-8 hours

---

## Success Criteria

1. ✅ `regroup_right_sum_to_RiemannUp_NEW` compiles without sorry
2. ✅ No use of h_fiber anywhere in the proof
3. ✅ All mathematics happens at sum level (no false pointwise claims)
4. ✅ Senior professor's concerns fully addressed

---

## Next Immediate Step

**Delete h_fiber proof block (lines 6257-6427) and replace with direct sum-level proof following the structure above.**

---

**Research Team**
October 16, 2025
