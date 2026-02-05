# Revised Implementation Plan: Riemann Tensor via Γ₁ - October 16, 2025

## Executive Summary

**Mathematical Status**: The h_fiber pointwise identity is **mathematically FALSE** (verified by counterexample). The correct approach uses **Christoffel symbols of the first kind (Γ₁)** to prove the identity at the sum level.

**Implementation Strategy**: 4-phase structured implementation with emphasis on:
- Small, targeted tactical steps (avoid big simp sets)
- Structured `calc` proofs with one rewrite per step
- Explicit handling of differentiability conditions
- Use of sumIdx plumbing lemmas instead of case splits

**Timeline**: 410-650 lines, 17-35 hours (bottleneck: Phase 3)

---

## Part I: Why h_fiber Failed (Mathematical Foundation)

### The False Statement

The h_fiber lemma attempted to prove **pointwise** (for each k):

```
∂_r(Γ^k_θa · g_kb) - ∂_θ(Γ^k_ra · g_kb) = R^k_{arθ} · g_kb
```

### Verified Counterexample

**Setup**: Flat 2D space in polar coordinates
- Metric: g_rr = 1, g_θθ = r², g_rθ = 0
- Non-zero Christoffels: Γ^r_θθ = -r, Γ^θ_rθ = Γ^θ_θr = 1/r

**Test case**: k=θ, a=r, b=θ

**LHS Computation**:
```
∂_r(Γ^θ_θr · g_θθ) - ∂_θ(Γ^θ_rr · g_θθ)
= ∂_r((1/r) · r²) - ∂_θ(0 · r²)
= ∂_r(r) - 0
= 1
```

**RHS Computation**:
```
R^θ_{rrθ} · g_θθ = 0 · r² = 0    (Riemann tensor vanishes in flat space)
```

**Result**: LHS = 1 ≠ 0 = RHS  ∴ Identity is FALSE

### Root Cause

The product rule expansion gives:
```
∂(Γ·g) = (∂Γ)·g + Γ·(∂g)
```

But the h_fiber identity claims:
```
∂(Γ·g) = (∂Γ + ΓΓ_commutators)·g
```

These are NOT equal because:
```
Γ·(∂g) ≠ (ΓΓ_commutators)·g    (pointwise for each k)
```

Even using metric compatibility to expand ∂g, the algebra doesn't produce the ΓΓ commutator structure pointwise.

### Factor of 2 Symptom

In diagonal case (k=a), metric compatibility gives:
```
∂_μ g_kk = 2 · Σ_λ Γ^λ_μk · g_λk
```

This factor of 2 is a **real mathematical fact** (from g_kk appearing in both lower indices), not a tactical artifact. It was a symptom that the underlying identity was false.

---

## Part II: The Correct Mathematical Framework

### Christoffel Symbols of the First Kind

**Definition**:
```lean
noncomputable def Γ₁ (M r θ : ℝ) (β a μ : Idx) : ℝ :=
  sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ a μ)
```

**Key Properties** (to be proven in Phase 1):

1. **Γ₁_diag**: In Schwarzschild (diagonal metric), the sum collapses:
   ```lean
   Γ₁ M r θ β a μ = g M β β r θ * Γtot M r θ β a μ
   ```
   (No sum needed when metric is diagonal)

2. **Γ₁_symm**: Symmetric in last two indices:
   ```lean
   Γ₁ M r θ β a μ = Γ₁ M r θ β μ a
   ```

### The Textbook Identity (CORRECT)

**Standard form** (proven in every GR textbook):
```
R_{βarθ} = ∂_r Γ_{βaθ} - ∂_θ Γ_{βar} + Σ_λ (Γ_{λaθ}·Γ^λ_{βr} - Γ_{λar}·Γ^λ_{βθ})
```

**Why it works**: The ΓΓ terms involve **mixed forms** (covariant Γ₁ times contravariant Γ), not pure products. This algebraic structure allows the "miracle" cancellation with ∂g terms when summed over indices.

### The "Algebraic Miracle"

When we sum over β:
```
Σ_β [Γ_{βaθ} · ∂_r Γ^β - Γ_{βar} · ∂_θ Γ^β]
```

Using metric compatibility to expand ∂Γ^β in terms of ∂g and ΓΓ products, the resulting expression **exactly cancels** with the expansion of:
```
Σ_β [∂_r Γ_{βaθ} - ∂_θ Γ_{βar}]
```

This cancellation happens **only at the sum level**, not pointwise, which is why h_fiber failed.

---

## Part III: Implementation Plan (4 Phases)

### Phase 1: Γ₁ Infrastructure

**Location**: After Riemann.lean line 1270

**Estimated**: 50-80 lines, 1-2 hours

**Tasks**:

1. **Define Γ₁**:
   ```lean
   noncomputable def Γ₁ (M r θ : ℝ) (β a μ : Idx) : ℝ :=
     sumIdx (fun ρ => g M β ρ r θ * Γtot M r θ ρ a μ)
   ```

2. **Prove Γ₁_diag** (diagonal simplification):
   ```lean
   lemma Γ₁_diag (M r θ : ℝ) (h_ext : Exterior M r θ) (β a μ : Idx) :
     Γ₁ M r θ β a μ = g M β β r θ * Γtot M r θ β a μ := by
     unfold Γ₁
     -- Use sumIdx_commute_weight_left or sumIdx_commute_weight_right
     -- NOT by_cases (avoid case explosion)
     -- Pattern:
     rw [sumIdx_commute_weight_left (k := β)]
     simp only [g_offdiag h_ext, mul_zero, zero_mul, add_zero]
   ```

3. **Prove Γ₁_symm** (symmetry):
   ```lean
   lemma Γ₁_symm (M r θ : ℝ) (β a μ : Idx) :
     Γ₁ M r θ β a μ = Γ₁ M r θ β μ a := by
     unfold Γ₁
     congr 1; ext ρ
     rw [Γ_symm_lower]  -- Assuming this exists for Γtot
   ```

**Tactical Guidance**:
- Use `sumIdx_commute_weight_left` / `sumIdx_commute_weight_right` to isolate β term
- Keep simp sets small: `simp only [g_offdiag, mul_zero, add_zero]`
- Avoid `set` for numeric expressions intended for rewriting
- All @[simp] lemmas should be kept local unless proven universally useful

**Dependencies**:
- Requires `g_offdiag` (already exists in Schwarzschild.lean:1578)
- May need `sumIdx_commute_weight_*` lemmas (check mathlib or add to sumIdx infrastructure)

---

### Phase 2: Product Rule to Γ₁

**Location**: Around Riemann.lean line 5800 (before regroup lemmas)

**Estimated**: 80-120 lines, 2-4 hours

**Tasks**:

#### Phase 2A: Derivative Interchange Lemmas

These lemmas allow swapping ∂ and Σ (requires differentiability):

```lean
lemma dCoord_r_sumIdx
    (M r θ : ℝ) (h_ext : Exterior M r θ)
    (f : Idx → ℝ → ℝ → ℝ)
    (h_diff : ∀ k, DifferentiableAt ℝ (fun p => f k p.1 p.2) (r, θ)) :
  dCoord Idx.r (fun r θ => sumIdx (fun k => f k r θ)) r θ
  = sumIdx (fun k => dCoord Idx.r (fun r θ => f k r θ) r θ) := by
  -- Use derivative linearity and finiteness of Idx
  unfold dCoord sumIdx
  rw [deriv_sum]
  · simp only [Prod.mk.eta]
  · intro k _
    exact h_diff k

lemma dCoord_θ_sumIdx
    (M r θ : ℝ) (h_ext : Exterior M r θ)
    (f : Idx → ℝ → ℝ → ℝ)
    (h_diff : ∀ k, DifferentiableAt ℝ (fun p => f k p.1 p.2) (r, θ)) :
  dCoord Idx.θ (fun r θ => sumIdx (fun k => f k r θ)) r θ
  = sumIdx (fun k => dCoord Idx.θ (fun r θ => f k r θ) r θ) := by
  -- Similar to dCoord_r_sumIdx
  sorry  -- Implement analogously
```

**Differentiability Discharge Strategy**:
- Most Christoffel and metric terms are smooth in exterior region
- Use existing `DiffAt_*` lemmas for Γtot and g
- If needed, add axiom: `axiom exterior_smooth : ∀ M r θ, Exterior M r θ → [smoothness conditions]`
- Senior Professor approved explicit differentiability handling

#### Phase 2B: Main Product Rule Lemma

This replaces the false `regroup_right_sum_to_RiemannUp_NEW`:

```lean
lemma sum_k_prod_rule_to_Γ₁
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  sumIdx (fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
  =
  sumIdx (fun k =>
    dCoord Idx.r (fun r θ => Γ₁ M r θ k a Idx.θ) r θ
  - dCoord Idx.θ (fun r θ => Γ₁ M r θ k a Idx.r) r θ)
  := by
  calc
    sumIdx (fun k => dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
                   - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
    _ = sumIdx (fun k =>
          (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
           + Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ)
        - (dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ
           + Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ))
        := by
          congr 1; ext k
          rw [dCoord_prod, dCoord_prod]
          -- Need differentiability side goals here
          · sorry  -- DifferentiableAt for Γ
          · sorry  -- DifferentiableAt for g
          · sorry  -- DifferentiableAt for Γ
          · sorry  -- DifferentiableAt for g

    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
        - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ)
      + sumIdx (fun k =>
          Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
        - Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ)
        := by ring_nf

    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
        - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ)
      + 0
        := by
          congr 1
          -- This is where metric compatibility ∇g = 0 implies the second sum vanishes
          -- (after expanding via Γ₁ and using the miracle cancellation)
          sorry  -- To be proven via metric compatibility

    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γ₁ M r θ k a Idx.θ) r θ
        - dCoord Idx.θ (fun r θ => Γ₁ M r θ k a Idx.r) r θ)
        := by
          congr 1; ext k
          unfold Γ₁
          rw [dCoord_r_sumIdx, dCoord_θ_sumIdx]
          sorry  -- Final step: show Σ_ρ (∂Γ^ρ)·g = ∂(Σ_ρ Γ^ρ·g)
          -- Need differentiability side goals
          · sorry
          · sorry
```

**Tactical Guidance**:
- Each `calc` step should have exactly one rewrite or ring simplification
- Use `congr 1; ext k` to move inside sumIdx
- Keep each sorry focused on a single mathematical fact
- Discharge differentiability explicitly (don't leave as metavariables)

**Critical Step**: The second sum vanishing requires proving that when metric compatibility is applied, the ∂g terms exactly cancel with part of the ΓΓ structure. This is a **non-trivial verification** (estimated 40-60 lines).

---

### Phase 3: Core Identity (Riemann_via_Γ₁)

**Location**: Around Riemann.lean line 1350 (with other Riemann lemmas)

**Estimated**: 250-400 lines, 8-16 hours (**BOTTLENECK**)

**Structure**: 10-step structured `calc` proof

```lean
lemma Riemann_via_Γ₁
    (M r θ : ℝ) (h_ext : Exterior M r θ) (β a : Idx) :
  sumIdx (fun k => Riemann M r θ k a Idx.r Idx.θ * g M k β r θ)
  = dCoord Idx.r (fun r θ => Γ₁ M r θ β a Idx.θ) r θ
  - dCoord Idx.θ (fun r θ => Γ₁ M r θ β a Idx.r) r θ
  + sumIdx (fun λ =>
      Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ β Idx.r
    - Γ₁ M r θ λ a Idx.r * Γtot M r θ λ β Idx.θ)
  := by
  calc
    -- Step 1: Expand Riemann definition (∂Γ - ∂Γ + ΓΓ - ΓΓ)
    sumIdx (fun k => Riemann M r θ k a Idx.r Idx.θ * g M k β r θ)
    _ = sumIdx (fun k =>
          (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
         - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
         + sumIdx (fun lam =>
             Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a
           - Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a))
          * g M k β r θ)
        := by unfold Riemann; rfl

    -- Step 2: Distribute g_kβ over the sum
    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k β r θ
        - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k β r θ)
      + sumIdx (fun k =>
          sumIdx (fun lam =>
            Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a
          - Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a)
          * g M k β r θ)
        := by ring_nf

    -- Step 3: Handle ∂Γ terms - use product rule BACKWARDS to get ∂(Γ·g) - Γ·∂g
    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k β r θ) r θ
        - Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k β r θ) r θ
        - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k β r θ) r θ
        + Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k β r θ) r θ)
      + sumIdx (fun k => sumIdx (fun lam => [...]))
        := by
          congr 1
          ext k
          rw [← dCoord_prod, ← dCoord_prod]
          ring_nf
          -- Differentiability side goals
          · sorry
          · sorry

    -- Step 4: Apply metric compatibility to expand ∂g terms
    --   ∂_μ g_kβ = Σ_ρ (Γ^ρ_μk·g_ρβ + Γ^ρ_μβ·g_kρ)
    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k β r θ) r θ
        - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k β r θ) r θ)
      - sumIdx (fun k =>
          Γtot M r θ k Idx.θ a * sumIdx (fun ρ =>
            Γtot M r θ ρ Idx.r k * g M ρ β r θ
          + Γtot M r θ ρ Idx.r β * g M k ρ r θ))
      + sumIdx (fun k =>
          Γtot M r θ k Idx.r a * sumIdx (fun ρ =>
            Γtot M r θ ρ Idx.θ k * g M ρ β r θ
          + Γtot M r θ ρ Idx.θ β * g M k ρ r θ))
      + sumIdx (fun k => sumIdx (fun lam => [...]))
        := by
          congr 1
          ext k
          rw [dCoord_g_via_compat_ext, dCoord_g_via_compat_ext]
          sorry  -- Expand the negative form to positive

    -- Step 5: Distribute and flatten nested sums (use ring_nf carefully)
    _ = [4 separate double sums from expanding the products]
        := by ring_nf

    -- Step 6: Apply Fubini to swap sum order (Σ_k Σ_ρ = Σ_ρ Σ_k)
    _ = [Same 4 sums with order swapped]
        := by
          simp only [sumIdx_swap_comm]

    -- Step 7: Relabel dummy indices (k ↔ ρ in appropriate terms)
    _ = [Relabeled to match target pattern]
        := by
          congr 1
          -- Use sumIdx_relabel lemma to swap k and ρ names
          sorry

    -- Step 8: Combine terms - the "algebraic miracle" happens here
    --   12 ΓΓg terms should reduce to 4 terms matching the ΓΓ structure
    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k β r θ) r θ
        - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k β r θ) r θ)
      + sumIdx (fun λ =>
          sumIdx (fun k =>
            Γtot M r θ k Idx.r λ * Γtot M r θ λ Idx.θ a * g M k β r θ
          - Γtot M r θ k Idx.θ λ * Γtot M r θ λ Idx.r a * g M k β r θ))
        := by
          -- This step requires careful algebraic verification
          -- May need 50-80 lines of intermediate lemmas
          sorry  -- CRITICAL BOTTLENECK

    -- Step 9: Recognize Γ₁ in the ∂(Γ·g) terms
    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γ₁ M r θ k a Idx.θ) r θ
        - dCoord Idx.θ (fun r θ => Γ₁ M r θ k a Idx.r) r θ)
      + sumIdx (fun λ =>
          sumIdx (fun k =>
            Γtot M r θ k Idx.r λ * Γtot M r θ λ Idx.θ a * g M k β r θ
          - Γtot M r θ k Idx.θ λ * Γtot M r θ λ Idx.r a * g M k β r θ))
        := by
          congr 1
          ext k
          unfold Γ₁
          rw [← dCoord_r_sumIdx, ← dCoord_θ_sumIdx]
          sorry  -- Show ∂(Σ Γ·g) = Σ ∂Γ·g when metric compatibility holds
          -- Differentiability side goals
          · sorry
          · sorry

    -- Step 10: Swap sum order in ΓΓ terms and recognize Γ₁
    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γ₁ M r θ k a Idx.θ) r θ
        - dCoord Idx.θ (fun r θ => Γ₁ M r θ k a Idx.r) r θ)
      + sumIdx (fun λ =>
          Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ β Idx.r
        - Γ₁ M r θ λ a Idx.r * Γtot M r θ λ β Idx.θ)
        := by
          congr 2
          ext λ
          unfold Γ₁
          -- Collapse inner sum over k using diagonal metric
          rw [sumIdx_swap_comm]
          sorry  -- Final algebraic simplification
```

**Critical Subsections**:

1. **Step 4 expansion** (40-60 lines): Convert metric compatibility from negative to positive form
2. **Step 8 cancellation** (50-80 lines): The "algebraic miracle" - verify 12 terms → 4 terms
3. **Step 9 recognition** (30-50 lines): Show ∂(Σ Γ·g) form equals Σ ∂Γ·g via interchange
4. **Differentiability discharge** (scattered): ~20-30 side goals total

**Tactical Patterns**:
- Each calc step: ONE rewrite or ring_nf
- Use `congr 1; ext k` to work inside sums
- Keep simp sets minimal: `simp only [specific_lemma, mul_comm, add_assoc]`
- If a step needs >5 lines, extract as separate `have` lemma
- Use `rw [show A = B from by tactics]` for inline micro-proofs

**Risk**: Step 8 cancellation is highly non-trivial. May require breaking into 5-10 intermediate lemmas.

---

### Phase 4: Final Assembly

**Location**: Riemann.lean line 5938 (replacing regroup_right_sum_to_RiemannUp_NEW)

**Estimated**: 30-50 lines, 1-2 hours

```lean
-- DELETE the old false lemma:
-- lemma regroup_right_sum_to_RiemannUp_NEW ... (lines 5938-6445)

-- REPLACE with correct version:
lemma regroup_right_sum_to_Riemann_CORRECT
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  sumIdx (fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
  = sumIdx (fun k =>
      Riemann M r θ k a Idx.r Idx.θ * g M k b r θ)
  := by
  calc
    sumIdx (fun k =>
      dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
    - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
    _ = sumIdx (fun k =>
          dCoord Idx.r (fun r θ => Γ₁ M r θ k a Idx.θ) r θ
        - dCoord Idx.θ (fun r θ => Γ₁ M r θ k a Idx.r) r θ)
        := sum_k_prod_rule_to_Γ₁ M r θ h_ext a b

    _ = dCoord Idx.r (fun r θ => Γ₁ M r θ b a Idx.θ) r θ
      - dCoord Idx.θ (fun r θ => Γ₁ M r θ b a Idx.r) r θ
      + sumIdx (fun λ =>
          Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ b Idx.r
        - Γ₁ M r θ λ a Idx.r * Γtot M r θ λ b Idx.θ)
      - sumIdx (fun λ =>
          Γ₁ M r θ λ a Idx.θ * Γtot M r θ λ b Idx.r
        - Γ₁ M r θ λ a Idx.r * Γtot M r θ λ b Idx.θ)
        := by
          rw [← Riemann_via_Γ₁]
          ring

    _ = sumIdx (fun k => Riemann M r θ k a Idx.r Idx.θ * g M k b r θ)
        := by simp only [add_sub_cancel]
```

**Tactical Notes**:
- Clean and simple once Phase 3 is done
- Mostly rearranging and canceling
- Final simp should be trivial

---

## Part IV: Deletion Plan

### Files to Modify

**Riemann.lean**:

1. **DELETE** lines 6257-6427:
   - Entire `have h_fiber : ∀ k, ...` proof
   - All of JP's PATCH A-D applied to h_fiber
   - All helper `have` statements within h_fiber block

2. **DELETE** lines 128-150:
   - fold_diag_kernel₂ and helper lemmas (mul_add_same, mul_add_same₃)
   - These were created to support false h_fiber proof

3. **DELETE** lines 235-238:
   - Deleted Γ_switch_k_a lemma (already marked as false)

4. **KEEP** lines 5955-5980:
   - Product rule application via pack_right_slot_prod
   - This is mathematically correct, will be reused in Phase 2

5. **KEEP** all metric compatibility infrastructure:
   - dCoord_g_via_compat_ext and related lemmas
   - These are correct and will be used in Phase 3

**Schwarzschild.lean**:
- **NO CHANGES** - all infrastructure lemmas remain valid

### What to Preserve

- Product rule lemmas (pack_right_slot_prod)
- Metric compatibility lemmas (dCoord_g_via_compat_ext)
- Sum manipulation infrastructure (sumIdx lemmas)
- Diagonal metric lemmas (g_offdiag, etc.)

---

## Part V: Testing and Verification

### Build Checkpoints

After each phase, verify:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Expected outcomes**:
- Phase 1: Should compile with 0 errors (self-contained)
- Phase 2: May have sorries for differentiability, but structure should compile
- Phase 3: Will have sorries in Step 8, but calc structure should type-check
- Phase 4: Should compile completely once Phase 3 sorries are filled

### Flat Space Testing Warning

**CRITICAL** (from Junior Professor):
> "Flat space" testing with Schwarzschild-specific Γtot is problematic. The Christoffel symbols Γtot M r θ ... are defined for the Schwarzschild metric, not flat space.

**Implication**: Cannot use flat 2D polar coordinates to test intermediate lemmas. Testing must be:
1. **Schwarzschild-specific**: Use actual Schwarzschild values in exterior region
2. **Symbolic verification**: Rely on Lean's type checker, not numerical examples
3. **Final theorem**: Test against known GR results (e.g., Ricci tensor in Schwarzschild)

### Integration Testing

Once all phases complete:
1. Verify `Riemann_rθrθ_ext` still compiles (should use new regroup lemma)
2. Check downstream Ricci tensor proofs still work
3. Run full build: `lake build`

---

## Part VI: Timeline and Effort Estimates

### Optimistic Scenario (17 hours, 410 lines)

- **Phase 1**: 1 hour, 50 lines (if sumIdx lemmas exist)
- **Phase 2**: 2 hours, 80 lines (if differentiability is smooth)
- **Phase 3**: 12 hours, 250 lines (if Step 8 cancellation works cleanly)
- **Phase 4**: 1 hour, 30 lines
- **Testing/Debug**: 1 hour

### Realistic Scenario (26 hours, 530 lines)

- **Phase 1**: 1.5 hours, 65 lines (need to add sumIdx plumbing)
- **Phase 2**: 3 hours, 100 lines (differentiability requires helper lemmas)
- **Phase 3**: 16 hours, 325 lines (Step 8 needs intermediate lemmas)
- **Phase 4**: 1.5 hours, 40 lines
- **Testing/Debug**: 4 hours (iterations on Phase 3)

### Pessimistic Scenario (35 hours, 650 lines)

- **Phase 1**: 2 hours, 80 lines (sumIdx lemmas complex)
- **Phase 2**: 4 hours, 120 lines (differentiability requires axioms)
- **Phase 3**: 24 hours, 400 lines (Step 8 highly non-trivial, may need rethinking)
- **Phase 4**: 2 hours, 50 lines
- **Testing/Debug**: 3 hours

**Bottleneck**: Phase 3, Step 8 (the "algebraic miracle")

---

## Part VII: Success Criteria

### Mathematical Correctness

1. ✅ No false pointwise identities proven
2. ✅ All identities proven at appropriate level (sum vs pointwise)
3. ✅ Metric compatibility and product rule applied correctly
4. ✅ Christoffel symbols of first kind properly defined and used

### Technical Completeness

1. ✅ `regroup_right_sum_to_Riemann_CORRECT` compiles without sorry
2. ✅ All downstream proofs (Riemann_rθrθ_ext, Ricci, etc.) still compile
3. ✅ No tactical timeouts or resource exhaustion
4. ✅ Differentiability conditions properly discharged (via lemmas or axioms)

### Code Quality

1. ✅ Structured `calc` proofs with one step per line
2. ✅ Minimal simp sets (avoid big hammer tactics)
3. ✅ Clear comments explaining each mathematical step
4. ✅ Reusable infrastructure lemmas properly documented

### Validation

1. ✅ Senior Professor's counterexample concern fully addressed
2. ✅ Junior Professor's tactical guidance followed
3. ✅ Both professors' approval obtained before merging

---

## Part VIII: Risk Mitigation

### High Risk: Phase 3 Step 8 Cancellation

**Risk**: The "algebraic miracle" of 12 ΓΓg terms canceling to 4 terms may be extremely difficult to formalize.

**Mitigation**:
1. **Hand calculation first**: Work out cancellation on paper with explicit indices
2. **Intermediate lemmas**: Break into 5-10 small lemmas, each handling 2-3 terms
3. **Use CAS**: Verify cancellation in Mathematica/SageMath symbolically
4. **Consult professors**: If stuck >8 hours, send detailed memo with specific blocker

### Medium Risk: Differentiability Conditions

**Risk**: May need differentiability at every derivative interchange, creating many side goals.

**Mitigation**:
1. **Axiom approach**: Add `axiom Schwarzschild_smooth` for global smoothness in exterior
2. **Lemma library**: Build library of DifferentiableAt lemmas for Γtot, g, etc.
3. **Tactic**: Write custom tactic to discharge standard differentiability goals

### Low Risk: sumIdx Infrastructure

**Risk**: May not have all sumIdx manipulation lemmas needed (swap, relabel, etc.)

**Mitigation**:
1. **Check mathlib**: Most should exist (Finset.sum lemmas)
2. **Add wrappers**: Write thin wrappers adapting mathlib lemmas to sumIdx
3. **Prove once**: If needed, prove general versions and mark @[simp]

---

## Part IX: Next Immediate Steps

### Before Implementation

1. ✅ **Senior Professor approval**: Obtain confirmation of strategy (DONE per summary)
2. ✅ **Junior Professor review**: Get tactical guidance (DONE per summary)
3. **Hand calculation**: Work out Phase 3 Step 8 cancellation on paper
4. **Differentiability strategy**: Decide axiom vs lemma approach

### During Implementation

1. **Phase 1 first**: Implement and test Γ₁ infrastructure completely
2. **Checkpoint builds**: Build after each phase
3. **Document blockers**: If stuck >2 hours on any step, document and ask
4. **Incremental commits**: Commit after each phase (use feature branch)

### After Implementation

1. **Full test suite**: Run all GR proofs
2. **Performance check**: Ensure no timeout regressions
3. **Documentation**: Add comments explaining the mathematical approach
4. **Final review**: Request both professors' signoff before merging to main

---

## Appendix A: Tactical Best Practices (from Professors)

### From Senior Professor

1. **Structured calc proofs**: Each step should be a single transformation
2. **Avoid big simp**: Use `simp only [specific_lemmas]` for predictability
3. **Explicit differentiability**: Discharge as separate lemmas or axioms, don't leave as goals
4. **Product rule backwards**: Use `← dCoord_prod` to combine ∂(f·g) from ∂f and ∂g

### From Junior Professor

1. **sumIdx plumbing**: Use `sumIdx_commute_weight_left/right` instead of by_cases
2. **No `set` for rewrites**: Use `let` or keep expressions inline if needed in rewrites
3. **Local @[simp]**: Don't pollute global simp set with proof-specific helpers
4. **ring_nf timing**: Only after shapes match, not for exploration
5. **Flat space warning**: Don't test Schwarzschild-specific code with flat space values

---

## Appendix B: Key Mathematical Facts

### Metric Compatibility (∇g = 0)

```
∂_μ g_{αβ} = -Σ_λ (Γ^λ_{μα} · g_{λβ} + Γ^λ_{μβ} · g_{αλ})
```

In positive form (equivalent via metric symmetry):
```
∂_μ g_{αβ} = Σ_λ (Γ^λ_{μα} · g_{λβ} + Γ^λ_{μβ · g_{αλ}})
```
(The sign difference requires algebraic manipulation using covariant derivative definition)

### Schwarzschild Diagonal Property

```
g_{αβ} = 0  when α ≠ β
```

**Implication**:
```
Σ_ρ g_{βρ} · f(ρ) = g_{ββ} · f(β)
```
(Sum collapses to single term)

### Riemann Tensor (Mixed Form)

```
R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Σ_λ (Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ})
```

### Riemann Tensor (Fully Covariant, via Γ₁)

```
R_{βσμν} = ∂_μ Γ_{βσν} - ∂_ν Γ_{βσμ} + Σ_λ (Γ_{λσν} Γ^λ_{βμ} - Γ_{λσμ} Γ^λ_{βν})
```

**Note**: ΓΓ terms mix covariant and contravariant forms!

---

## Document Status

**Version**: 1.0
**Date**: October 16, 2025
**Authors**: Research Team with Senior and Junior Professor guidance
**Status**: Ready for implementation pending final approval

**Changes from UNIFIED_STRATEGY_OCT16_FINAL.md**:
1. Incorporated Senior Professor's concrete code for Phases 1 & 2
2. Integrated Junior Professor's tactical refinements (sumIdx plumbing, avoid `set`)
3. Added explicit flat space testing warning
4. Refined Phase 3 structure with emphasis on small calc steps
5. Updated risk assessment based on professors' feedback
6. Added Appendix A with consolidated tactical best practices

**Next Action**: Await user approval to begin Phase 1 implementation.

---

**Research Team**
October 16, 2025
