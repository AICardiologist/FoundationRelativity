# JP's Four-Block Implementation Plan for Pattern B (October 27, 2025)

**Status**: ✅ Infrastructure complete, ready for implementation
**Prepared by**: Claude Code based on JP's detailed guidance
**For**: Paul + Future implementers

---

## Executive Summary

JP has provided a precise, mechanical solution to the Pattern B cross-term issue. The key insight: **don't prove the branches separately**—combine them BEFORE applying the Ricci identity, so the cross terms cancel structurally.

**Infrastructure Status**:
- ✅ **Lemma L1** (`sumIdx_antisymm_kernel_zero`) - Implemented at line 2040
- ✅ **Lemma L2** (`cross_block_kernel` + `cross_block_antisymm`) - Implemented at lines 2085-2099
- ✅ **Both lemmas compile** without errors
- ✅ **All existing Pattern A/C/D infrastructure** remains intact

**What's needed**: Refactor the two Pattern B calc chains (lines 7808-7843 and 7970-8000) to use the combined Four-Block approach.

---

## The Mathematical Fix

### What Was Wrong

**Isolated b-branch** attempts to prove:
```
Σ_ρ B_b(ρ) - Σ_ρ[Γ^ρ_μa·∇_ν g_ρb] + Σ_ρ[Γ^ρ_νa·∇_μ g_ρb] = Σ_ρ[-R^ρ_aμν · g_ρb]
```

After expansion, this has a non-zero cross term:
```
T_{a,Cross} = Σ_{ρ,e} [(Γ^ρ_μa Γ^e_νb - Γ^ρ_νa Γ^e_μb) · g_ρe]
```

SP proved `T_{a,Cross} = -1` in flat polar coordinates. **The identity is false.**

### What Is Correct

**Combined both branches**:
```
[Σ_ρ B_b(ρ) - Σ_ρ[Γ^ρ_μa·∇_ν g_ρb] + Σ_ρ[Γ^ρ_νa·∇_μ g_ρb]]
+ [Σ_ρ B_a(ρ) - Σ_ρ[Γ^ρ_μb·∇_ν g_aρ] + Σ_ρ[Γ^ρ_νb·∇_μ g_aρ]]
= Σ_ρ[-R^ρ_aμν · g_ρb] + Σ_ρ[-R^ρ_bμν · g_aρ]
```

The cross terms cancel:
```
T_{a,Cross} + T_{b,Cross} = 0
```

This is proven structurally by JP's Lemmas L1 + L2.

---

## The Four-Block Strategy (JP's Plan)

### Step 1: Expand Each Branch Deterministically

**Use existing stable tactics** (Patterns A/C/D):
- Expand definitions with bounded `simp only`
- Use diagonality lemmas (`sumIdx_reduce_by_diagonality_right`)
- Collect ∂Γ terms and main ΓΓ terms
- **DO NOT try to close the branch**—just expand it

### Step 2: Add the Branches Before Simplifying

```lean
have combined_lhs :
  [expanded b-branch LHS] + [expanded a-branch LHS]
  = [target combined form] := by
  -- literally add the two expanded expressions
  exact ...
```

### Step 3: Kill Cross Terms in One Line

```lean
have h_cross :
  sumIdx (fun ρ => sumIdx (fun e =>
    cross_block_kernel M r θ μ ν a b ρ e * g M ρ e r θ)) = 0 := by
  exact sumIdx_antisymm_kernel_zero M r θ _ (cross_block_antisymm M r θ μ ν a b)
```

This is the **new ingredient**. It's deterministic, requires no search, and completes instantly.

### Step 4: Finish to RiemannUp

Use existing Pattern C infrastructure:
- Diagonality to factor out `g_bb` and `g_aa`
- Combine sums with `sumIdx_add_distrib`
- Match to RiemannUp definition

---

## Detailed Implementation Guide

### Location: Lines 7808-8000 (Current Pattern B Sites)

**Current structure** (WRONG):
```lean
/-

 b-branch calc chain (lines 7808-7843) - attempts isolated proof
  calc
    sumIdx B_b - ... + ... = ... := by sorry

-- then separately:
-- a-branch calc chain (lines 7970-8000) - attempts isolated proof
  calc
    sumIdx B_a - ... + ... = ... := by sorry
```

**New structure** (CORRECT):
```lean
/- Combined Four-Block calc chain -/
calc
  -- Step 1: Define combined LHS
  (sumIdx B_b - sumIdx(Γ^ρ_μa·∇_ν g_ρb) + sumIdx(Γ^ρ_νa·∇_μ g_ρb))
  + (sumIdx B_a - sumIdx(Γ^ρ_μb·∇_ν g_aρ) + sumIdx(Γ^ρ_νb·∇_μ g_aρ))

  -- Step 2: Expand both branches (use existing stable tactics)
  = [expanded form with ∂Γ terms + main ΓΓ + cross ΓΓ] := by
    simp only [nabla_g, sub_eq_add_neg]
    -- expand covariant derivatives for both branches
    -- collect terms

  -- Step 3: Show payload cancellation (already works from Pattern C)
  = [after payload cancel: ∂Γ + main ΓΓ + cross ΓΓ] := by
    -- your existing payload_cancel infrastructure

  -- Step 4: Show cross terms vanish ← NEW STEP
  = [after cross cancel: ∂Γ + main ΓΓ] := by
    have h_cross :
      sumIdx (fun ρ => sumIdx (fun e =>
        cross_block_kernel M r θ μ ν a b ρ e * g M ρ e r θ)) = 0 := by
      exact sumIdx_antisymm_kernel_zero M r θ _
              (cross_block_antisymm M r θ μ ν a b)
    -- use h_cross to eliminate the cross block
    simp [h_cross]

  -- Step 5: Match to RiemannUp (use existing diagonality + factoring)
  = Σ_ρ[-R^ρ_aμν·g_ρb] + Σ_ρ[-R^ρ_bμν·g_aρ] := by
    -- your existing first_block two-step pattern:
    -- 1) collapse inner sum with diagonality
    -- 2) factor and pack
```

---

## Concrete Code Skeleton

### Phase 1: Set Up Combined Expression

```lean
-- Around line 7806, replace the current two separate calc chains with:

/- Combined Four-Block proof: both branches together -/
have ricci_combined :
  -- LHS: sum of both branch contributions
  (sumIdx B_b
    - sumIdx (fun ρ => Γtot M r θ ρ μ a * nabla_g M r θ ν ρ b)
    + sumIdx (fun ρ => Γtot M r θ ρ ν a * nabla_g M r θ μ ρ b))
  +
  (sumIdx B_a
    - sumIdx (fun ρ => Γtot M r θ ρ μ b * nabla_g M r θ ν a ρ)
    + sumIdx (fun ρ => Γtot M r θ ρ ν b * nabla_g M r θ μ a ρ))
  -- RHS: sum of both Riemann contributions
  = (- sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) + rho_core_b)
    + (- sumIdx (fun ρ => RiemannUp M r θ ρ b μ ν * g M a ρ r θ) + rho_core_a)
  := by
    -- Proof goes here (see Phase 2)
    sorry
```

### Phase 2: Expand and Collect

```lean
:= by
  -- Expand nabla_g on both branches
  simp only [nabla_g]

  -- The goal now has form:
  -- Σ B_b - Σ[Γ·(∂g - Σ Γg - Σ Γg)] + Σ[Γ·(∂g - Σ Γg - Σ Γg)]
  -- + (symmetric for a-branch)

  -- Expand the products
  simp only [mul_sub, sumIdx_map_sub]

  -- Now we have:
  -- Σ B_b - Σ[Γ·∂g] + Σ[Γ·Σ Γg] + Σ[Γ·Σ Γg]  [b-branch]
  -- + Σ B_a - Σ[Γ·∂g] + Σ[Γ·Σ Γg] + Σ[Γ·Σ Γg]  [a-branch]

  -- Collect into term types:
  -- [∂Γ terms from B_b and B_a]
  -- + [payload terms: Γ·∂g - these cancel with parts of B]
  -- + [main ΓΓ terms]
  -- + [cross ΓΓ terms]  ← these will vanish via h_cross
```

### Phase 3: Payload Cancellation

```lean
  -- Show that Γ·∂g terms from expansion cancel with corresponding parts of B
  -- This is what you already had working; keep your existing approach

  have payload_b : ∀ ρ,
    [terms from B_b involving ∂g] + [terms from expansion involving Γ·∂g] = 0 := by
    intro ρ; ring

  have payload_a : ∀ ρ,
    [similar for a-branch] = 0 := by
    intro ρ; ring

  simp [payload_b, payload_a, sumIdx_congr]

  -- After this, goal has only:
  -- [∂Γ terms] + [main ΓΓ] + [cross ΓΓ]
```

### Phase 4: Cross Term Cancellation (THE NEW STEP)

```lean
  -- Define the antisymmetric kernel
  have h_cross :
    sumIdx (fun ρ => sumIdx (fun e =>
      cross_block_kernel M r θ μ ν a b ρ e * g M ρ e r θ)) = 0 := by
    exact sumIdx_antisymm_kernel_zero M r θ _
            (cross_block_antisymm M r θ μ ν a b)

  -- The cross block in the goal matches this structure exactly
  -- (may need to unfold cross_block_kernel to make it syntactically match)
  unfold cross_block_kernel at h_cross

  -- Now substitute h_cross to eliminate the cross terms
  simp only [h_cross, add_zero]

  -- After this, goal has only:
  -- [∂Γ terms] + [main ΓΓ]
```

### Phase 5: Match to RiemannUp

```lean
  -- Now we have:
  -- Σ_ρ[-(∂_μ Γ^ρ_νa - ∂_ν Γ^ρ_μa + Σ_e Γ^ρ_μe Γ^e_νa - Σ_e Γ^ρ_νe Γ^e_μa)·g_ρb]
  -- + (symmetric for a/b swap)

  -- This matches the RiemannUp definition
  simp only [RiemannUp]

  -- Use diagonality and your existing first_block pattern to finish
  -- (This is what you already had working in Pattern C)
```

---

## What This Eliminates

### No Longer Needed

1. **The entire scalar_finish dance** — we don't use it at all
2. **sumIdx_add3 packing** — not needed because we're not trying to pack branch-wise
3. **Global AC simp** — no heavy normalization required
4. **Timeouts** — gone, because we're not searching for non-existent proofs

### Still Used (From Patterns A/C/D)

1. **Diagonality lemmas** (`sumIdx_reduce_by_diagonality_right`) ✅
2. **Bounded simp** (`simp only [nabla_g, ...]`) ✅
3. **Pointwise reasoning** (`apply sumIdx_congr; intro ρ`) ✅
4. **Ring normalizer** (for payload cancellation) ✅

---

## Implementation Checklist

### Prerequisites (All Done ✅)
- [x] Lemma L1: `sumIdx_antisymm_kernel_zero` (line 2040)
- [x] Lemma L2: `cross_block_kernel` definition (line 2085)
- [x] Lemma L2: `cross_block_antisymm` (line 2094)
- [x] Both lemmas compile without errors
- [x] Existing Pattern A/C/D infrastructure intact

### Implementation Tasks
- [ ] Remove current Pattern B sorries (lines 7817-7843, 7980-8000)
- [ ] Create combined calc chain structure
- [ ] Phase 1: Set up combined LHS and RHS
- [ ] Phase 2: Expand both branches with stable tactics
- [ ] Phase 3: Show payload cancellation (reuse existing)
- [ ] Phase 4: Apply h_cross to eliminate cross terms
- [ ] Phase 5: Match to RiemannUp (reuse existing Pattern C)
- [ ] Build and verify no errors
- [ ] Verify error count drops from 24

### Validation
- [ ] Build succeeds
- [ ] No timeouts
- [ ] No type mismatches
- [ ] Error count improves
- [ ] All proofs deterministic and bounded

---

## Estimated Effort

**If implementing now**: 2-4 hours
- 1 hour: Careful refactoring of calc chain structure
- 1 hour: Debugging any tactical mismatches
- 1 hour: Testing and validation
- 1 hour: Documentation

**Complexity**: Moderate
- The logic is clear (JP's plan is explicit)
- Infrastructure all exists
- Main work is careful calc chain construction
- No heavy automation needed

**Risk**: Low
- All components already proven to work
- No new mathematical content
- Can revert to sorry if issues arise

---

## Alternative: Document and Defer

**If not implementing now**:
1. Keep the current sorry markers (already have detailed comments)
2. This document serves as complete implementation plan
3. Any future implementer has everything they need
4. Focus effort on the other 24 errors instead

**Trade-offs**:
- **Defer**: Make progress on other errors, come back to Pattern B later with fresh eyes
- **Implement now**: Complete the Pattern B fix while context is fresh

---

## Success Criteria

When implementation is complete:
- ✅ Both Pattern B sites use combined Four-Block approach
- ✅ Cross terms eliminated via h_cross in one line
- ✅ No timeouts or type mismatches
- ✅ Error count drops (expected: 24 → ~18-20)
- ✅ All proofs deterministic and fast (<1 second each)
- ✅ Code is clean and maintainable

---

## Questions for Paul

1. **Priority**: Implement Pattern B now vs defer and fix other errors first?
2. **Timeline**: Is there urgency to get Pattern B working, or can it wait?
3. **Resources**: Should I proceed with implementation, or hand off to human expert?

---

## Acknowledgments

**Thank you JP!** Your precise mechanical plan with the two structural lemmas turns what seemed like an intractable tactical nightmare into a straightforward, clean proof. The antisymmetry cancellation is elegant mathematics made Lean-friendly.

**Thank you SP!** Your counterexample saved us from weeks of futile debugging and pointed us to the correct mathematical structure.

---

**Prepared by**: Claude Code (Sonnet 4.5)
**Date**: October 27, 2025
**Status**: ✅ Infrastructure complete, implementation plan ready
**Confidence**: Very high — JP's plan is explicit and all components tested

---

**END OF IMPLEMENTATION PLAN**
