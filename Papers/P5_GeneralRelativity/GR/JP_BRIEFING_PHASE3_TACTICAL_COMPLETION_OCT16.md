# Junior Professor Briefing: Phase 3 Tactical Completion
## Date: October 16, 2025
## Task: Complete 6 tactical proofs in Riemann_via_Γ₁
## Estimated Time: 3-4 hours

---

## Quick Start

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Lines to Fix**:
- Line 1430: `Riemann_via_Γ₁_Cancel_r` (sorry)
- Line 1444: `Riemann_via_Γ₁_Cancel_θ` (sorry)
- Line 1462: `Riemann_via_Γ₁_Identify_r` (sorry)
- Line 1476: `Riemann_via_Γ₁_Identify_θ` (sorry)
- Line 1549: Steps 4-7 in main proof (sorry)
- Line 1577: Step 8 assembly in main proof (sorry)

**Build Command**:
```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Current Status**: ✅ Builds successfully (0 errors, 6 documented sorries)

---

## Context: What You Need to Know

### The Big Picture

We're formalizing the Riemann tensor identity that appears in every GR textbook:

```
R_{βarθ} = ∂_r Γ₁_{βaθ} - ∂_θ Γ₁_{βar} - T2
```

where:
- `R_{βarθ}` = Riemann tensor (fully covariant)
- `Γ₁_{βaθ}` = First-kind Christoffel symbols = Σ_ρ g_{βρ} Γ^ρ_{aθ}
- `T2` = ΓΓ commutator terms = Σ_λ (Γ_{λaθ} Γ^λ_{βr} - Γ_{λar} Γ^λ_{βθ})

### Recent History (Oct 16, 2025)

**Senior Professor (SP) Discovery**: Original Phase 3 proof had wrong starting point and sign error.

**SP's Corrected Approach**:
1. Start from R_{βarθ} directly (not Σ_k version)
2. Expand via RiemannUp definition
3. Distribute and rearrange (Steps 1-7)
4. Apply "algebraic miracle": M - D = -T2 using 4 auxiliary lemmas

**AI's Implementation**: Created complete structural form, but tactical proof execution blocked by Lean 4 pattern matching issues.

### The 4 Auxiliary Lemmas ("The Algebraic Miracle")

These prove M - D = -T2:

1. **Cancel_r**: M_r = D_r2 (pure index gymnastics via Fubini)
2. **Cancel_θ**: M_θ = D_θ2 (same as Cancel_r with θ↔r)
3. **Identify_r**: D_r1 = T2_r (uses symmetries g_symm, Γtot_symm)
4. **Identify_θ**: D_θ1 = T2_θ (same as Identify_r with θ↔r)

All have correct type signatures. Only tactical proofs need completion.

---

## The Core Technical Challenge

### Pattern Matching in Lean 4

Lean's rewrite tactics require **exact syntactic patterns**, not semantic equality.

**Example Problem**:

After applying `conv_rhs => arg 1; ext ρ; rw [mul_comm, mul_sumIdx]`, the goal is:
```lean
sumIdx fun ρ => sumIdx fun k => Γtot M r θ ρ Idx.θ a * (Γtot M r θ k Idx.r ρ * g M β k r θ)
```

We want to apply `sumIdx_swap` which expects:
```lean
sumIdx (fun k => sumIdx (fun lam => F k lam))
```

But the outer `Γtot ... *` factor prevents direct pattern matching.

**AI's Attempts** (all failed):
- Global `simp_rw`: Transforms both sides, breaks equality
- `conv` with `ext`: Navigation and pattern matching issues
- Multiple combinations of `mul_comm`, `mul_sumIdx`, etc.

**What You Have That AI Doesn't**:
- Expertise with Lean 4 `conv` syntax
- Knowledge of advanced pattern matching tactics
- Experience with similar Mathlib proofs

---

## Detailed Task Breakdown

### Task 1: Cancel_r (Line 1430) ⭐ START HERE

**Priority**: High - prototype for Cancel_θ

**Lemma Signature**:
```lean
lemma Riemann_via_Γ₁_Cancel_r (M r θ : ℝ) (β a : Idx) :
  sumIdx (fun ρ => g M β ρ r θ * sumIdx (fun lam =>
      Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a))
  =
  sumIdx (fun ρ => sumIdx (fun σ => Γtot M r θ σ Idx.r ρ * g M β σ r θ)
    * Γtot M r θ ρ Idx.θ a)
```

**Operations Needed**:
1. LHS: Distribute `g_βρ` into inner sum using `mul_sumIdx`
2. RHS: Distribute `Γ^ρ_{θa}` into inner sum (multiplication on right)
3. Apply Fubini (`sumIdx_swap`) to RHS
4. Compare: both sides should be Σ_ρ Σ_λ (products), differ only in index order
5. Use `sumIdx_congr` + `ring` to finish

**Available Lemmas**:
- `mul_sumIdx` (Line 1314): `c * sumIdx f = sumIdx (fun k => c * f k)`
- `sumIdx_swap` (Line 1320): Fubini for `sumIdx`
- `sumIdx_congr` (Line 1348): Pointwise equality implies sum equality
- Standard `ring` tactic for commutativity/associativity

**Suggested Approach**:
```lean
by
  classical
  -- LHS: straightforward
  conv_lhs => arg 1; ext ρ; rw [mul_sumIdx]

  -- RHS: needs careful handling of right multiplication
  -- Option A: Create helper lemma for (sumIdx f) * c pattern
  -- Option B: Use conv to navigate + mul_comm + mul_sumIdx
  -- Option C: Manual expansion to Finset.sum

  -- After both sides distributed, apply Fubini to RHS
  conv_rhs => rw [sumIdx_swap]  -- May need adjustment

  -- Final comparison
  apply sumIdx_congr; intro i
  apply sumIdx_congr; intro j
  ring
```

**Estimated Time**: 30-45 minutes

**Success Criterion**: Build passes, no sorry

---

### Task 2: Cancel_θ (Line 1444)

**Priority**: Medium - should be quick after Cancel_r

**Operations**: Identical to Cancel_r with all θ and r swapped

**Suggested Approach**: Copy Cancel_r proof, swap indices

**Estimated Time**: 10 minutes

---

### Task 3: Identify_r (Line 1462) ⭐ MORE COMPLEX

**Priority**: High - prototype for Identify_θ

**Lemma Signature**:
```lean
lemma Riemann_via_Γ₁_Identify_r (M r θ : ℝ) (β a : Idx) :
  sumIdx (fun ρ => sumIdx (fun σ => Γtot M r θ σ Idx.r β * g M σ ρ r θ)
    * Γtot M r θ ρ Idx.θ a)
  =
  sumIdx (fun lam =>
      Γ₁ M r θ lam a Idx.θ * Γtot M r θ lam β Idx.r)
```

**Operations Needed**:
1. Unfold Γ₁ on RHS: `unfold Γ₁`
2. Distribute Γ terms into sums on both sides
3. Apply Fubini to LHS: ΣρΣσ → ΣσΣρ
4. **Apply symmetries**:
   - `g_symm` (Line 1359): g_{αβ} = g_{βα}
   - `Γtot_symm` (Line 1365): Γ^k_{ab} = Γ^k_{ba}
5. Compare with `sumIdx_congr` + `ring`

**Key Challenge**: Symmetry application after Fubini

**Available Lemmas**:
- `Γ₁` definition (Lines 1370-1405): Σ_ρ g_{ρσ} Γ^ρ_{ab}
- `g_symm` (@[simp]): Can use in `simp_rw`
- `Γtot_symm` (@[simp]): Can use in `simp_rw`

**Suggested Approach**:
```lean
by
  classical
  unfold Γ₁
  -- Distribute on LHS
  conv_lhs => arg 1; ext ρ; rw [mul_comm, mul_sumIdx]
  -- Apply Fubini
  conv_lhs => rw [sumIdx_swap]
  -- Apply symmetries (may need careful placement)
  simp_rw [Γtot_symm M r θ]
  simp_rw [g_symm M]
  -- Distribute on RHS
  conv_rhs => arg 1; ext lam; rw [mul_comm, mul_sumIdx]
  -- Compare
  apply sumIdx_congr; intro i
  apply sumIdx_congr; intro j
  ring
```

**Estimated Time**: 45-60 minutes

---

### Task 4: Identify_θ (Line 1476)

**Priority**: Medium

**Operations**: Identical to Identify_r with θ ↔ r swap

**Estimated Time**: 10 minutes

---

### Task 5: Steps 4-7 (Line 1549) ⭐ NESTED SUMS

**Context**: Part of main `Riemann_via_Γ₁` proof

**Current Goal** (Line 1529):
```lean
sumIdx (fun ρ =>
    g M β ρ r θ * dCoord Idx.r ...
  - g M β ρ r θ * dCoord Idx.θ ...
  + g M β ρ r θ * sumIdx (fun lam =>
      Γtot M r θ ρ Idx.r lam * Γtot M r θ lam Idx.θ a
    - Γtot M r θ ρ Idx.θ lam * Γtot M r θ lam Idx.r a))
```

**Target Goal** (Line 1536):
```lean
  sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.r ...)
- sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.θ ...)
+ sumIdx (fun lam => sumIdx (fun ρ => g M β ρ r θ * (Γtot ... Γtot ...)))
- sumIdx (fun lam => sumIdx (fun ρ => g M β ρ r θ * (Γtot ... Γtot ...)))
```

**Operations Needed**:
1. Distribute sum over subtraction/addition
2. Distribute `g M β ρ r θ` into inner sum
3. Distribute into nested sum's subtraction
4. Apply Fubini twice to swap ρ ↔ lam

**Suggested Approach**:
```lean
by
  -- Step 1: Separate first two terms
  have h1 : ... := by
    -- Use Finset.sum_sub_distrib or manual calc steps
    sorry
  rw [h1]; clear h1

  -- Step 2: Distribute g into nested sum
  congr 1; ext ρ
  rw [mul_sumIdx]

  -- Continue with remaining steps...
  sorry
```

**Estimated Time**: 30-45 minutes

---

### Task 6: Step 8 Assembly (Line 1577) ⭐ MOST COMPLEX

**Context**: Final step of main `Riemann_via_Γ₁` proof

**Operations Needed** (documented in file):
1. Apply product rule (backwards) to recognize ∂Γ₁ terms
2. Expand metric compatibility: `dCoord_g_via_compat_ext` (Line 1973)
3. After expansion, separate into: ∂Γ₁ terms + (M - D) terms
4. **Apply all 4 auxiliary lemmas**:
   - `Riemann_via_Γ₁_Cancel_r`
   - `Riemann_via_Γ₁_Cancel_θ`
   - `Riemann_via_Γ₁_Identify_r`
   - `Riemann_via_Γ₁_Identify_θ`
5. Final simplification: `ring_nf` or multi-step `calc`

**Dependencies**: Requires Tasks 1-4 complete

**Suggested Approach**:
```lean
by
  -- This is a multi-step calc chain
  calc
    sumIdx (fun ρ => g M β ρ r θ * dCoord Idx.r ...) - ...
    _ = ... := by
      -- Apply product rule using dCoord_g_via_compat_ext
      sorry
    _ = ... := by
      -- Recognize Γ₁ terms
      sorry
    _ = ... := by
      -- Apply Cancel_r and Cancel_θ
      rw [Riemann_via_Γ₁_Cancel_r, Riemann_via_Γ₁_Cancel_θ]
      sorry
    _ = ... := by
      -- Apply Identify_r and Identify_θ
      rw [Riemann_via_Γ₁_Identify_r, Riemann_via_Γ₁_Identify_θ]
      ring_nf
```

**Estimated Time**: 60-90 minutes

---

## Infrastructure Reference

### sumIdx Lemmas (Lines 1307-1352)

```lean
lemma sumIdx_map_sub (f g : Idx → ℝ) :
  sumIdx (fun i => f i - g i) = sumIdx f - sumIdx g

lemma mul_sumIdx (c : ℝ) (f : Idx → ℝ) :
  c * sumIdx f = sumIdx (fun k => c * f k)

lemma sumIdx_swap (F : Idx → Idx → ℝ) :
  sumIdx (fun k => sumIdx (fun lam => F k lam))
  = sumIdx (fun lam => sumIdx (fun k => F k lam))

lemma sumIdx_mul (c : ℝ) (f : Idx → ℝ) :
  sumIdx (fun k => c * f k) = c * sumIdx f

lemma sumIdx_swap_comm {i j : Type} [Fintype i] [DecidableEq i] [Fintype j] [DecidableEq j]
    (F : i → j → ℝ) :
  Finset.sum Finset.univ (fun x => Finset.sum Finset.univ (fun y => F x y))
  = Finset.sum Finset.univ (fun y => Finset.sum Finset.univ (fun x => F x y))

lemma sumIdx_add_distrib (f g : Idx → ℝ) :
  sumIdx (fun i => f i + g i) = sumIdx f + sumIdx g

lemma sumIdx_congr {f g : Idx → ℝ} (h : ∀ i, f i = g i) :
  sumIdx f = sumIdx g
```

### Symmetry Lemmas (Lines 1359-1368)

```lean
@[simp] lemma g_symm (M r θ : ℝ) (α β : Idx) :
  g M α β r θ = g M β α r θ

@[simp] lemma Γtot_symm (M r θ : ℝ) (k a b : Idx) :
  Γtot M r θ k a b = Γtot M r θ k b a
```

### Key Definitions

**Γ₁ (First-kind Christoffel)** (Line 1375):
```lean
def Γ₁ (M r θ : ℝ) (α a b : Idx) : ℝ :=
  sumIdx (fun ρ => g M α ρ r θ * Γtot M r θ ρ a b)
```

**sumIdx** (from Schwarzschild.lean):
```lean
def sumIdx {α} [AddCommMonoid α] (f : Idx → α) : α := ∑ i : Idx, f i
```

**Idx** (4-element type):
```lean
inductive Idx : Type
  | t | r | θ | φ
```

---

## Proposed Helper Lemmas (Optional)

If direct tactical approach fails, consider creating these helpers:

### Helper 1: Right Multiplication Distribution
```lean
lemma sumIdx_mul_right (f : Idx → ℝ) (c : ℝ) :
  (sumIdx f) * c = sumIdx (fun k => f k * c) := by
  rw [mul_comm, mul_sumIdx]
  congr 1; ext; rw [mul_comm]
```

### Helper 2: Fubini with Outer Factor
```lean
lemma sumIdx_swap_with_factor (F : Idx → Idx → ℝ) (c : Idx → ℝ) :
  sumIdx (fun k => c k * sumIdx (fun lam => F k lam))
  = sumIdx (fun lam => sumIdx (fun k => c k * F k lam)) := by
  congr 1; ext k
  rw [mul_sumIdx]
  rw [sumIdx_swap]
```

These could simplify Cancel lemmas significantly.

---

## Testing Strategy

### Incremental Approach

1. **Start with Cancel_r**:
   - Get this working first
   - Build: `lake build Papers.P5_GeneralRelativity.GR.Riemann`
   - Verify: 1 less sorry

2. **Replicate to Cancel_θ**:
   - Should be quick copy-paste
   - Build and verify

3. **Tackle Identify_r**:
   - More complex due to symmetries
   - Test incrementally

4. **Replicate to Identify_θ**

5. **Steps 4-7 in main proof**

6. **Step 8 assembly** (last, requires all 4 lemmas)

### Debugging Tips

If stuck on pattern matching:
- Use `trace` to see exact goal state: `trace "{goal}"`
- Try `#check` to verify lemma types
- Consider `unfold sumIdx` to work at `Finset.sum` level
- Use `show` to explicit restate goal
- Break into smaller `have` statements

---

## Expected Outcomes

### Success Metrics

1. ✅ Build passes: `lake build Papers.P5_GeneralRelativity.GR.Riemann`
2. ✅ Zero sorries in lines 1418-1577
3. ✅ All 6 tactical proofs complete
4. ✅ No new warnings or errors introduced

### Completion Checklist

- [ ] Cancel_r proven (Line 1430)
- [ ] Cancel_θ proven (Line 1444)
- [ ] Identify_r proven (Line 1462)
- [ ] Identify_θ proven (Line 1476)
- [ ] Steps 4-7 proven (Line 1549)
- [ ] Step 8 assembly proven (Line 1577)
- [ ] Build passes with 0 errors
- [ ] Git commit with message: "feat: complete Phase 3 tactical proofs for Riemann_via_Γ₁"

---

## Background Reading (If Needed)

### Recent Documentation

1. **`STEP_8_FINAL_STATUS_OCT16_V4.md`**
   - Complete analysis of pattern matching challenges
   - All attempted solutions documented
   - Lessons learned

2. **`TACTICAL_IMPLEMENTATION_STATUS_OCT16_V2.md`**
   - Infrastructure verification
   - Correct 4-lemma approach
   - Comparison to original plan

3. **`PHASE_3_IMPLEMENTATION_COMPLETE_OCT16.md`**
   - Initial structural implementation
   - Success criteria
   - Timeline

### SP's Memorandum (Oct 16, 2025)

The Senior Professor provided detailed tactical guidance including:
- Exact tactic sequences for each lemma
- "Selective Fubini" strategy (apply swap to one side only)
- Multi-step Step 8 assembly approach

This is the authoritative source for the proof strategy.

---

## Questions?

If you encounter issues:

1. **Check documentation**: 3 detailed reports in same directory
2. **Verify infrastructure**: All lemmas in Lines 1307-1405 should work
3. **Test incrementally**: Build after each lemma completion
4. **Consider helpers**: If pattern matching is consistently blocked

**Expected total time**: 3-4 hours for all 6 proofs

---

## Final Note

This is a **well-defined tactical task**. The mathematical structure is complete and verified. What's needed is expertise with Lean 4's syntactic requirements - exactly your strength.

The proof will be a significant contribution to the formalization, completing Phase 3 of the Riemann tensor verification.

**Good luck!**

---

**Prepared by**: Claude (AI Assistant)
**Date**: October 16, 2025
**For**: Junior Professor (Tactical Expert)
**Estimated Completion**: 3-4 hours
**Current Build Status**: ✅ 0 errors, 6 documented sorries
**Priority**: High (blocks Phase 4 progress)
