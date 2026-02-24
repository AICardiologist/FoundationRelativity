# Memo to JP: Four-Block Strategy Tactical Guidance Request
**Date**: October 24, 2025  
**From**: Claude Code Implementation Team  
**To**: JP (Lean Expert)  
**Subject**: Bounded Proof Tactics for Four-Block Strategy Lemmas

---

## Executive Summary

✅ **Accomplished**: Four-Block Strategy infrastructure fully implemented and committed (commit `64a227c`)  
⏳ **Status**: 7 block lemmas need bounded proofs (all have structure and sorries in place)  
🎯 **Request**: Specific bounded tactic sequences for each block  

**Build**: ✅ 0 errors, 23 sorries, clean compilation

---

## What Was Accomplished

### 1. Infrastructure Complete ✅

**Helper Lemmas Added**:
```lean
@[simp] lemma sumIdx_add3 (f g h : Idx → ℝ) :
  sumIdx (fun i => f i + g i + h i) = sumIdx f + sumIdx g + sumIdx h

lemma reorder_triple_mul (A B C : ℝ) : A * B * C = A * C * B := by ring

@[simp] lemma sumIdx_zero : sumIdx (fun _ : Idx => (0 : ℝ)) = 0
```

**All 7 Blocks Structured** (Riemann.lean:6270-6520):
- Block 0: `clairaut_g`, `expand_P_pointwise_a/b`, `expand_Pa/Pb`
- Block A: `payload_cancel_a/b/all`
- Block C: `main_to_commutator`
- Block D: `dGamma_match`
- Block B: `cross_block_zero`
- Final: `algebraic_identity` (15-line assembly)

**Deleted Flawed Code**:
- Removed ~630 lines of previous monolithic approach
- Eliminated duplicate lemma declarations
- Clean build with 0 errors

### 2. Mathematical Framework Validated ✅

Per Senior Professor's October 24 memo:
- ✅ Correct formula: **P + C' = RHS** (not C' = RHS)
- ✅ Block A is the linchpin (payload cancellation)
- ✅ No use of metric compatibility (∇g = 0)
- ✅ All blocks follow corrected strategy

---

## What Needs Bounded Proofs (7 Lemmas)

### Block 0: Expand P (3 lemmas with sorries)

#### 1. `clairaut_g` (Line 6283)
**Signature**:
```lean
lemma clairaut_g (M : ℝ) (ρ b : Idx) (r θ : ℝ) (h_ext : Exterior M r θ) (μ ν : Idx) :
  dCoord μ (fun r θ => dCoord ν (fun r θ => g M ρ b r θ) r θ) r θ
= dCoord ν (fun r θ => dCoord μ (fun r θ => g M ρ b r θ) r θ) r θ
```

**Current Status**:
```lean
cases ρ <;> cases b <;> simp [g, dCoord] <;> sorry
```

**Strategy Needed**:
- Off-diagonals: `g = 0` so both sides are 0 (trivial)
- Diagonals: Use ContDiffAt facts + Mathlib Clairaut theorem

**Question**: How to invoke Clairaut for C² functions in our setup?

---

#### 2. `expand_P_pointwise_a` (Line 6303)
**Goal**: Expand `dCoord μ(nabla_g) - dCoord ν(nabla_g)` into `(D) ∂Γ terms + (A) payload terms`

**Formula A** (nabla_g definition, Line 2661):
```lean
nabla_g M r θ c a b = 
  dCoord c (fun r θ => g M a b r θ) r θ
  - sumIdx (fun e => Γtot M r θ e c a * g M e b r θ)
  - sumIdx (fun e => Γtot M r θ e c b * g M a e r θ)
```

**Current Status**: `sorry`

**Strategy Needed**:
```lean
-- Unfold nabla_g
simp only [nabla_g, sub_eq_add_neg]
-- Push dCoord through +/-/Σ using:
--   dCoord_add, dCoord_sub, dCoord_sumIdx, dCoord_mul_of_diff
-- ∂∂g terms cancel via clairaut_g
-- Group by (∂Γ)g and Γ∂g using flatteners and sumIdx_add3
```

**Question**: Exact sequence of dCoord lemmas and how to apply clairaut_g for cancellation?

---

#### 3. `expand_P_pointwise_b` (Line 6324)
Mirror of `expand_P_pointwise_a` with `a ↔ b` swapped.

**Current Status**: `sorry`

**Strategy Needed**: Same as pointwise_a but for b-branch.

---

#### 4. `expand_Pa` and `expand_Pb` (Lines 6341, 6359)
**Goal**: Lift pointwise lemmas across Σ_ρ

**Current Status**:
```lean
classical
-- TODO: This requires expand_P_pointwise_a to be proven first
sorry
```

**Strategy Needed**:
```lean
have hρ : ∀ ρ, _ := expand_P_pointwise_a M r θ h_ext μ ν a b
have h := sumIdx_congr hρ
-- Then distribute the sum
rw [sumIdx_add3] at h
exact h
```

**Question**: Should work once pointwise lemmas are proven. Confirm this pattern?

---

### Block A: Payload Cancellation (3 lemmas)

#### 5. `payload_cancel_a` (Line 6382)
**Goal**: Prove P_payload,a + C'_payload,a = 0

**Attempted Tactics** (failed during compilation):
```lean
rw [← sumIdx_add_distrib]
apply sumIdx_congr; intro ρ
ring
```

**Error**: `Tactic 'apply' failed: could not unify the conclusion of @sumIdx_congr`

**Question**: 
- Why is `apply sumIdx_congr` failing after `rw [← sumIdx_add_distrib]`?
- Do we need an intermediate `have` lemma?
- Alternative: `apply sumIdx_congr` then `intro ρ; ring` in proof term form?

---

#### 6. `payload_cancel_b` (Line 6390)
Mirror of `payload_cancel_a`.

**Same tactical issue** as above.

---

#### 7. `payload_cancel_all` (Line 6403)
**Goal**: Combine both payload cancellations

**Attempted Strategy**:
```lean
have ha := payload_cancel_a M r θ h_ext μ ν a b
have hb := payload_cancel_b M r θ h_ext μ ν a b
calc _ = (_ + _) + (_ + _) := by ring
     _ = 0 + 0 := by rw [ha, hb]
     _ = 0 := by ring
```

**Error**: `calc expression has type ?m.109 = 0 but is expected to have type ...`

**Question**: How to structure the calc chain when the LHS is a large explicit sum?

---

### Block C: Main to Commutator (1 lemma)

#### 8. `main_to_commutator` (Line 6437)
**Goal**: Transform C'_main into RHS_ΓΓ

**Strategy Needed** (from your Oct 24 memo):
- Use `sumIdx_swap` to swap Σ_ρ Σ_e
- Pointwise `sumIdx_congr` + `ring` to reorder factors
- Apply collectors to bundle terms

**Current Status**: `sorry`

**Question**: Exact sequence of rewrites? Example:
```lean
-- Swap sums Σ_ρ Σ_e → Σ_e Σ_ρ
rw [sumIdx_swap_comm]
-- Reorder factors inside
have h_reorder : ∀ e ρ, ... := by intro e ρ; ring
rw [sumIdx_congr (sumIdx_congr h_reorder)]
-- Apply metric symmetry g M e b = g M b e
-- Bundle into RHS form
```

---

### Block D: ∂Γ Matching (1 lemma)

#### 9. `dGamma_match` (Line 6468)
**Goal**: Match P_∂Γ with RHS_∂Γ

**Strategy Needed**:
- Swap Σ_ρ Σ_e
- Relabel dummy indices
- Use commutativity

**Current Status**: `sorry`

**Question**: Similar to Block C - exact rewrite sequence?

---

### Block B: Cross Cancellation (1 lemma)

#### 10. `cross_block_zero` (Line 6493)
**Goal**: Prove cross terms vanish

**Strategy Needed** (from your memo):
- Diagonality: `g_ρe = 0` for `ρ ≠ e` reduces double sum to diagonal
- On diagonal: kernel cancels by commutativity

**Current Status**: `sorry`

**Question**: How to apply diagonality in pointwise context?
```lean
-- Reduce to diagonal
simp [g] in pointwise?
-- Apply fold_diag_kernel₂
-- Use commutativity Γtot_symm
```

---

## Specific Questions

### Q1: Block A Tactical Issue
Why does this fail?
```lean
lemma payload_cancel_a ... :=
  ( sumIdx (fun ρ => - Γ... * dCoord... + Γ... * dCoord...) )
+ ( sumIdx (fun ρ => - Γ... * dCoord... + Γ... * dCoord...) )
  = 0 := by
  rw [← sumIdx_add_distrib]
  apply sumIdx_congr  -- ❌ unification error
  intro ρ
  ring
```

The goal after `rw [← sumIdx_add_distrib]` should be:
```
⊢ sumIdx (fun ρ => (...) + (...)) = 0
```

Shouldn't `apply sumIdx_congr` work here to go pointwise?

**Alternative approaches to try**:
1. `apply sumIdx_congr; intro ρ; ring` in one line?
2. Use `have` instead: `have h : ∀ ρ, ... := by intro ρ; ring; simpa using sumIdx_congr h`?
3. Direct proof term: `sumIdx_congr (fun ρ => by ring)`?

### Q2: Clairaut Application
We have `clairaut_g` stating mixed partials commute. In `expand_P_pointwise_a`, after pushing dCoord through nabla_g, we get ∂∂g terms. How do we invoke `clairaut_g` to cancel them?

Example context after expansion:
```
... + dCoord μ (fun r θ => dCoord ν (fun r θ => g M ρ b r θ) r θ) r θ
    - dCoord ν (fun r θ => dCoord μ (fun r θ => g M ρ b r θ) r θ) r θ
    + ...
```

Do we:
1. `have hmixed := clairaut_g M ρ b r θ h_ext μ ν`?
2. Then `rw [hmixed]`?
3. Or `simp only [clairaut_g]`?

### Q3: Sum Manipulation in Blocks C/D
For transforming:
```
sumIdx (fun ρ => sumIdx (fun e => Γ * Γ * g e b))
```
into:
```
sumIdx (fun ρ => g b ρ * sumIdx (fun lam => Γ * Γ))
```

Is the pattern:
1. `rw [sumIdx_swap_comm]` to swap order
2. `apply sumIdx_congr; intro ρ`
3. Factor out `g` using collectors
4. Relabel `e → lam`?

---

## Available Infrastructure

### Proven Lemmas We Have:
- ✅ `sumIdx_add_distrib`, `sumIdx_mul`, `sumIdx_sub_same_right`
- ✅ `sumIdx_swap_comm` (Fubini)
- ✅ `sumIdx_congr` (pointwise equality)
- ✅ `sumIdx_add3` (3-term distributor)
- ✅ `Γtot_symm` (torsion-free)
- ✅ `g_symm` (metric symmetry)
- ✅ Expansion kit: `expand_nabla_g_pointwise_a/b`, `expand_Ca/Cb` (all proven in previous session)

### dCoord Lemmas Available:
- `dCoord_add`, `dCoord_sub`, `dCoord_mul_of_diff`
- `dCoord_sumIdx` (pushes dCoord into sums)
- `dCoord_commute_for_g_all` (Clairaut for metric)

---

## Request

Please provide **bounded, deterministic tactic sequences** for the 7 lemmas above. Specifically:

1. **Block 0** (expand P):
   - How to expand nabla_g and cancel ∂∂g terms
   - Exact sequence of dCoord lemmas

2. **Block A** (payload cancellation):
   - Fix for the `apply sumIdx_congr` unification issue
   - Correct calc chain structure for `payload_cancel_all`

3. **Blocks C, D, B**:
   - Exact sum swapping and factor reordering sequences
   - How to apply diagonality and collectors

**Format preferred**: Drop-in proof skeletons like you provided for the expansion kit (those worked perfectly once we fixed the environment-specific issues).

---

## Current Build Status

```
Build completed successfully (3078 jobs).
✅ 0 compilation errors
⏳ 23 sorries (all in Four-Block Strategy infrastructure)
```

**Files**:
- `Riemann.lean`: Lines 6270-6520 (Four-Block Strategy)
- Commit: `64a227c` - "refactor: implement Four-Block Strategy for algebraic_identity"

---

## Bottom Line

✅ **Mathematical framework**: Correct (SP validated)  
✅ **Structure**: Complete (all blocks in place)  
✅ **Build**: Stable (0 errors)  
⏳ **Proofs**: Need bounded tactics for 7 lemmas

With your bounded proof guidance, we can complete the Four-Block Strategy and finalize `algebraic_identity`. The infrastructure is solid - just need the tactical patterns.

**Thank you for your continued guidance!**

---

**Attachments**:
- Current Riemann.lean (Four-Block Strategy section)
- SESSION_STATUS_OCT24_FOUR_BLOCK_STRATEGY.md (implementation details)
- Build verification output

**Claude Code Team**  
October 24, 2025
