# Consult: Junior Professor - Tactical Implementation of Modular Strategy for Diagonal Ricci Cases

**Date**: October 6, 2025
**Topic**: Tactical assistance needed to implement Senior Professor's modular strategy
**Status**: Phase 2 complete (0 sorries), Phase 3 refactoring in progress
**Urgency**: High - blocking completion of main scientific result

---

## Executive Summary

**Phase 2 Status**: ✅ **COMPLETE** - All 6 Riemann component lemmas proven with 0 sorries!

**Phase 3 Status**: 🚧 **IN PROGRESS** - Refactoring diagonal Ricci cases per Senior Professor's guidance

**Current Blocker**: Tactical challenge in converting between mixed and covariant Riemann tensors

**What We Need**: Your expertise in Lean tactics to successfully apply the modular strategy

---

## Context: Senior Professor's Strategic Direction

The Senior Professor reviewed our previous "Patch M" approach and identified a **critical strategic failure**. We were using `_reduce` lemmas which expand everything into Christoffel symbols, leading to:

1. ❌ Monolithic algebraic complexity
2. ❌ Failed trigonometric cancellations
3. ❌ Spurious θ-dependence (mathematically incorrect)

**The numerical test confirmed**: Our polynomial didn't equal zero (gave 2.5 for M=1, r=3, θ=π/4)

### Senior Professor's Prescribed Strategy

**Use the modular approach with Phase 2 component lemmas:**

```
R_tt = g^ρσ R_ρtσt (using inverse metric and covariant Riemann)
     = g^rr R_rtrt + g^θθ R_θtθt + g^φφ R_φtφt
     = f(r)·(-2M/r³) + (1/r²)·(Mf/r) + (1/(r²sin²θ))·(Mf·sin²θ/r)
     = -2Mf/r³ + Mf/r³ + Mf/r³
     = 0  ✓
```

**Key insight**: Trigonometric terms cancel trivially (`sin²θ / sin²θ = 1`), which failed in the monolithic expansion.

---

## Phase 2: Component Lemmas - COMPLETE ✅

All 6 independent Schwarzschild Riemann components are proven (lines 4897-5149):

### Successfully Proven Component Lemmas

1. **`Riemann_trtr_eq`** (lines 4912-4937): R_trtr = -2M/r³ ✅
2. **`Riemann_tθtθ_eq`** (lines 4939-5002): R_tθtθ = M·f(r)/r ✅
3. **`Riemann_tφtφ_eq`** (lines 5004-5026): R_tφtφ = M·f(r)·sin²θ/r ✅
4. **`Riemann_rθrθ_eq`** (lines 5028-5051): R_rθrθ = -M/(r·f(r)) ✅
5. **`Riemann_rφrφ_eq`** (lines 5053-5076): R_rφrφ = -M·sin²θ/(r·f(r)) ✅
6. **`Riemann_θφθφ_eq`** (lines 5078-5149): R_θφθφ = 2Mr·sin²θ ✅
   - Uses cross-multiplication to handle θ=0,π singularity
   - Two-lemma pattern per your Oct 5 guidance

**Verification Status**: 0 sorries, all lemmas compile cleanly

**Proof Strategy** (per your guidance):
1. Contract first index using `Riemann_contract_first`
2. Expand RiemannUp only for concrete indices
3. Insert closed-form pieces (derivatives, Christoffel symbols)
4. Close with `field_simp` + `ring`

---

## Phase 3: Refactoring Diagonal Ricci Cases

### The Challenge

We need to prove: `RicciContraction M r θ a b = 0` for diagonal cases (t.t, r.r, θ.θ, φ.φ)

**Definition**:
```lean
noncomputable def RicciContraction (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun ρ => Riemann M r θ ρ a ρ b)
```

This is **Scenario B** from Senior Professor's memo: Ricci defined via mixed tensor R^ρ_aρb.

### Mathematical Path (for case t.t)

```
R_tt = Σ_ρ R^ρ_tρt
     = Σ_ρ (g_ρρ)⁻¹ · R_ρtρt    [convert mixed to covariant]
     = (g_rr)⁻¹·R_rtrt + (g_θθ)⁻¹·R_θtθt + (g_φφ)⁻¹·R_φtφt
     = f·(-2M/r³) + r²·(Mf/r) + r²sin²θ·(Mf·sin²θ/r)    [use _eq lemmas]
     = -2Mf/r³ + Mf/r³ + Mf/r³ = 0  ✓
```

### Infrastructure Available

**`Riemann_contract_first`** (line 1120):
```lean
@[simp] lemma Riemann_contract_first
  (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d = g M a a r θ * RiemannUp M r θ a b c d
```

This relates covariant Riemann to mixed RiemannUp via the metric.

---

## Tactical Exploration: What We Tried

### Current Implementation (case t.t, lines 5156-5206)

```lean
case t.t =>
  classical
  have hf_ne : f M r ≠ 0 := Exterior.f_ne_zero h_ext
  have hθ : Real.sin θ ≠ 0 := h_sin_nz

  -- Step 1: Expand sum, drop ρ=t term (R^t_ttt = 0)
  simp only [sumIdx_expand]
  simp only [Riemann_first_equal_zero_ext M r θ h_ext h_sin_nz]

  -- Goal after Step 1:
  -- 0 + Riemann ρ=r + Riemann ρ=θ + Riemann ρ=φ = 0

  -- Step 2: Apply symmetries to normalize index order
  have h_rt : Riemann M r θ Idx.r Idx.t Idx.r Idx.t = Riemann M r θ Idx.t Idx.r Idx.t Idx.r := by [...]
  have h_th : Riemann M r θ Idx.θ Idx.t Idx.θ Idx.t = Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ := by [...]
  have h_ph : Riemann M r θ Idx.φ Idx.t Idx.φ Idx.t = Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ := by [...]

  rw [h_rt, h_th, h_ph]

  -- Goal after Step 2:
  -- 0 + Riemann t r t r + Riemann t θ t θ + Riemann t φ t φ = 0

  -- Step 3: ❌ THIS IS WHERE WE'RE STUCK
  -- Need to convert: Riemann ρ a ρ b (mixed in def) to covariant form
  -- But Riemann_contract_first is simp-lemma, already applied!

  -- After simp_only [Riemann_contract_first], we get:
  -- g M t t r θ * RiemannUp M r θ t Idx.r t Idx.r +
  -- g M t t r θ * RiemannUp M r θ t Idx.θ t Idx.θ +
  -- g M t t r θ * RiemannUp M r θ t φ t φ = 0

  -- We tried: rw [←Riemann_contract_first ...] to go backwards
  -- ERROR: "Did not find an occurrence of the pattern"

  -- Step 4: BLOCKED - can't apply _eq lemmas because we have RiemannUp, not Riemann
```

### Why the Backwards Rewrite Fails

The pattern in `Riemann_contract_first` is:
```lean
Riemann M r θ a b c d = g M a a r θ * RiemannUp M r θ a b c d
```

To rewrite backwards (`←`), Lean needs to find `g M a a r θ * RiemannUp M r θ a b c d` in the goal.

**But the actual goal has**:
```lean
g M t t r θ * RiemannUp M r θ t Idx.r t Idx.r
```

The indices are **concrete values** (Idx.r, Idx.θ, etc.), not the pattern variable `a`. Lean's pattern matcher doesn't recognize this as an instance of the lemma.

---

## Request for Junior Professor

### Question 1: How to Convert RiemannUp to Riemann?

**Current goal** (after Step 2):
```lean
g M t t r θ * RiemannUp M r θ t Idx.r t Idx.r +
g M t t r θ * RiemannUp M r θ t Idx.θ t Idx.θ +
g M t t r θ * RiemannUp M r θ t φ t φ = 0
```

**Desired goal**:
```lean
Riemann M r θ t Idx.r t Idx.r +
Riemann M r θ t Idx.θ t Idx.θ +
Riemann M r θ t φ t φ = 0
```

**Tactical options we considered**:
- ❌ `rw [←Riemann_contract_first ...]` - pattern doesn't match
- ❌ `simp only [←Riemann_contract_first]` - doesn't apply backward
- ❓ `conv_lhs => { ... }` - how to target the three terms?
- ❓ Create helper lemmas for each concrete index pattern?
- ❓ Use `calc` to manually rewrite each term?

### Question 2: Should We Refactor RicciContraction?

**Alternative approach**: Redefine Ricci using inverse metric directly:

```lean
noncomputable def RicciContractionAlt (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun ρ => gInv M r θ ρ ρ * Riemann M r θ ρ a ρ b)
```

This would give us covariant Riemann directly. But:
- ✅ Simpler tactical path
- ❌ High-impact infrastructure change
- ❌ Need to prove equivalence to old definition
- ❌ May break other proofs

**Is this refactoring worth it?**

### Question 3: Pattern Matching with Concrete Indices

More generally: When a `@[simp]` lemma has pattern variables but the goal has concrete values, how do we:

1. Apply it forward (simp does this automatically) ✓
2. Apply it backward (how?) ❓
3. Apply it selectively to specific subterms (how?) ❓

This seems like a common tactical challenge. What's the standard approach?

---

## Minimal Reproducible Example

```lean
-- Given
@[simp] lemma my_lemma (a : Idx) : foo a = bar a * baz a

-- Goal has concrete index
⊢ bar Idx.r * baz Idx.r = 0

-- Want to rewrite to
⊢ foo Idx.r = 0

-- This fails:
rw [←my_lemma Idx.r]  -- ERROR: "Did not find an occurrence of the pattern"

-- Why? How to fix?
```

---

## Current Error Count

**Total**: 7 errors
- 3 pre-existing infrastructure (not blocking)
- 4 diagonal Ricci cases (all blocked by same tactical issue)

**Impact**: Blocking completion of main scientific result (Ricci = 0 for Schwarzschild)

---

## Files and Line References

- **Main file**: `Papers/P5_GeneralRelativity/GR/Riemann.lean`
- **Phase 2 component lemmas**: Lines 4897-5149 ✅
- **Diagonal case t.t**: Lines 5156-5206 (current WIP)
- **Infrastructure**: `Riemann_contract_first` at line 1120
- **Senior Professor's memo**: `GR/CONSULT_SENIOR_PROF_RICCI_TT_POLYNOMIAL.md`

---

## What We've Learned

1. **Modular strategy is correct** ✅ - Senior Professor confirmed the mathematical approach
2. **Phase 2 lemmas are robust** ✅ - All proven with clear, simple tactics
3. **Tactical gap identified** 🎯 - Need to bridge mixed ↔ covariant tensor representations
4. **Pattern matching challenge** 📚 - Concrete indices vs pattern variables

---

## Summary

We've successfully completed Phase 2 (all component lemmas proven) and have a clear mathematical strategy for Phase 3 (modular diagonal Ricci proofs).

**The tactical challenge**: Converting between `g * RiemannUp` (mixed) and `Riemann` (covariant) when indices are concrete values.

Your tactical expertise would help us:
1. Complete the 4 diagonal cases using the modular strategy
2. Learn the correct Lean patterns for this type of rewrite
3. Finish the main scientific result (Ricci = 0)

Thank you for your guidance!

---

**Assistant**: Claude Code
**Current Branch**: feat/p0.2-invariants
**Build Status**: 7 errors (4 tactical, 3 infrastructure)
