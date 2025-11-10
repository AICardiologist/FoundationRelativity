# Infrastructure Audit: Index Relabeling and Sum Manipulation

**Date**: October 30, 2025
**Status**: ✅ **ALL REQUIRED INFRASTRUCTURE EXISTS**
**Purpose**: Document available lemmas for implementing SP's correct algebraic approach

---

## Executive Summary

**Good news**: All infrastructure required for SP's index relabeling + Fubini approach **already exists** in Riemann.lean. The codebase contains:
- ✅ Index relabeling/renaming lemmas
- ✅ Fubini (sum swapping) lemmas
- ✅ Congruence lemmas for pointwise equality
- ✅ Factor swapping and commutativity lemmas
- ✅ **Working example**: `main_to_commutator` lemma (lines 8994-9026) demonstrates the exact pattern SP prescribed

**The correct algebraic approach is already implemented in Block C**. The quartet decomposition strategy (lines ~7280-7880) was an **incorrect parallel attempt** that must be abandoned.

---

## Required Infrastructure (Per SP's Guidance)

SP's transformation requires:
1. **Index relabeling**: Swap dummy summation variables (ρ ↔ e)
2. **Fubini theorem**: Swap order of finite summations
3. **Commutativity**: Reorder scalar factors
4. **Congruence**: Apply pointwise equality to sums

---

## Available Lemmas

### 1. Index Relabeling

**Line 2072**: `sumIdx_rename`
```lean
@[simp] lemma sumIdx_rename (f : Idx → ℝ) :
  sumIdx (fun ρ => f ρ) = sumIdx (fun lam => f lam) := rfl
```
**Purpose**: Alpha-renaming of bound variables (purely syntactic)

### 2. Congruence (Pointwise Equality)

**Line 1708**: `sumIdx_congr`
```lean
/-- Congruence for sumIdx: if functions are pointwise equal, sums are equal. -/
lemma sumIdx_congr {f g : Idx → ℝ} (h : ∀ i, f i = g i) :
  sumIdx f = sumIdx g := by
  congr 1
```
**Purpose**: Lift pointwise equality to sum equality
**Usage**: Apply after showing terms are equal for all indices

### 3. Fubini Theorem (Sum Swapping)

**Line 1627**: `sumIdx_swap` (marked @[simp])
```lean
/-- Fubini for finite sums: swap order of summation. -/
@[simp] lemma sumIdx_swap (F : Idx → Idx → ℝ) :
  sumIdx (fun k => sumIdx (fun lam => F k lam))
    = sumIdx (fun lam => sumIdx (fun k => F k lam))
```
**Purpose**: Swap outer and inner summation indices
**Note**: Marked @[simp] for automatic application

**Line 1636**: `sumIdx_swap_args` (NOT @[simp])
```lean
/-- Swap the two dummy indices inside a double `sumIdx`. Purely algebraic.
    NOTE: Not marked @[simp] to avoid bidirectional rewriting loops. Use explicitly. -/
lemma sumIdx_swap_args (F : Idx → Idx → ℝ) :
  sumIdx (fun ρ => sumIdx (fun e => F ρ e))
    = sumIdx (fun ρ => sumIdx (fun e => F e ρ))
```
**Purpose**: Swap the argument order within a double sum
**Note**: Requires explicit use with `rw`

**Line 2402**: `sumIdx_mul_sumIdx_swap`
```lean
/-- Generalized Fubini with multiplication distribution.
    Σρ (G ρ * Σλ (F ρ λ)) = Σλ (Σρ (G ρ * F ρ λ))
    Combines mul_sumIdx_distrib and sumIdx_swap. -/
lemma sumIdx_mul_sumIdx_swap (G : Idx → ℝ) (F : Idx → Idx → ℝ) :
  sumIdx (fun ρ => G ρ * sumIdx (fun lam => F ρ lam))
  = sumIdx (fun lam => sumIdx (fun ρ => G ρ * F ρ lam))
```
**Purpose**: Specialized Fubini for factor-sum structures
**Critical**: Avoids infinite loops in simp

### 4. Factor Swapping (Commutativity)

**Line 2156**: `sumIdx_swap_factors`
```lean
/-- Swap the order of factors inside a `sumIdx` body (keep out of simp). -/
lemma sumIdx_swap_factors (A B : Idx → ℝ) :
  sumIdx (fun ρ => A ρ * B ρ) = sumIdx (fun ρ => B ρ * A ρ)
```
**Purpose**: Commutativity of multiplication under summation
**Note**: NOT @[simp] to avoid loops

### 5. Metric Symmetry

**Line 1393**: `g_symm` (referenced in multiple proofs)
```lean
g M i j r θ = g M j i r θ
```
**Purpose**: Schwarzschild metric is symmetric
**Usage**: Apply with `simp only [g_symm]` or directly in calc chains

### 6. Scalar Commutativity

**Built-in**: `ring` tactic
**Purpose**: Handles all algebraic manipulations including:
- Multiplication commutativity: `a * b = b * a`
- Associativity: `(a * b) * c = a * (b * c)`
- Distributivity: `a * (b + c) = a * b + a * c`

---

## Working Example: `main_to_commutator` (Block C)

**Location**: Lines 8994-9026

**Purpose**: Prove `C'_main = RHS_ΓΓ` using purely algebraic approach

**Strategy** (matches SP's prescription):
```lean
lemma main_to_commutator (M r θ : ℝ) (h_ext : Exterior M r θ) (μ ν a b : Idx) :
  -- LHS: C'_Main with (ρ, e) as summation indices
  ( sumIdx (fun ρ => sumIdx (fun e =>
      Γtot M r θ ρ μ a * Γtot M r θ e ν ρ * g M e b r θ
    - Γtot M r θ ρ ν a * Γtot M r θ e μ ρ * g M e b r θ)) )
  =
  -- RHS: RHS_ΓΓ with (e, ρ) as summation indices (swapped!)
  ( sumIdx (fun e => g M e b r θ * (sumIdx (fun ρ =>
      Γtot M r θ e ν ρ * Γtot M r θ ρ μ a
    - Γtot M r θ e μ ρ * Γtot M r θ ρ ν a))) )
```

**Proof steps**:
1. **Line 9015**: `rw [sumIdx_swap]` - Swap sum order: Σ_ρ Σ_e → Σ_e Σ_ρ (Fubini)
2. **Line 9017**: `apply sumIdx_congr` - Apply pointwise equality
3. **Line 9020**: `rw [← sumIdx_mul]` - Factor out `g M e b r θ`
4. **Line 9021**: `apply sumIdx_congr` - Apply pointwise equality on inner sum
5. **Line 9024**: `simp only [g_symm]` - Use metric symmetry
6. **Line 9025**: `ring` - Scalar commutativity and regrouping

**Result**: ✅ **Proof compiles successfully** (part of working Block C strategy)

---

## Why This Matters: Quartet vs. Algebraic Approach

### Correct Approach (Block C - Already Implemented)

**File structure**:
- Lines 8990-9026: `main_to_commutator` ✅ WORKING
- Uses: Fubini + index manipulation + metric symmetry
- **No false mathematical assumptions**

**Key insight**: The correct approach was already implemented by Senior Professor in the Four-Block Strategy. Block C uses purely algebraic transformations.

### Incorrect Approach (Quartet Decomposition - ABANDONED)

**File structure**:
- Lines 7247-7278: JP's splitter lemmas (mechanically sound but serve wrong strategy)
- Lines 7284-7880: `ΓΓ_quartet_split_b` and `ΓΓ_quartet_split_a` ❌ UNSOUND
  - Line 7303: Unsolved goal (requires false identity)
  - Line 7605: Unsolved goal (requires false identity)

**Fatal flaw**: Attempts to prove `Σ_e (Γ^b_{νe} · Γ^e_{μa}) = Σ_e (Γ^b_{μe} · Γ^e_{νa})`
- This is equivalent to claiming connection matrices commute
- **Contradicts curvature** (Riemann tensor measures non-commutativity)
- SP provided explicit counterexample showing LHS ≠ RHS in Schwarzschild

---

## Comparison: SP's Transformation vs. `main_to_commutator`

### SP's Prescribed Steps (from CRITICAL_SP_FINDING_FALSE_IDENTITY_OCT30.md)

**For 'a' branch**:
```
Step 1: Start with C'_Main,a = Σ_{ρ,e} [(Γ^ρ_{μa} Γ^e_{νρ} - Γ^ρ_{νa} Γ^e_{μρ}) g_{eb}]
Step 2: Index relabeling: swap ρ ↔ e
Step 3: Fubini + commutativity
Step 4: Result: C'_Main,a = Σ_{ρ,e} [(Γ^ρ_{νe} Γ^e_{μa} - Γ^ρ_{μe} Γ^e_{νa}) g_{ρb}]
```

### `main_to_commutator` Implementation (Line 8994)

**Actual code**:
```lean
-- Start: Σ_ρ Σ_e [ (Γ^ρ_{μa} Γ^e_{νρ} - Γ^ρ_{νa} Γ^e_{μρ}) g_{eb} ]
rw [sumIdx_swap]          -- Fubini: Σ_ρ Σ_e → Σ_e Σ_ρ
apply sumIdx_congr        -- Pointwise equality
rw [← sumIdx_mul]         -- Factor g outside: g_{eb} * Σ_ρ (...)
simp only [g_symm]        -- Metric symmetry: g_{eb} = g_{be}
ring                      -- Commutativity: rearrange Christoffel products
-- Result: Σ_e g_{eb} Σ_ρ [ (Γ^e_{νρ} Γ^ρ_{μa} - Γ^e_{μρ} Γ^ρ_{νa}) ]
```

**Match**: ✅ **Perfect alignment** with SP's strategy!

---

## Action Items

### ✅ COMPLETED
1. Audit infrastructure lemmas
2. Identify that correct approach exists in `main_to_commutator`
3. Confirm quartet decomposition is unsound
4. Document findings

### 🔄 NEXT STEPS

**PRIORITY 1**: Consult with JP/Paul
- Share this infrastructure audit
- Confirm that `main_to_commutator` already implements SP's correct approach
- Get guidance on removing quartet decomposition code

**PRIORITY 2**: Code cleanup
- Remove or comment out:
  - Lines 7284-7880: `ΓΓ_quartet_split_b` and `ΓΓ_quartet_split_a` proofs
  - Any downstream code depending on quartet strategy
- Preserve JP's splitter lemmas (lines 7247-7278) as they're mechanically sound
- Update documentation to reference correct Block C approach

**PRIORITY 3**: Verify algebraic_identity completion path
- Check if `algebraic_identity_four_block_old` (line 9127) can be completed
- Four blocks are proven:
  - Block A: `payload_cancel_all` ✅
  - Block B: `cross_block_zero` ✅ (lines 9058-9117)
  - Block C: `main_to_commutator` ✅ (lines 8994-9026)
  - Block D: `dGamma_match` ✅ (lines 9031-9052)
- Assembly blocked by `expand_P_ab` (line 9141 comment)

---

## Summary for User

### Infrastructure Status: ✅ READY

All lemmas needed for SP's correct algebraic approach exist:
- `sumIdx_congr` - Pointwise equality
- `sumIdx_swap` - Fubini (sum swapping)
- `sumIdx_swap_args` - Argument swapping
- `sumIdx_mul` - Factor extraction
- `sumIdx_swap_factors` - Commutativity
- `g_symm` - Metric symmetry
- `ring` - Scalar algebra

### Key Discovery: Correct Implementation Already Exists

**Block C** (`main_to_commutator` at lines 8994-9026) **already implements SP's prescribed approach**:
1. Uses Fubini to swap sum order
2. Factors out metric component
3. Applies metric symmetry
4. Uses ring for scalar commutativity

**This proves the correct algebraic approach works in Lean 4**.

### Problem: Parallel Incorrect Attempt

The quartet decomposition (lines 7284-7880) was a **parallel strategy** that:
- Pursued a different decomposition approach
- Relied on false mathematical identity
- Has unsolved goals that **cannot** be closed
- Must be removed

### Resolution Path

1. **No new infrastructure needed** - everything exists
2. **Abandon quartet decomposition** (~600 lines of code)
3. **Complete Block C's integration** with Four-Block Strategy
4. **Focus on `expand_P_ab`** - the actual blocker for assembly

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: October 30, 2025
**Status**: Infrastructure audit complete - ready for cleanup and integration
**Next action**: Consult JP/Paul on removing quartet decomposition code

---

## Appendix: Lemma Reference Table

| Lemma Name | Line | Purpose | In @[simp]? | Usage |
|------------|------|---------|-------------|-------|
| `sumIdx_rename` | 2072 | Alpha-rename bound variable | Yes | Automatic |
| `sumIdx_congr` | 1708 | Pointwise → sum equality | No | `apply sumIdx_congr` |
| `sumIdx_swap` | 1627 | Fubini (swap sums) | Yes | Automatic or `rw` |
| `sumIdx_swap_args` | 1636 | Swap arguments | No | `rw [sumIdx_swap_args]` |
| `sumIdx_mul_sumIdx_swap` | 2402 | Fubini with factor | No | `rw [sumIdx_mul_sumIdx_swap]` |
| `sumIdx_swap_factors` | 2156 | Commutativity | No | `rw [sumIdx_swap_factors]` |
| `g_symm` | ~1393 | Metric symmetry | In library | `simp only [g_symm]` |
| `ring` | Built-in | Scalar algebra | Tactic | `ring` |

**Note**: Lemmas marked @[simp] are applied automatically by `simp` tactic. Others require explicit `rw` or `apply`.
