# Left Regrouping Progress - October 18 Evening
## Implementing Route A per JP's guidance

---

## ✅ Completed Steps

### 1. Added `sumIdx_collect6` helper (Lines 1625-1633)
Successfully created lemma to linearize 6 terms from nested form to flat form:
```lean
sumIdx (fun k => f₁ k - f₂ k + (f₃ k + f₄ k) - (f₅ k + f₆ k))
= (sumIdx f₁ - sumIdx f₂) + (sumIdx f₃ + sumIdx f₄) - (sumIdx f₅ + sumIdx f₆)
```

**Proof**: Simplified from complex approach to just `simp only [sumIdx_add_distrib, sumIdx_map_sub]` ✅

### 2. Linearized 6 terms with `split6` (Lines 4106-4163)
Successfully separated the nested sumIdx into 6 top-level sums:
- **f1, f2**: ∂Γ terms (derivatives)
- **f3, f5**: Diagonal Γ·Γ terms `Γ(k,...,b) * Σ_{k₁} Γ(k₁,...,a) * g(k₁,k)`
- **f4, f6**: Off-diagonal Γ·Γ terms `Γ(k,...,b) * Σ_{k₁} Γ(k₁,...,k) * g(a,k₁)`

**Key insight**: Needed `goal_shape` bridge lemma to handle syntactic matching between `+(-(...))`  and `- ...` forms.

**Status**: Compiles cleanly ✅

---

## ⚠️ Current Blocker: Diagonal Γ·Γ Conversion

### The Goal State (after split6):
```lean
(sumIdx f1 - sumIdx f2) + (sumIdx f3 + sumIdx f4) - (sumIdx f5 + sumIdx f6)
  = g M a a r θ * RiemannUp M r θ a b Idx.r Idx.θ
```

### The Challenge:
Need to convert all 4 Γ·Γ terms to "per-k form" (JP's terminology):
```lean
g M a k r θ * sumIdx (fun lam => Γtot M r θ k ... lam * Γtot M r θ lam ... b)
```

### Diagonal Terms (f3, f5) - BLOCKED:
**Current form**:
```lean
f3 k = Γtot M r θ k Idx.θ b * sumIdx (fun k₁ => Γtot M r θ k₁ Idx.r a * g M k₁ k r θ)
```

**Target form**:
```lean
g M a k r θ * sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ b)
```

**Mathematical intuition**:
- Inner sum `Σ_{k₁} Γ(k₁,r,a) * g(k₁,k)` should collapse via diagonal property to `Γ(k,r,a) * g(k,k)`
- Thus: `f3 k = Γ(k,θ,b) * Γ(k,r,a) * g(k,k)`
- But how do we get from this to `g(a,k) * Σ_lam Γ(k,r,lam) * Γ(lam,θ,b)`?
- The single term `Γ(k,r,a)` needs to become a sum `Σ_lam ...`

**Question**: Is this the right transformation? Or am I misunderstanding "per-k form"?

### Off-Diagonal Terms (f4, f6) - Should be Solvable:
**H₁ and H₂** (lines 4079-4102) are designed for these patterns:
- **H₁**: Converts `Γ(k,θ,b) * Σ_lam Γ(lam,r,k) * g(a,lam)` to per-k form
- **H₂**: Converts `Γ(k,r,b) * Σ_lam Γ(lam,θ,k) * g(a,lam)` to per-k form

**Problem**: Can't apply H₁/H₂ yet because the diagonal terms need to be handled first (they're lumped together in the goal).

---

## 🔧 Attempts Made

### Attempt 1: Pointwise Proof with `sumIdx_congr`
```lean
apply sumIdx_congr
intro k
simp only [f3]
-- Swap g(k₁,k) to g(k,k₁) via g_symm
conv_lhs => arg 2; arg 1; ext k₁; rw [g_symm M r θ k₁ k]
-- Expand and collapse
simp only [sumIdx_expand]
simp only [g, sumIdx_mul_g_left]  -- or sumIdx_mul_g_right
ring
```

**Result**: Unsolved goals after `simp only [g, sumIdx_mul_g_right]`
- The contraction lemmas expect specific index patterns
- After collapse, get `Γ(k,r,a) * g(k,k)`, not a sum over lam

### Attempt 2: Top-Level Symmetry Approach
```lean
-- Use g_symm to swap indices, then reassociate
conv_lhs => arg 2; arg 1; ext k₁; rw [g_symm M r θ k₁ k]
simp only [sumIdx_expand, g, sumIdx_mul_g_left]
rw [g_symm M r θ k a]
```

**Result**: Still stuck on how to introduce the `Σ_lam` on RHS

### Attempt 3: Consider Using Identify Lemmas (Route B)
The `Riemann_via_Γ₁_Identify_r` and `_θ` lemmas (lines 1779-1830) exist and transform:
```lean
sumIdx (fun ρ => sumIdx (fun σ => Γ(σ,r,β) * g(σ,ρ)) * Γ(ρ,θ,a))
  = sumIdx (fun lam => Γ₁(lam,a,θ) * Γ(lam,β,r))
```

**Problem**: Our f3/f5 have different index structure - would need Fubini swap and relabeling first.

**JP's note**: Route B (Γ₁ route) is "more steps" than Route A. But maybe simpler for diagonal terms?

---

## ❓ Questions for JP

### 1. Diagonal Conversion Strategy
**What's the exact transformation for diagonal terms?**

Given `Γ(k,θ,b) * Σ_{k₁} Γ(k₁,r,a) * g(k₁,k)`, how do we get to:
```lean
g M a k r θ * sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ b)
```

Options I see:
- **A**: Use a Kronecker delta trick to expand `Γ(k,r,a)` into `Σ_lam δ_{a,lam} * Γ(k,r,lam)`?
- **B**: The transformation is different - maybe the diagonal terms stay as-is and get collected differently?
- **C**: Use Fubini in a way I haven't understood yet?
- **D**: Just use the Identify lemmas (Route B) for diagonal terms?

### 2. Contraction Lemma Application
**Which contraction lemma for which term?**

For `Σ_{k₁} Γ(k₁,r,a) * g(k₁,k)`:
- Tried `sumIdx_mul_g_right` (contracts on first index: `Σ_k F(k) * g(k,b) = F(b) * g(b,b)`)
- Result: `Γ(k,r,a) * g(k,k)` ✓
- But then what? How to get `g(a,k) * ...` from this?

### 3. Tactical Sequence
**Can you provide the exact tactic sequence for f3_eq proof?**

Starting from:
```lean
have f3_eq : sumIdx f3 = sumIdx (fun k =>
    g M a k r θ * sumIdx (fun lam =>
      Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ b)) := by
  classical
  -- YOUR TACTICAL SEQUENCE HERE
```

What comes next?

### 4. Route Recommendation
**Should I switch to Route B for diagonal terms?**

Given the difficulties with Route A for f3/f5, would it be simpler to:
- Use Route A (direct per-k) for f4/f6 (off-diagonal) via H₁/H₂
- Use Route B (Identify lemmas) for f3/f5 (diagonal)
- Then proceed with Step 5 (collect and recognize kernel)?

---

## 📊 Current Status

**File**: `Riemann.lean`
**Build**: Clean ✅ (0 errors, 12 sorries - unchanged from start)
**Lines Modified**: 1625-1633 (sumIdx_collect6), 4036-4188 (main lemma)

**Sorry Location**: Line 4188 (after linearization, at Step 3/4 blocker)

**Completed**:
- ✅ sumIdx_collect6 helper
- ✅ Linearization with split6
- ✅ H₁ and H₂ definitions (lines 4079-4102)

**Blocked**:
- ⚠️ Diagonal Γ·Γ conversion (f3, f5)
- ⏸️ Off-diagonal conversion (f4, f6) - waiting for diagonal resolution
- ⏸️ Step 5 (collect 4 k-sums and recognize kernel)

---

## 🔄 Next Steps (Awaiting Guidance)

1. **Resolve diagonal blocker** - need tactical sequence or route clarification
2. **Apply transformations to f3, f4, f5, f6**
3. **Collect 4 k-sums** (JP's Step 5A.3)
4. **Recognize RiemannUp kernel pointwise**
5. **Final contraction with Riemann_contract_first**

---

**Prepared by**: Claude Code
**Date**: October 18, 2025 (Evening)
**Session**: Continuation from morning blocker, implementing Route A per JP's guidance
**Key Reference**: JP's detailed Route A vs Route B explanation from latest message

---

## Appendix: Definitions for Reference

### f3 and f5 (Diagonal Terms)
```lean
let f3 : Idx → ℝ := fun k => Γtot M r θ k Idx.θ b * sumIdx (fun k₁ =>
                      Γtot M r θ k₁ Idx.r a * g M k₁ k r θ)

let f5 : Idx → ℝ := fun k => Γtot M r θ k Idx.r b * sumIdx (fun k₁ =>
                      Γtot M r θ k₁ Idx.θ a * g M k₁ k r θ)
```

### f4 and f6 (Off-Diagonal Terms - H₁/H₂ Should Handle)
```lean
let f4 : Idx → ℝ := fun k => Γtot M r θ k Idx.θ b * sumIdx (fun k₁ =>
                      Γtot M r θ k₁ Idx.r k * g M a k₁ r θ)

let f6 : Idx → ℝ := fun k => Γtot M r θ k Idx.r b * sumIdx (fun k₁ =>
                      Γtot M r θ k₁ Idx.θ k * g M a k₁ r θ)
```

### Target Per-K Form (All 4 Terms)
```lean
g M a k r θ * sumIdx (fun lam => Γtot M r θ k (dir1) lam * Γtot M r θ lam (dir2) b)
```
where `dir1` and `dir2` vary depending on which term.

### Available Lemmas
- **sumIdx_mul_g_left**: `Σ_k g(a,k) * F(k) = g(a,a) * F(a)`
- **sumIdx_mul_g_right**: `Σ_k F(k) * g(k,b) = F(b) * g(b,b)`
- **g_symm**: `g(i,j) = g(j,i)`
- **Γtot_symm**: `Γ(i,d,j) = Γ(j,d,i)`
- **sumIdx_expand**: Expands sum to explicit 4-term form
- **sumIdx_swap**: Fubini for nested sums

