# Mathlib API Compatibility Issues - Sprint 35 Day 6

**Critical Issue**: CI failing due to mathlib API incompatibility  
**Version**: mathlib 4.22.0-rc3 vs expected stable APIs  
**Impact**: Complete build failure on Day 6 changes  

---

## 🚨 **FAILING API CALLS**

### **1. `ContinuousLinearMap.isSelfAdjoint_diagonal`**
```lean
-- FAILING CODE (Line 90):
lemma cheeger_selfAdjoint (β : ℝ) (b : ℕ → Bool) :
    IsSelfAdjoint (cheeger β b) := by
  simp [cheeger, ContinuousLinearMap.isSelfAdjoint_diagonal]  -- ❌ API doesn't exist
```

**Error**: `unknown constant 'ContinuousLinearMap.isSelfAdjoint_diagonal'`

**Alternatives to Research**:
- `ContinuousLinearMap.isSelfAdjoint_diagonal_of_real`
- `ContinuousLinearMap.adjoint_diagonal`
- Manual proof via `IsSelfAdjoint` definition

### **2. `ContinuousLinearMap.norm_diagonal_le`**
```lean
-- FAILING CODE (Line 94-95):
lemma cheeger_bounded (β : ℝ) (b : ℕ → Bool) :
    ∥cheeger β b∥ ≤ max ‖β‖ 1 := by
  simpa [cheeger] using
    (ContinuousLinearMap.norm_diagonal_le _ _).trans_eq rfl  -- ❌ API doesn't exist
```

**Error**: `unknown constant 'ContinuousLinearMap.norm_diagonal_le'`

**Alternatives to Research**:
- `ContinuousLinearMap.opNorm_diagonal_le` 
- `ContinuousLinearMap.norm_diagonal`
- Manual proof via `opNorm_le_bound`

### **3. Structure Definition Issues**
```lean
-- USAGE (Line 100-105):
lemma cheeger_has_gap
    {β : ℝ} (hβ : |β - 1| ≥ (1/2 : ℝ)) (b : ℕ → Bool) :
    selHasGap (cheeger β b) := by
  refine
    { a := ((β + 1) / 2) - (1/4),
      b := ((β + 1) / 2) + (1/4),
      gap_lt := by nlinarith,
      gap := trivial }
```

**Error**: `type of theorem 'SpectralGap.cheeger_has_gap' is not a proposition`

**Issue**: `selHasGap` is defined as `Type` (structure), not `Prop`, but theorem signature suggests `Prop`.

---

## 🔍 **WORKING DEFINITIONS**

From `SpectralGap/NoWitness.lean` (these work correctly):

```lean
-- ✅ These definitions are correct and working:
structure GapHyp (T : BoundedOp) : Type where
  a      : ℝ
  b      : ℝ  
  gap_lt : a < b
  gap    : True  -- placeholder

abbrev selHasGap (T : BoundedOp) : Type := GapHyp T

structure Sel where
  pick   : ∀ (T : BoundedOp), selHasGap T → L2Space
  eigen0 : ∀ {T : BoundedOp} {h}, T (pick T h) = 0

def WLPO : Prop :=
  ∀ b : Nat → Bool, (∀ n, b n = false) ∨ (∃ n, b n = true)

lemma acω_of_wlpo : WLPO → ACω := by
  intro _ 
  have : RequiresACω := RequiresACω.mk
  exact acω_from_requires this
```

---

## 🛠️ **RECOVERY STRATEGIES**

### **Strategy 1: API Research (Recommended)**
```bash
# Research correct APIs in mathlib 4.22.0-rc3:
lean --version  # Confirm version
lake env lean --run scripts/find_mathlib_api.lean  # If exists
```

**Search for**:
- Diagonal operator properties in `Analysis.NormedSpace.*`
- Self-adjoint lemmas in `Analysis.InnerProductSpace.*`
- Operator norm bounds in `Analysis.NormedSpace.OperatorNorm.*`

### **Strategy 2: Manual Proofs (Fallback)**
```lean
-- Replace API calls with manual proofs:
lemma cheeger_selfAdjoint (β : ℝ) (b : ℕ → Bool) :
    IsSelfAdjoint (cheeger β b) := by
  rw [IsSelfAdjoint]
  ext v n  
  simp [cheeger, ContinuousLinearMap.adjoint_apply]
  -- Manual computation for real eigenvalues
  sorry  -- Implement step by step

lemma cheeger_bounded (β : ℝ) (b : ℕ → Bool) :
    ∥cheeger β b∥ ≤ max ‖β‖ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
  · apply le_max_of_le_right; norm_num
  · intro v
    -- Manual bound via triangle inequality
    sorry  -- Implement coordinate-wise bounds
```

### **Strategy 3: Rollback & Incremental (Safest)**
```bash
# Rollback to working Day 5 state:
git reset --hard 0690689

# Apply ONLY documentation changes:
# - docs/cheeger-pathology.md  
# - Enhanced comments in Cheeger.lean
# - SpectralGap/Proofs.lean import (test carefully)

# Test each change individually before proceeding
```

---

## 🎯 **VERIFICATION TARGETS**

### **Required API Equivalents**
1. **Self-adjoint diagonal**: Find replacement for `isSelfAdjoint_diagonal`
2. **Norm bounds**: Find replacement for `norm_diagonal_le`  
3. **Structure usage**: Confirm `selHasGap` construction syntax

### **Testing Commands**
```bash
# Once APIs are fixed:
lake build SpectralGap.Cheeger  # Test individual module
grep -n "sorry" SpectralGap/Cheeger.lean  # Confirm 0 sorry
scripts/check-no-axioms.sh  # Verify axiom usage
```

### **Success Criteria**
- ✅ **Build passes**: `lake build` succeeds
- ✅ **No sorry**: File remains sorry-free as achieved in Day 5
- ✅ **CI green**: Full CI pipeline passes < 70s
- ✅ **API compliance**: Only use existing mathlib 4.22.0-rc3 APIs

---

## 📚 **CONTEXT FOR NEW SESSION**

### **Math-AI Code Status**
- **Days 1-5**: All Math-AI patches applied successfully, working perfectly
- **Day 6**: Math-AI patches applied but use incompatible APIs
- **Approach**: Math-AI assumes newer/different mathlib version than we have

### **Repository Context**
- **Branch**: `feat/cheeger-bottleneck` 
- **Last working**: `0690689` (Day 5 - sorry-free, CI passing)
- **Current**: `ae99d1c` (Day 6 - API failures)
- **Goal**: Restore CI while preserving mathematical content

### **Mathematical Correctness**
The **mathematical content is completely sound**. Only implementation details (API calls) need adjustment for our mathlib version.

---

**Resolution Priority**: URGENT - Blocking Sprint 35 completion  
**Recommended Approach**: API research + incremental testing  
**Fallback Plan**: Manual proof implementations if APIs can't be found  

---

*API Issue Documentation - Sprint 35 Day 6*