# UPDATED Comprehensive Diagnostic: All Issues + Cross-File Dependencies - October 25, 2025

**Agent**: Claude Code (Sonnet 4.5)
**Status**: ✅ Complete investigation including cross-file dependencies
**Total Sorries**: 26 in Riemann.lean
**Build Errors**: 2 (line 6069 pre-existing, line 6972 new critical issue)

---

## 🚨 CRITICAL FINDING: Riemann_swap_a_b is REQUIRED by Invariants.lean

**User was correct!** The `Riemann_swap_a_b` lemmas (lines 7304, 7316, 7322, 7323) are **NOT optional** - they are **heavily used** by Invariants.lean for the Kretschmann scalar computation.

### Cross-File Dependency Chain

```
Schwarzschild.lean (base infrastructure)
        ↓
Riemann.lean (proof of Ricci identity)
        ↓
Invariants.lean (Kretschmann & Ricci scalar computations)
```

### What Invariants.lean Needs from Riemann.lean

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Invariants.lean`

**Critical Dependency**: `Riemann_swap_a_b` (from Riemann.lean line 7316)

**Usage Count**: Used in **13 different locations** in Invariants.lean:
- Line 121: `Riemann_sq_swap_a_b` helper (calls `Riemann_swap_a_b`)
- Lines 131, 142, 153, 164, 175, 186: All 6 block-reduction lemmas use it
- Line 209: `Kretschmann_block_sq` (currently has sorry because Riemann_swap_a_b has sorry!)

**Blocking Issue in Invariants.lean**:
```lean
-- Line 201 in Invariants.lean
private lemma Kretschmann_block_sq
    (M r θ : ℝ) (a b : Idx) :
  ... = 4 * sixBlock M r θ a b := by
  sorry
  /-
  TODO: Complete once Riemann_swap_a_b is proven:
  classical
  unfold sixBlock
  have hw :
    (gInv M a a r θ)^2 * (gInv M b b r θ)^2
      = (gInv M a a r θ * gInv M b b r θ)^2 := by ring
  simp [hw, Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]
  ring
  -/
```

**Impact**: Without `Riemann_swap_a_b`, the Kretschmann scalar computation (curvature invariant) **cannot be completed**.

---

## REVISED Priority Classification

### Tier 1: CRITICAL (Blocks Everything) - 1 sorry

| Line | Lemma | Issue | Blocks |
|------|-------|-------|--------|
| 6972 | expand_P_ab | Sum restructuring needed | algebraic_identity, entire critical path |

### Tier 2: HIGH (Critical Path) - 2 sorries

| Line | Lemma | Issue | Blocks |
|------|-------|-------|--------|
| 7244 | algebraic_identity | Needs expand_P_ab | ricci_identity_on_g_general, Riemann_swap_a_b |
| 7304 | Riemann_swap_a_b_ext | Needs ricci_identity_on_g_rθ_ext | Riemann_swap_a_b, **Invariants.lean** |

### Tier 3: HIGH (Required by Invariants.lean) - 4 sorries

| Line | Lemma | Issue | Blocks |
|------|-------|-------|--------|
| 7316 | Riemann_swap_a_b | Needs Riemann_swap_a_b_ext | **Invariants.lean Kretschmann computation** |
| 7322 | Riemann_swap_a_b (r ≤ 2M case) | Edge case of Riemann_swap_a_b | **Invariants.lean completeness** |
| 7323 | Riemann_swap_a_b (M ≤ 0 case) | Edge case of Riemann_swap_a_b | **Invariants.lean completeness** |
| 7281 | ricci_identity_on_g_rθ_ext | Apply ricci_identity_on_g_general | Riemann_swap_a_b_ext |

### Tier 4: MEDIUM (Downstream) - 1 sorry

| Line | Lemma | Issue | Priority |
|------|-------|-------|----------|
| 7296 | ricci_identity_on_g | Times out (alternative approach) | 🟡 MEDIUM |

### Tier 5: LOW (Deprecated/Optional) - 12 sorries

| Line | Lemma | Reason | Action |
|------|-------|--------|--------|
| 2008 | dCoord_g_expand | Forward decl (proven at 3230) | Can remove |
| 2100, 2112 | flatten_comm_block_r | Deprecated flatten approach | Can remove |
| 2183, 2192 | flatten_comm_block_θ | Deprecated flatten approach | Can remove |
| 2484 | dCoord_g_via_compat_ext_temp | Forward decl (proven at 3230) | Can remove |
| 6117, 6123 | ricci_identity_on_g_rθ_ext (old) | Deprecated unbounded-simp approach | Can remove |
| 6147 | dCoord_g_differentiable_r_ext | C² lemma (not critical path) | Defer |
| 6158 | dCoord_g_differentiable_θ_ext | C² lemma (not critical path) | Defer |

### Tier 6: DEFERRED (Alternative Proof Paths) - 6 sorries

| Line | Lemma | Reason | Action |
|------|-------|--------|--------|
| 9911-9987 | Phase 2B/4 lemmas | Alternative Γ₁-based proof approach | Not needed |

---

## REVISED Critical Path to Project Completion

```
Step 1: Fix expand_P_ab line 6972 (sum restructuring)
           Estimated: 1-3 hours
           ↓
Step 2: Complete algebraic_identity (line 7244)
           Estimated: 30-60 minutes
           Uses: expand_P_ab (from step 1)
           ↓
Step 3: Complete ricci_identity_on_g_general
           Estimated: 15-30 minutes
           Uses: algebraic_identity (from step 2)
           ↓
Step 4: Complete ricci_identity_on_g_rθ_ext (line 7281)
           Estimated: 15 minutes
           Uses: ricci_identity_on_g_general (from step 3)
           ↓
Step 5: Complete Riemann_swap_a_b_ext (line 7304)
           Estimated: 1-2 hours
           Uses: ricci_identity_on_g_rθ_ext (from step 4)
           ↓
Step 6: Complete Riemann_swap_a_b (line 7316)
           Estimated: 30 minutes
           Uses: Riemann_swap_a_b_ext (from step 5)
           ↓
Step 7: Complete edge cases (lines 7322, 7323)
           Estimated: 1-2 hours
           ↓
───────────────────────────────────────────────
RESULT: Ricci identity PROVEN + Invariants.lean UNBLOCKED
        Kretschmann scalar computation can complete

TOTAL EFFORT: 5-10 hours
```

---

## Detailed Dependency Analysis

### What Invariants.lean Does

**Kretschmann Scalar**: `K := R_{abcd} R^{abcd}`

This is a curvature invariant that measures spacetime curvature strength. For Schwarzschild:
- Expected value: `K = 48M²/r⁶` (textbook result)
- Used to detect singularities and compare different spacetimes

**Computation Strategy**:
1. Compute all components of `Riemann M r θ a b c d`
2. Raise all indices using `gInv` (inverse metric)
3. Contract: `K = Σ_{abcd} R_{abcd} R^{abcd}`

**Simplification via Symmetries**:
- Due to Riemann tensor symmetries, K reduces to sum over 6 "blocks" (unordered pairs)
- Each block has 4 permutation terms that need to be collapsed
- **Collapse requires**: `Riemann_sq_swap_a_b` and `Riemann_sq_swap_c_d`

**Current Blocker**:
```lean
-- Invariants.lean line 201
private lemma Kretschmann_block_sq ... := by
  sorry
  /-
  TODO: Complete once Riemann_swap_a_b is proven
  -/
```

Without this lemma, the entire Kretschmann computation is **blocked**.

### Lemma Dependency Graph

```
expand_P_ab (6972) ✅ → NEEDS FIX
    ↓
algebraic_identity (7244)
    ↓
ricci_identity_on_g_general
    ↓
ricci_identity_on_g_rθ_ext (7281)
    ↓
Riemann_swap_a_b_ext (7304)
    ↓
Riemann_swap_a_b (7316) ← CRITICAL for Invariants.lean!
    ↓
Kretschmann_block_sq (Invariants.lean line 201)
    ↓
Kretschmann scalar computation
    ↓
Proof that K = 48M²/r⁶ for Schwarzschild
```

---

## Files That Import Riemann.lean

**Found 4 files**:

1. **Invariants.lean** ← USES Riemann_swap_a_b (CRITICAL DEPENDENCY!)
2. **Guardrails.lean** ← No usage of sorry lemmas
3. **RiemannStage1_LHS.lean** ← No usage of sorry lemmas
4. **TestSorryFixes.lean** ← Test file, not production

**Conclusion**: Only Invariants.lean has critical dependencies on Riemann.lean sorry lemmas.

---

## Updated Summary Table

| Category | Count | Blocks Invariants.lean? | Priority |
|----------|-------|-------------------------|----------|
| **Critical (expand_P_ab)** | 1 | YES (transitively) | 🔴 CRITICAL |
| **High (Ricci proof chain)** | 2 | YES (transitively) | 🟠 HIGH |
| **High (Riemann symmetries)** | 4 | **YES (directly!)** | 🟠 **HIGH** |
| **Medium (alternatives)** | 1 | NO | 🟡 MEDIUM |
| **Low (deprecated)** | 12 | NO | 🟢 LOW |
| **Deferred (alternative paths)** | 6 | NO | ⚪ DEFER |
| **TOTAL** | 26 | 7 critical for Invariants | - |

---

## Key Code Snippets from Invariants.lean

### Riemann_sq_swap_a_b Helper (Line 119-121)

```lean
private lemma Riemann_sq_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  (Riemann M r θ b a c d)^2 = (Riemann M r θ a b c d)^2 := by
  rw [Riemann_swap_a_b, sq_neg]  ← USES Riemann_swap_a_b from Riemann.lean!
```

### Example Block Reduction (Line 124-132)

```lean
private lemma Kretschmann_block_tr (M r θ : ℝ) :
  (gInv M Idx.t Idx.t r θ * gInv M Idx.r Idx.r r θ * ...)^2 * (Riemann M r θ Idx.t Idx.r Idx.t Idx.r)^2 +
  (gInv M Idx.t Idx.t r θ * gInv M Idx.r Idx.r r θ * ...)^2 * (Riemann M r θ Idx.t Idx.r Idx.r Idx.t)^2 +
  (gInv M Idx.r Idx.r r θ * gInv M Idx.t Idx.t r θ * ...)^2 * (Riemann M r θ Idx.r Idx.t Idx.t Idx.r)^2 +
  (gInv M Idx.r Idx.r r θ * gInv M Idx.t Idx.t r θ * ...)^2 * (Riemann M r θ Idx.r Idx.t Idx.r Idx.t)^2
  = 4 * sixBlock M r θ Idx.t Idx.r := by
  unfold sixBlock
  simp only [Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]  ← USES Riemann_sq_swap_a_b!
  ring
```

**All 6 blocks** (tr, tθ, tφ, rθ, rφ, θφ) use this pattern.

### Blocked Generic Lemma (Line 194-211)

```lean
private lemma Kretschmann_block_sq
    (M r θ : ℝ) (a b : Idx) :
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b a b)^2 +
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b b a)^2 +
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ b a a b)^2 +
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ b a b a)^2
  = 4 * sixBlock M r θ a b := by
  sorry  ← BLOCKED!
  /-
  TODO: Complete once Riemann_swap_a_b is proven:
  classical
  unfold sixBlock
  have hw :
    (gInv M a a r θ)^2 * (gInv M b b r θ)^2
      = (gInv M a a r θ * gInv M b b r θ)^2 := by ring
  simp [hw, Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]
  ring
  -/
```

**This is the generic version** that would allow all 6 specific block lemmas to be unified.

---

## What Schwarzschild.lean Provides (No Dependencies on Sorry Lemmas)

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Schwarzschild.lean`

**Role**: Base infrastructure (metric, Christoffel symbols, basic lemmas)

**Imports**: Only Mathlib and Interfaces (NOT Riemann.lean)

**Status**: **Self-contained** - no dependencies on Riemann.lean sorry lemmas

**Key Exports**:
- `g` (metric tensor)
- `gInv` (inverse metric)
- `Γtot` (Christoffel symbols)
- `sumIdx`, `sumIdx2` (sum helpers)
- `f M r` (Schwarzschild factor)
- Various differentiability and positivity lemmas

**Conclusion**: Schwarzschild.lean is complete and doesn't need any fixes in Riemann.lean.

---

## Recommendations for JP (UPDATED)

### Must-Do Priority Order

**Priority 1: Fix expand_P_ab (line 6972)**
- **Effort**: 1-3 hours
- **Blocks**: Everything else

**Priority 2: Complete algebraic_identity (line 7244)**
- **Effort**: 30-60 minutes
- **Dependency**: expand_P_ab (Priority 1)

**Priority 3: Complete ricci_identity_on_g_general**
- **Effort**: 15-30 minutes
- **Dependency**: algebraic_identity (Priority 2)

**Priority 4: Complete ricci_identity_on_g_rθ_ext (line 7281)**
- **Effort**: 15 minutes
- **Dependency**: ricci_identity_on_g_general (Priority 3)

**Priority 5: Complete Riemann_swap_a_b_ext (line 7304)**
- **Effort**: 1-2 hours
- **Dependency**: ricci_identity_on_g_rθ_ext (Priority 4)
- **Importance**: **Required for Invariants.lean**

**Priority 6: Complete Riemann_swap_a_b (line 7316)**
- **Effort**: 30 minutes
- **Dependency**: Riemann_swap_a_b_ext (Priority 5)
- **Importance**: **CRITICAL - Directly used by Invariants.lean**

**Priority 7: Complete edge cases (lines 7322, 7323)**
- **Effort**: 1-2 hours
- **Dependency**: Riemann_swap_a_b_ext (Priority 5)
- **Importance**: **Required for full Riemann_swap_a_b coverage**

### Optional Cleanup (Low Priority)

- Remove forward declarations (lines 2008, 2484)
- Remove deprecated flatten lemmas (lines 2100, 2112, 2183, 2192)
- Remove old ricci_identity approach (lines 6117, 6123)

---

## Bottom Line

**User was absolutely right!**

The Riemann_swap_a_b lemmas are **NOT optional**. They are:
1. **Required by Invariants.lean** for Kretschmann scalar computation
2. **Blocking 1 sorry in Invariants.lean** (line 201: Kretschmann_block_sq)
3. **Used 13 times across Invariants.lean** for block reduction lemmas

**Revised Effort Estimate**:
- **Minimum (just Ricci proof)**: 2-4 hours (Priorities 1-4)
- **Complete (including Invariants.lean)**: 5-10 hours (Priorities 1-7)

**Impact**: Completing Priorities 1-7 unlocks:
- ✅ Ricci identity proven without metric compatibility
- ✅ Kretschmann scalar computation completed
- ✅ Full curvature invariant analysis for Schwarzschild spacetime

---

**Diagnostic Status**: ✅ **COMPLETE WITH CROSS-FILE DEPENDENCIES**
**Date**: October 25, 2025
**Agent**: Claude Code (Sonnet 4.5)

---

*Thank you to the user for catching this! The Riemann_swap_a_b lemmas are critical for the broader project, not just the Ricci identity proof itself.*
