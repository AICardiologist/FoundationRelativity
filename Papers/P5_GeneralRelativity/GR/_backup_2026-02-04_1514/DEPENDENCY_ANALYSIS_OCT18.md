# Dependency Analysis: GR Module Structure
## Date: October 18, 2025
## Purpose: Understand dependencies before Phase 2B modularization

---

## Executive Summary

This analysis maps the import and definition dependencies across the four main files in the GR module:
- **Interfaces.lean** (1.8 KB) - Abstract type definitions
- **Schwarzschild.lean** (99.8 KB) - Core metric and Christoffel infrastructure
- **Riemann.lean** (314.4 KB) - Riemann tensor derivation and proofs
- **Invariants.lean** (21.5 KB) - Ricci and Kretschmann scalars

**Key Finding**: The files form a clean linear dependency chain with one critical issue:
- Interfaces ← Schwarzschild ← Riemann ← Invariants ✅ (linear chain)
- BUT: Riemann defines `dCoord` (line 270) which is needed by compatibility infrastructure (lines 2040-2477) which is used by main proof (line 1871) ⚠️ **Forward reference problem**

---

## Import Structure

### 1. Interfaces.lean (Base Layer - No imports)

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Interfaces.lean`

**Imports**: NONE (base layer)

**Key Exports**:
```lean
structure Manifold
structure LorentzMetric (M : Manifold)
structure Spacetime
structure TensorField (S : Spacetime)
def ChristoffelSymbols (_S : Spacetime) : Type := Prop
def RiemannTensor (_S : Spacetime) : TensorField _S
def RicciTensor (_S : Spacetime) : TensorField _S
def RicciScalar (_S : Spacetime)
def EinsteinTensor (_S : Spacetime) : TensorField _S
def StressEnergyTensor (_S : Spacetime) : TensorField _S
def IsPinnedSchwarzschild (_S : Spacetime) : Prop
def VacuumEFE (_S : Spacetime) : Prop
def IsMinkowski (_S : Spacetime) : Prop
```

**Purpose**: Abstract schematic definitions (placeholders for formal GR structures)

**Role in dependency**: Base layer - no dependencies

---

### 2. Schwarzschild.lean (Core Infrastructure Layer)

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Schwarzschild.lean`

**Imports**:
```lean
import Papers.P5_GeneralRelativity.GR.Interfaces
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Pow
```

**Key Exports (Core Types)**:
```lean
-- Line ~50: Index type
inductive Idx | t | r | θ | φ

-- Line ~42: Schwarzschild factor
noncomputable def f (M r : ℝ) : ℝ := 1 - 2*M/r

-- Line 1005: Metric tensor (diagonal components)
@[simp] noncomputable def g (M : ℝ) : Idx → Idx → ℝ → ℝ → ℝ
  | Idx.t, Idx.t, r, _θ => -f M r
  | Idx.r, Idx.r, r, _θ => (f M r)⁻¹
  | Idx.θ, Idx.θ, r, _θ => r^2
  | Idx.φ, Idx.φ, r, θ  => r^2 * (Real.sin θ)^2
  | _, _, _, _ => 0

-- Line 1352: Index summation
@[inline] def sumIdx {α} [AddCommMonoid α] (f : Idx → α) : α := ∑ i : Idx, f i
@[inline] def sumIdx2 {α} [AddCommMonoid α] (f : Idx → Idx → α) : α

-- Line ~1477: NonzeroChristoffel predicate (13 non-zero combinations)
inductive NonzeroChristoffel : Idx → Idx → Idx → Prop where
  | Γ_t_tr : NonzeroChristoffel Idx.t Idx.t Idx.r
  | Γ_r_tt : NonzeroChristoffel Idx.r Idx.t Idx.t
  | Γ_r_rr : NonzeroChristoffel Idx.r Idx.r Idx.r
  | Γ_r_θθ : NonzeroChristoffel Idx.r Idx.θ Idx.θ
  | Γ_r_φφ : NonzeroChristoffel Idx.r Idx.φ Idx.φ
  | Γ_θ_rθ : NonzeroChristoffel Idx.θ Idx.r Idx.θ
  | Γ_θ_φφ : NonzeroChristoffel Idx.θ Idx.φ Idx.φ
  | Γ_φ_rφ : NonzeroChristoffel Idx.φ Idx.r Idx.φ
  | Γ_φ_θφ : NonzeroChristoffel Idx.φ Idx.θ Idx.φ

-- Line ~1500: Total Christoffel symbols
noncomputable def Γtot (M r θ : ℝ) : Idx → Idx → Idx → ℝ

-- Derivative lemmas for individual Γ components (many)
```

**Purpose**: Concrete Schwarzschild metric implementation with Christoffel symbols

**Depends on**: Interfaces (for namespace only - no actual dependency on definitions)

**Used by**: Riemann, Invariants

---

### 3. Riemann.lean (Main Computational Layer)

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`

**Imports**:
```lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
```

**Key Exports (Ordered by definition line)**:
```lean
-- Line 27: Exterior domain
structure Exterior (M r θ : ℝ) : Prop where
  hM : 0 < M
  hr_ex : 2 * M < r

-- Line 270: Coordinate derivative (CRITICAL - needed by compatibility)
@[simp] noncomputable def dCoord (μ : Idx) (F : ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ :=
  match μ with
  | Idx.r => deriv (fun s => F s θ) r
  | Idx.θ => deriv (fun t => F r t) θ
  | _     => 0

-- Line 396: Directional differentiability wrappers
def DifferentiableAt_r (f : ℝ → ℝ → ℝ) (r θ : ℝ) : Prop
def DifferentiableAt_θ (f : ℝ → ℝ → ℝ) (r θ : ℝ) : Prop

-- Line 492: Master Lemmas for g (Phase 2A)
lemma differentiableAt_g_all_r
lemma differentiableAt_g_all_θ

-- Line 792: Zero Lemma for Γtot (Phase 2A)
lemma Γtot_eq_zero_of_not_nonzero

-- Line 807: Master Lemmas for Γtot (Phase 2A)
lemma differentiableAt_Γtot_all_r
lemma differentiableAt_Γtot_all_θ

-- Line 1144: Inverse metric
def gInv (M : ℝ) (μ ν : Idx) (r θ : ℝ) : ℝ

-- Line 1440-1449: Preliminary Riemann definitions (with lowered indices)
noncomputable def RiemannUp  -- line 1440
noncomputable def Riemann    -- line 1449

-- Line 1573: Γ₁ (second Christoffel derivative term)
noncomputable def Γ₁ (M r θ : ℝ) (β a μ : Idx) : ℝ

-- Line 1781: ⚠️ TEMPORARY AXIOM (Phase 2B target)
axiom dCoord_g_via_compat_ext_temp (M r θ : ℝ) (h_ext : Exterior M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ)

-- Line 1800-1935: ✅ MAIN PROOF (Phase 3 - 100% complete)
lemma Riemann_via_Γ₁ (M r θ : ℝ) (h_ext : Exterior M r θ)
    (h_θ : ∀ (ρ a : Idx), DifferentiableAt_θ (fun r θ => Γtot M r θ ρ a .r) r θ)
    (a b c d : Idx) :
    Riemann M r θ a b c d = ... (100% proven)

-- Line 2033: Covariant derivative operator
noncomputable def nabla (T : ℝ → ℝ → ℝ → Idx → Idx → ℝ)

-- Line 2040: Covariant derivative of metric (∇g)
noncomputable def nabla_g (M r θ : ℝ) (c a b : Idx) : ℝ :=
  dCoord c (fun r θ => g M a b r θ) r θ
  - sumIdx (fun e => Γtot M r θ e c a * g M e b r θ)
  - sumIdx (fun e => Γtot M r θ e c b * g M a e r θ)

-- Lines 2050-2476: Compatibility infrastructure (9+ helper lemmas)
lemma compat_r_tt_ext
lemma compat_r_rr_ext
lemma compat_r_θθ_ext
lemma compat_r_φφ_ext
lemma compat_θ_φφ_ext
lemma compat_t_tr_ext
lemma compat_θ_rθ_ext
lemma compat_φ_rφ_ext
lemma compat_φ_θφ_ext
-- ... (many more helper lemmas)

-- Line 2477: ✅ ACTUAL PROOF (Phase 2B target - fully proven, 0 sorries)
lemma dCoord_g_via_compat_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ) := by
  classical
  cases x <;> cases a <;> cases b
  all_goals {
    first
    | exact compat_r_tt_ext M r θ h_ext
    | exact compat_r_rr_ext M r θ h_ext
    | ... (9 specific cases)
    | { -- automated fallback for trivial cases
        ... (full proof, no sorries)
      }
  }

-- Lines 2737-2768: Alternative Riemann formulations
def ContractionC
def RiemannUp  -- (redefinition)
def Riemann    -- (redefinition)

-- Lines 3000+: Many auxiliary lemmas for Ricci identity, symmetries, etc.

-- Line 5972: Ricci tensor contraction
noncomputable def RicciContraction (M r θ : ℝ) (a b : Idx) : ℝ
```

**Purpose**: Riemann tensor computation, main proofs, compatibility infrastructure

**Depends on**: Schwarzschild (for Idx, g, Γtot, sumIdx, f, NonzeroChristoffel)

**Used by**: Invariants

**Critical Issue**:
- `dCoord` defined at line 270
- Used in `nabla_g` at line 2040
- `nabla_g` used by compatibility helpers (lines 2050-2476)
- Compatibility proof `dCoord_g_via_compat_ext` at line 2477
- But temporary axiom `dCoord_g_via_compat_ext_temp` at line 1781
- Axiom used by main proof `Riemann_via_Γ₁` at line 1871
- **Gap**: 600 lines between usage (1871) and proof (2477)

---

### 4. Invariants.lean (Application Layer)

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Invariants.lean`

**Imports**:
```lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild
import Papers.P5_GeneralRelativity.GR.Riemann
```

**Key Exports**:
```lean
-- Line 13: Ricci scalar definition
noncomputable def RicciScalar (M r θ : ℝ) : ℝ :=
  sumIdx2 (fun μ ν => gInv M μ ν r θ * Ricci M r θ μ ν)

-- Line 19: Ricci scalar vanishing theorem
theorem RicciScalar_exterior_zero (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r)
    (hθ : 0 < θ ∧ θ < Real.pi) : RicciScalar M r θ = 0

-- Line 33: Kretschmann scalar definition
noncomputable def Kretschmann (M r θ : ℝ) : ℝ

-- Line 442: Kretschmann scalar value theorem
theorem Kretschmann_exterior_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r)
    (hθ : 0 < θ ∧ θ < Real.pi) : Kretschmann M r θ = 48 * M^2 / r^6
```

**Purpose**: Compute and verify curvature invariants (Ricci, Kretschmann scalars)

**Depends on**: Schwarzschild (for sumIdx2, gInv), Riemann (for Ricci, Riemann definitions)

**Used by**: None (top of dependency chain)

---

## Dependency Graph (Visual)

```
┌─────────────────┐
│ Interfaces.lean │ (Abstract GR structures - 1.8 KB)
│  - Manifold     │
│  - Spacetime    │
│  - TensorField  │
└────────┬────────┘
         │
         │ import
         ▼
┌──────────────────────┐
│ Schwarzschild.lean   │ (Core infrastructure - 99.8 KB)
│  - Idx (t,r,θ,φ)     │
│  - f(M,r)            │
│  - g (metric)        │
│  - Γtot (Christoffel)│
│  - sumIdx, sumIdx2   │
│  - NonzeroChristoffel│
└────────┬─────────────┘
         │
         │ import
         ▼
┌─────────────────────────────────┐
│ Riemann.lean                    │ (Main computation - 314.4 KB)
│  - Exterior                     │
│  - dCoord ⚠️ (line 270)         │
│  - DifferentiableAt_r/_θ        │
│  - Master Lemmas (Phase 2A)     │
│  - Riemann_via_Γ₁ ✅ (Phase 3)  │
│  - nabla_g (line 2040)          │
│  - Compatibility (2050-2477)    │
│    ⚠️ FORWARD REF ISSUE:        │
│    - Axiom at 1781              │
│    - Used at 1871               │
│    - Proof at 2477              │
│  - gInv                         │
│  - RiemannUp, Riemann           │
│  - RicciContraction             │
└────────┬────────────────────────┘
         │
         │ import
         ▼
┌──────────────────────┐
│ Invariants.lean      │ (Applications - 21.5 KB)
│  - RicciScalar       │
│  - Kretschmann       │
│  - Theorems (R=0,    │
│    K=48M²/r⁶)        │
└──────────────────────┘
```

---

## Critical Dependencies for Phase 2B

### Problem: Forward Reference in Riemann.lean

**The Issue**:
```
Line 270:  dCoord definition ✅
Line 1781: axiom dCoord_g_via_compat_ext_temp ⚠️
Line 1871: Main proof uses axiom ⚠️
Line 2040: nabla_g definition (uses dCoord) ✅
Lines 2050-2476: Compatibility helper lemmas ✅
Line 2477: dCoord_g_via_compat_ext actual proof ✅
```

**Dependency Chain**:
```
dCoord (270)
  └─> nabla_g (2040)
       └─> compat_r_tt_ext, compat_r_rr_ext, ... (2050-2476)
            └─> dCoord_g_via_compat_ext (2477) ✅ PROVEN
                 └─> [needed by] Riemann_via_Γ₁ (1871) ⚠️
```

**Problem**:
- Main proof at line 1871 needs `dCoord_g_via_compat_ext`
- Actual proof is at line 2477 (600 lines later)
- Currently using temporary axiom at line 1781 as workaround

---

## Modularization Strategy Options

### Option 1: Move Compatibility Earlier (Simple Reordering)

**Approach**: Move lines 2040-2477 before line 1781

**Files to move**:
1. `nabla_g` definition (line 2040)
2. All 9+ compatibility helper lemmas (lines 2050-2476)
3. `dCoord_g_via_compat_ext` proof (line 2477)

**Dependencies to check**:
- nabla_g: needs dCoord ✅ (already at line 270)
- compat helpers: need g, Γtot, Exterior ✅ (all defined earlier)
- May need some derivative lemmas moved earlier

**Pros**:
✅ Stays within Riemann.lean
✅ No new module files
✅ Minimal changes

**Cons**:
❌ May disrupt logical flow
❌ Need to check if helper lemmas have dependencies on later code
❌ Estimated 2-3 hours + debugging

---

### Option 2: Extract to Compatibility.lean Module (Failed Attempt)

**Approach**: Create new `Compatibility.lean` module with compatibility infrastructure

**What we learned from first attempt**:
❌ Type inference issues with Idx notation in new module
❌ Circular dependency risk (Riemann needs Compatibility, Compatibility needs dCoord from Riemann)
❌ Many scattered dependencies hard to track

**Status**: REVERTED - not recommended without better dependency understanding

---

### Option 3: Extract to Multiple Focused Modules (Recommended)

**Approach**: Break Riemann.lean into logical modules based on dependency analysis

**Proposed structure**:
```lean
-- CoordinateDerivatives.lean (NEW)
import Schwarzschild
- dCoord definition
- DifferentiableAt_r, DifferentiableAt_θ wrappers
- Basic derivative lemmas
- Master Lemmas (Phase 2A)

-- MetricCompatibility.lean (NEW)
import Schwarzschild
import CoordinateDerivatives
- nabla_g definition
- All compat_* helper lemmas
- dCoord_g_via_compat_ext proof

-- Riemann.lean (REDUCED)
import Schwarzschild
import CoordinateDerivatives
import MetricCompatibility
- Exterior structure
- gInv definition
- Γ₁ definition
- RiemannUp, Riemann definitions
- Riemann_via_Γ₁ main proof ← uses MetricCompatibility
- Auxiliary lemmas
- RicciContraction
```

**Dependency order**:
```
Schwarzschild
  ├─> CoordinateDerivatives
  │     └─> MetricCompatibility
  │           └─> Riemann (reduced)
  └─> Riemann (reduced)
```

**Pros**:
✅ Clean logical separation
✅ No circular dependencies
✅ Each module has clear purpose
✅ Easier to maintain

**Cons**:
❌ More complex initial setup
❌ Need to carefully track dependencies
❌ Estimated 4-6 hours + debugging

---

### Option 4: Hybrid Approach (Recommended for Phase 2B)

**Approach**: Minimal extraction + reordering

**Phase 2B.1 (Immediate - 1 hour)**:
1. Move compatibility infrastructure earlier in Riemann.lean
   - Move nabla_g (line 2040) → before line 1781
   - Move compat helpers (2050-2476) → before line 1781
   - Move dCoord_g_via_compat_ext (2477) → before line 1781
2. Remove temporary axiom at line 1781
3. Test build

**Phase 2B.2 (Future cleanup - optional)**:
1. Extract CoordinateDerivatives module (dCoord + Phase 2A Master Lemmas)
2. Extract MetricCompatibility module (nabla_g + compat helpers)
3. Reduce Riemann.lean to main computational logic

**Pros**:
✅ Quick win for Phase 2B (remove axiom)
✅ Defers complex modularization to later
✅ Low risk of breakage
✅ Can do cleanup incrementally

**Cons**:
⚠️ Temporary solution (file still large)
⚠️ Logical flow may be slightly disrupted

---

## Dependency Analysis: What Needs What

### From Schwarzschild.lean (widely used):
- **Idx** (inductive type): Used everywhere for indices
- **f** (Schwarzschild factor): Used by g, gInv, derivatives
- **g** (metric): Used by Riemann proofs, compatibility, invariants
- **Γtot** (Christoffel): Used by Riemann computation, compatibility
- **sumIdx, sumIdx2**: Used for index contractions everywhere
- **NonzeroChristoffel**: Used by Phase 2A Master Lemmas

### From Riemann.lean (internal + exports):
- **dCoord** (line 270): ⚠️ CRITICAL - used by compatibility, needed early
- **Exterior**: Used throughout as hypothesis
- **DifferentiableAt_r/_θ**: Used by Phase 2A, product rules
- **gInv**: Used by Riemann computation, Invariants
- **Riemann, RiemannUp**: Used by Invariants for Kretschmann
- **RicciContraction**: Used by Invariants for Ricci scalar
- **nabla_g**: Internal use only (compatibility infrastructure)
- **Compatibility lemmas**: Used only by Riemann_via_Γ₁ proof

### From Invariants.lean (top layer):
- **RicciScalar, Kretschmann**: Final curvature invariants (not used by lower layers)

---

## Recommendations for Phase 2B

### Immediate Action (1-2 hours):

**Option 4 - Hybrid Approach (Phase 2B.1)**:

1. **Backup current state**:
   ```bash
   git add -A
   git commit -m "chore: backup before Phase 2B modularization"
   ```

2. **Move compatibility infrastructure earlier** in Riemann.lean:
   - Identify exact lines for nabla_g, compat helpers, dCoord_g_via_compat_ext
   - Move to before line 1781 (before axiom)
   - Check dependencies (should be minimal since dCoord already at line 270)

3. **Remove temporary axiom**:
   - Delete line 1781 axiom definition
   - Change line 1871 to use `dCoord_g_via_compat_ext` (remove `_temp`)

4. **Test build**:
   ```bash
   lake build Papers.P5_GeneralRelativity.GR.Riemann
   ```

5. **Commit if successful**:
   ```bash
   git add -A
   git commit -m "feat: complete Phase 2B - remove temporary axiom via reordering"
   ```

### Future Cleanup (Optional - Phase 2B.2):

If file organization becomes problematic, consider Option 3 (modular extraction) later.

---

## Appendix: File Statistics

| File | Size | Lines | Key Definitions | Imports | Used By |
|------|------|-------|----------------|---------|---------|
| Interfaces.lean | 1.8 KB | ~65 | 10+ structures/defs | 0 (base) | Schwarzschild |
| Schwarzschild.lean | 99.8 KB | ~2800 | Idx, f, g, Γtot, sumIdx, etc. | Interfaces + Mathlib | Riemann, Invariants |
| Riemann.lean | 314.4 KB | ~6900 | dCoord, Exterior, Riemann, gInv, etc. | Schwarzschild + Mathlib | Invariants |
| Invariants.lean | 21.5 KB | ~460 | RicciScalar, Kretschmann | Schwarzschild, Riemann | None (top layer) |

**Total**: ~10,225 lines of code across 4 files

---

## Questions for Senior Professor (if needed)

1. **Q1**: Do you recommend Option 4 (Hybrid - move earlier) or Option 3 (full modularization)?

2. **Q2**: Are there any hidden dependencies in the compatibility helpers (lines 2050-2476) that would prevent moving them earlier?

3. **Q3**: Should we extract CoordinateDerivatives.lean as a separate module eventually, or keep everything in Riemann.lean?

4. **Q4**: File organization philosophy - prefer smaller focused modules or larger comprehensive files?

---

**Prepared by**: Research Team (Claude Code)
**Date**: October 18, 2025
**Status**: Analysis complete, awaiting decision on modularization approach
**Next step**: Execute Option 4 (Hybrid approach) unless advised otherwise
