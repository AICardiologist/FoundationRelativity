# Paper 1 Lean Files Dependency Chart - RankOneToggle Track Only

**Generated**: August 22, 2025 (Updated after reorganization)  
**Purpose**: Dependency analysis of RankOneToggle track - the core of Paper 1's proof

## Executive Summary

**REORGANIZATION COMPLETE**: Paper 1 now focuses **exclusively on the RankOneToggle track**.

Paper 1 consists of **6 active Lean files** in the RankOneToggle implementation:
- **4 Core Modules**: Complete implementation (0 sorries each) 
- **2 Planned Extensions**: Fredholm theory and Tutorial (future work)

**Original Gödel-Banach files** (9 files) have been **moved to `old_files/`** - they are complete but not needed for the current Paper 1 proof.

---

## Current Active Files - RankOneToggle Track Only

### 🏗️ Foundation Layer (Level 0)
**Files with no internal dependencies - pure mathematical foundations**

#### `RankOneToggle/Projection.lean`
- **Purpose**: Orthogonal projection API for rank-one projections onto lines
- **External Dependencies**: `Mathlib.Analysis.InnerProductSpace.Basic`, `Mathlib.Analysis.Normed.Operator.ContinuousLinearMap`
- **Internal Dependencies**: None
- **Status**: ✅ Complete (0 sorries)
- **Key Results**: Projection idempotency, self-adjointness, norm bounds

### 🏛️ Core Layer (Level 1)
**Core mathematical structures building on foundations**

#### `RankOneToggle/Toggle.lean`
- **Purpose**: Full toggle operator G(c) := id - c·P implementation
- **External Dependencies**: `Mathlib.Analysis.InnerProductSpace.Orthogonal`
- **Internal Dependencies**: `Papers.P1_GBC.RankOneToggle.Projection`
- **Status**: ✅ Complete (0 sorries)
- **Key Results**: Toggle operator definition, kernel/range characterization

#### `RankOneToggle/ShermanMorrison.lean`
- **Purpose**: Sherman-Morrison identities and resolvent analysis with robust norm bounds
- **External Dependencies**: `Mathlib` (comprehensive)
- **Internal Dependencies**: None (standalone but conceptually part of RankOneToggle)
- **Status**: ✅ Complete (0 sorries) - **MAJOR ACHIEVEMENT**
- **Key Results**: Inverse formulas, explicit resolvent, triangle inequality norm bounds

---

### 📐 Integration Layer (Level 2)  
**Advanced integration of core components**

#### `RankOneToggle/Spectrum.lean`
- **Purpose**: Spectrum and essential spectrum computations for toggle operators
- **External Dependencies**: `Mathlib.Analysis.Normed.Algebra.Spectrum`
- **Internal Dependencies**: `Papers.P1_GBC.RankOneToggle.Toggle`, `Papers.P1_GBC.RankOneToggle.ShermanMorrison`
- **Status**: ✅ Complete (0 sorries)
- **Key Results**: Complete spectral analysis, essential spectrum characterization

---

### 🎯 Planned Extensions (Level 3)
**Future extensions to the core implementation**

#### `RankOneToggle/Fredholm.lean`
- **Purpose**: Fredholm theory - index 0 and dimension calculations for toggle operators
- **External Dependencies**: TBD
- **Internal Dependencies**: `Papers.P1_GBC.RankOneToggle.Toggle`, `Papers.P1_GBC.RankOneToggle.Spectrum`
- **Status**: 📋 Planned
- **Expected Results**: Fredholm index computation, kernel/cokernel dimensions

#### `RankOneToggle/Tutorial.lean`
- **Purpose**: Comprehensive examples and teaching material for rank-one toggle operators
- **External Dependencies**: None
- **Internal Dependencies**: All RankOneToggle modules
- **Status**: 📋 Planned
- **Expected Results**: Didactic examples, practical usage demonstrations

---

### 🧪 Application Layer (Build Target)
**Complete build target including all active modules**

#### `P1_Minimal.lean`
- **Purpose**: Complete build target for Paper 1's rank-one toggle implementation
- **External Dependencies**: None
- **Internal Dependencies**: ALL core RankOneToggle modules (Projection, Toggle, Spectrum, ShermanMorrison)
- **Status**: ✅ Complete (0 sorries)
- **Build Command**: `lake build Papers.P1_GBC.P1_Minimal`

---

## RankOneToggle Dependency Graph (Simplified)

```
Level 0 (Foundation):
  RankOneToggle/Projection.lean
  RankOneToggle/ShermanMorrison.lean (standalone)

Level 1 (Core):
  RankOneToggle/Toggle.lean ← Projection

Level 2 (Integration):
  RankOneToggle/Spectrum.lean ← Toggle, ShermanMorrison

Level 3 (Extensions - Planned):
  RankOneToggle/Fredholm.lean ← Toggle, Spectrum
  RankOneToggle/Tutorial.lean ← All modules

Build Target:
  P1_Minimal.lean ← Projection, Toggle, Spectrum, ShermanMorrison
```

---

## Paper 1 Mathematical Content Location

### 🎯 Where Are the Paper 1 Proofs?

The **complete proofs for Paper 1** are contained in the **RankOneToggle track**:

#### Core Mathematical Results:
1. **Projection Theory**: `RankOneToggle/Projection.lean`
   - Orthogonal projection onto lines in Hilbert spaces
   - Idempotency, self-adjointness, and norm properties

2. **Toggle Operator Theory**: `RankOneToggle/Toggle.lean`  
   - Rank-one toggle operator G(c) := id - c·P
   - Kernel/range characterization and injectivity ↔ surjectivity

3. **Spectral Analysis**: `RankOneToggle/Spectrum.lean`
   - Complete spectrum computation: σ(G(false)) = {1}, σ(G(true)) = {0,1}
   - Essential spectrum analysis for both cases

4. **Sherman-Morrison Formula**: `RankOneToggle/ShermanMorrison.lean` ⭐
   - Projection-specialized Sherman-Morrison inverse: (I + αP)⁻¹ = I - α/(1+α)P
   - Explicit resolvent formulas for toggle operators
   - **Robust norm bounds** using triangle inequality approach

#### Mathematical Achievement:
- **0 sorries** across all core modules
- **Version-stable proofs** using robust mathematical techniques
- **Complete operator-theoretic framework** from projections to resolvents
- **Ready for mathlib4** contribution with clean mathematical API

---

## Build Dependencies

### Minimal Build Targets
```bash
# Minimal Sherman-Morrison core (0 sorries)
lake build Papers.P1_GBC.P1_Minimal

# Complete Sherman-Morrison with norm bounds
lake build Papers.P1_GBC.RankOneToggle.ShermanMorrison

# Original Gödel-Banach complete
lake build Papers.P1_GBC.SmokeTest
```

### Development Dependencies
```bash
# Core mathematical framework
lake build Papers.P1_GBC.Core

# Toggle operator family
lake build Papers.P1_GBC.RankOneToggle.Toggle
lake build Papers.P1_GBC.RankOneToggle.Spectrum

# Integration testing
lake build Papers.P1_GBC.Statement
```

---

## Key Architectural Insights

1. **Clean Separation**: Two distinct mathematical tracks with minimal cross-dependencies
2. **Foundation Independence**: Base layer files require only external mathematical libraries
3. **Incremental Build**: Well-structured dependency layers enable incremental compilation
4. **Minimal Interfaces**: Clear import boundaries between conceptual layers
5. **Testing Strategy**: Both smoke testing (integration) and minimal builds (core functionality)

### Sherman-Morrison Achievement Highlight
The **Sherman-Morrison implementation** represents a major milestone:
- **Zero sorries** in core operator theory modules
- **Version-stable proofs** using robust mathematical techniques  
- **Ready for mathlib4** contribution with clean dependency structure
- **Complete mathematical framework** from projections to norm bounds

---

**Last Updated**: August 22, 2025  
**Total Files**: 19 Lean files  
**Completion Status**: Sherman-Morrison core complete (0 sorries), extensions planned