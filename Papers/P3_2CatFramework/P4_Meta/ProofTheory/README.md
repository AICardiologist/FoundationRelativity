# Paper 3B: Proof-Theoretic Scaffold

## ❄️ STATUS: FROZEN - Complete (September 2, 2025)

## 🚨 SEE SEPARATION GUIDE FIRST

**CRITICAL**: Read [`../../documentation/MASTER_DEPENDENCY_CHART.md`](../../documentation/MASTER_DEPENDENCY_CHART.md) before any work!

This guide shows the complete Paper 3A/3B separation and which files are frozen.

---

This directory contains the complete Paper 3B formalization with 21 axioms representing the honest limit of schematic encoding.

## ⚠️ IMPORTANT: DO NOT MODIFY THESE FILES

All files in this directory are FROZEN. They belong to Paper 3B which is complete.
Paper 3A development should NOT touch or import these files.

## 📦 Aggregator

To use Paper 3B components, import the aggregator:
```lean
import Papers.P3_2CatFramework.Paper3B_Main
```

Do NOT import individual ProofTheory files directly.

## 📁 Files (All Frozen)

| File | Purpose | Axioms | Status |
|------|---------|--------|--------|
| Core.lean | Stage-based ladders, circular dependency solution | 5 | ❄️ FROZEN |
| Reflection.lean | RFN machinery and principles | 4 | ❄️ FROZEN |
| Heights.lean | Height certificates for proof theory | 3 | ❄️ FROZEN |
| Progressions.lean | Progression through consistency levels | 4 | ❄️ FROZEN |
| Collisions.lean | Main results: RFN→Con, collision theorems | 5 | ❄️ FROZEN |
| **TOTAL** | | **21** | ❄️ **FROZEN** |

## 🎯 Key Achievements

### Axiom Reduction Timeline
- Initial: 30 axioms
- PR-5b: 24 axioms (Bot_is_FalseInN discharged)
- PR-6: 21 axioms (collision_step_semantic discharged via Stage approach)
- PR-7: 21 axioms stable (collision_tag discharged via internalization)

### Core Results (All Proven)
1. **RFN_implies_Con**: RFN_Σ₁ → Con proved schematically (theorem, not axiom)
2. **collision_step_semantic**: Discharged as theorem via Stage-based approach
3. **collision_tag**: Discharged as theorem via RFN_implies_Con_formula
4. **Height certificates**: Upper bounds constructive, lower bounds axiomatized

## 📊 Statistics
- **Total Lines**: ~800
- **Mathematical Sorries**: 0
- **Axioms**: 21 (honest limit of schematic encoding)
- **Files**: 5
- **Status**: Complete and frozen

## 🔗 Documentation
- Full axiom index: `documentation/AXIOM_INDEX.md`
- Paper 3B status: `documentation/P3B_STATUS.md`
- Release notes: `documentation/RELEASE_NOTES_P3B.md`

## 📋 Design Decisions

### Stage-Based Ladders
The key innovation was using `Stage` structures that carry type class instances, solving circular dependencies between consistency and reflection ladders:

```lean
structure Stage where
  n : Nat
  theory : Theory
  [isCons : IsCons theory]
  [isReflect : IsReflect theory]
```

### Axiom Discipline
All 21 axioms are:
- In the `Ax` namespace
- Documented with clear mathematical meaning
- CI-guarded against regression
- Represent unavoidable schematic limitations

## ⚠️ Development Rules

1. **DO NOT MODIFY** any file in this directory
2. **DO NOT ADD** new files to this directory
3. **DO NOT IMPORT** these files in Paper 3A code
4. **USE Paper3B_Main.lean** as the only entry point
5. **RESPECT** the frozen status - Paper 3B is complete

## ✅ Verification

Run to verify Paper 3B status:
```bash
lake build Papers.P3_2CatFramework.Paper3B_Main
```

Expected output:
```
✅ STATUS: COMPLETE (September 2, 2025)
📊 Final Statistics:
- Axioms: 21 (honest limit reached)
- Sorries: 0
❄️ This paper is FROZEN - no further changes needed
```