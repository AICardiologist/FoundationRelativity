# Foundation-Relativity

[![CI](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml)
[![Nightly](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml)
[![Lean 4.3.0](https://img.shields.io/badge/Lean-4.3.0-blue)](https://github.com/leanprover/lean4)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

> **Ready for PR Creation & Merge** 🚀  
> All 4 Sprint S2 branches are pushed. Infrastructure complete for formal proof development.

A Lean 4 formalization exploring how mathematical pathologies behave differently under various foundational assumptions.

## 🎯 Overview

This project formalizes the concept of **foundation-relativity** in constructive mathematics, demonstrating how certain mathematical constructions (pathologies) that are well-behaved in classical mathematics (ZFC) become problematic or impossible in constructive settings (BISH).

### Key Insight

The same mathematical object can exhibit fundamentally different properties depending on the foundational system:
- In **BISH** (Bishop's constructive mathematics): Pathologies manifest as empty witness types
- In **ZFC** (classical set theory): The same constructions have non-empty witnesses

## 🏗️ Architecture

```
Foundation ⥤ Cat
    │
    ├── Gap₂ : Foundation ⥤ Cat
    ├── AP_Fail₂ : Foundation ⥤ Cat  
    └── RNP_Fail₂ : Foundation ⥤ Cat
```

Each pathology functor maps:
- `bish ↦ ∅` (empty groupoid)
- `zfc ↦ ★` (singleton groupoid)
- `forget : bish → zfc` maps to the unique functor `∅ ⥤ ★`

## 📁 Project Structure

```
FoundationRelativity/
├── Found/
│   ├── InterpCore.lean      # Core foundation definitions
│   ├── BaseGroupoids.lean   # Shared groupoid constructions
│   └── WitnessCore.lean     # Generic witness API
├── Gap2/
│   └── Functor.lean         # Gap₂ pathology
├── APFunctor/
│   └── Functor.lean         # Approximate pathology
├── RNPFunctor/
│   └── Functor.lean         # Real number pathology
└── test/
    ├── NonIdMorphisms.lean  # Covariant functor tests
    └── AllPathologiesTest.lean # Comprehensive validation
```

## 🚀 Quick Start

### Prerequisites

- [Lean 4.3.0](https://github.com/leanprover/lean4/releases/tag/v4.3.0)
- [VS Code](https://code.visualstudio.com/) with [lean4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

### Building

```bash
# Clone the repository
git clone https://github.com/AICardiologist/FoundationRelativity.git
cd FoundationRelativity

# Build the project
lake build

# Run comprehensive test suite
lake exe testFunctors
lake exe testNonIdMorphisms
lake exe AllPathologiesTests
lake exe WitnessTests

# Verify no sorry in core modules
bash scripts/verify-no-sorry.sh
```

### Current Status: Ready for PR Merge

The repository has **4 feature branches** ready for sequential merge:

1. **[PR-1: feat/witness-core](https://github.com/AICardiologist/FoundationRelativity/pull/new/feat/witness-core)** - Witness API foundation
2. **[PR-2: feat/gap2-witness-api](https://github.com/AICardiologist/FoundationRelativity/pull/new/feat/gap2-witness-api)** - Gap₂ migration  
3. **[PR-3: feat/ap-rnp-witness-api](https://github.com/AICardiologist/FoundationRelativity/pull/new/feat/ap-rnp-witness-api)** - AP & RNP migrations
4. **[PR-4: feat/nightly-ci](https://github.com/AICardiologist/FoundationRelativity/pull/new/feat/nightly-ci)** - CI/CD workflows

**Merge Order**: PR-1 → PR-2 → PR-3 → PR-4 (each depends on the previous)

**After merge**: Tag `v0.3.0-witness` to mark Sprint S2 completion and unblock Sprint S3 proof development.

## 🔬 Technical Details

### Foundation Type

```lean
inductive Foundation
  | bish  -- Bishop's constructive mathematics
  | zfc   -- Classical set theory with choice
```

### Interpretation Morphisms

```lean
inductive Interp : Foundation → Foundation → Type
  | id_bish : Interp bish bish
  | id_zfc : Interp zfc zfc
  | forget : Interp bish zfc
```

### Witness API

The project uses a generic witness API to reduce boilerplate:

```lean
def WitnessType (α : Type) : Foundation → Type
  | bish => Empty
  | zfc => PUnit

def pathologyFunctor (α : Type) : Foundation ⥤ Cat
```

## 🎓 Mathematical Background

This formalization targets **four key pathologies** from recent research on foundation-relativity:

### Paper Targets (ρ-degree hierarchy)

| Pathology | Logic Strength | Status | Description |
|-----------|---------------|--------|-------------|
| **Gap₂** | ρ = 1 (WLPO) | 🎯 Sprint S3 | Bidual gap in Banach spaces |
| **AP_Fail₂** | ρ = 1 (WLPO) | 📅 Sprint S4 | Approximation Property failure |
| **RNP_Fail₂** | ρ = 2 (DC_ω) | 📅 Sprint S5 | Radon-Nikodým Property failure |
| **Spectral Gap** | Beyond ρ-scale | 🔮 Future | Gödel-incompleteness connection |

### Foundation-Relativity Principle

The same mathematical construction exhibits different behavior:

1. **BISH setting**: Witness type is `Empty` → pathology cannot be constructed
2. **ZFC setting**: Witness type is `PUnit` → pathology exists classically  
3. **Gap analysis**: Requires specific classical principles (WLPO, LPO, DC_ω)

This provides a **constructive diagnostic** for identifying exactly which non-constructive principles a theorem requires.

## 🛠️ Development

### Running CI Locally

```bash
LEAN_ABORT_ON_SORRY=1 lake build
```

### Adding New Pathologies

1. Create a new pathology type:
   ```lean
   structure MyPathology where
     data : Unit
   ```

2. Define the functor:
   ```lean
   def My_Pathology : Foundation ⥤ Cat := 
     pathologyFunctor MyPathology
   ```

3. Add tests to verify behavior

## 📚 Documentation

- [Development Guide](docs/DEV_GUIDE.md) - Detailed development instructions
- [CI Workflows](.github/workflows/README.md) - CI/CD documentation
- [Roadmap](ROADMAP.md) - Project milestones and future work

## 🤝 Contributing

Contributions are welcome! Please:

1. Fork the repository
2. Create a feature branch (`git checkout -b feature/amazing-feature`)
3. Commit your changes with clear messages
4. Push to your fork
5. Open a Pull Request

Ensure all tests pass and no `sorry` remains in core modules.

## 📈 Project Status

### Sprint Progress

- ✅ **Sprint S0**: Core infrastructure (`Foundation`, `Interp`, basic functors)
- ✅ **Sprint S1**: Covariant functors (fixed mathematical impossibility of contravariant approach)  
- ✅ **Sprint S2**: Witness API (unified `WitnessCore`, migrations, CI/CD) **← COMPLETE**
- 🎯 **Sprint S3**: Gap₂ WLPO proof (target: `Gap_requires_WLPO : RequiresWLPO Gap₂`)
- 📅 **Sprint S4**: AP_Fail₂ proof (reuse ρ=1 infrastructure)
- 📅 **Sprint S5**: RNP_Fail₂ proof (introduce ρ=2 DSL)

### Next Milestone: First Formal Proof

**Sprint S3 Goal**: Prove `Gap₂` requires WLPO with zero `sorry`

```lean
theorem Gap_requires_WLPO : RequiresWLPO Gap.Pathology := by
  -- Uses new Witness API + minimal classical lemmas
  -- Target: complete proof < 200 LoC
```

**Why Gap₂ first?** Minimal dependencies (elementary Banach spaces), exercises the full pipeline, quick win for proof-of-concept.

## 📄 License

This project is licensed under the Apache 2.0 License - see the [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

- The Lean 4 development team
- The mathlib4 community
- Contributors to constructive mathematics foundations

---

*"Mathematics is not about numbers, equations, computations, or algorithms: it is about understanding."* – William Paul Thurston