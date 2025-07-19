# Foundation-Relativity

[![CI](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml)
[![Nightly](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml)
[![Lean 4.3.0](https://img.shields.io/badge/Lean-4.3.0-blue)](https://github.com/leanprover/lean4)

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

# Run tests
lake exe testFunctors
lake exe testNonIdMorphisms
lake exe AllPathologiesTests
```

### Verify No Sorry

```bash
bash scripts/verify-no-sorry.sh
```

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

This formalization is based on the observation that certain mathematical constructions require classical axioms (like the Law of Excluded Middle or the Axiom of Choice) to be well-defined. By formalizing these as functors between categories, we can precisely characterize:

1. **What fails**: The witness type is empty in constructive settings
2. **Why it fails**: Specific classical principles required (WLPO, LPO, etc.)
3. **How to fix it**: Alternative constructive formulations

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

- ✅ **Sprint S0**: Core infrastructure
- ✅ **Sprint S1**: Covariant functors  
- ✅ **Sprint S2**: Witness API
- 🚧 **Sprint S3**: Formal proofs (in progress)
- 📅 **Sprint S4**: Planned

## 📄 License

This project is licensed under the Apache 2.0 License - see the [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

- The Lean 4 development team
- The mathlib4 community
- Contributors to constructive mathematics foundations

---

*"Mathematics is not about numbers, equations, computations, or algorithms: it is about understanding."* – William Paul Thurston