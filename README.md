# Foundation-Relativity

[![CI](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml)
[![Nightly](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml)
[![Lean 4.3.0](https://img.shields.io/badge/Lean-4.3.0-blue)](https://github.com/leanprover/lean4)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

> **Sprint S5 Complete**: RNP₃ axiom-free proofs ✅  
> All pathology frameworks complete with rigorous theorem proofs (zero axioms, zero sorry).

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
    ├── RNP_Fail₂ : Foundation ⥤ Cat
    └── RNP_Fail₃ : Foundation ⥤ Cat
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
│   ├── WitnessCore.lean     # Generic witness API
│   ├── LogicDSL.lean        # RequiresWLPO/DCω framework
│   └── Analysis/
│       └── Lemmas.lean      # Martingale tail functional proofs
├── Gap2/
│   ├── Functor.lean         # Gap₂ pathology
│   └── Proofs.lean          # Gap_requires_WLPO theorem ✅
├── APFunctor/
│   ├── Functor.lean         # Approximate pathology
│   └── Proofs.lean          # AP_requires_WLPO theorem ✅
├── RNPFunctor/
│   ├── Functor.lean         # Real number pathology
│   ├── Proofs.lean          # RNP_requires_DCω theorem ✅
│   └── Proofs3.lean         # RNP₃_requires_DCω_plus theorem ✅
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

### Verification

All formal proofs can be verified with:

```bash
# Verify Gap₂ requires WLPO
lake exe Gap2ProofTests

# Verify AP_Fail₂ requires WLPO  
lake exe APProofTests

# Verify RNP_Fail₂ requires DC_ω
lake exe RNPProofTests

# Verify RNP₃ requires DC_{ω+1}  
lake exe RNP3ProofTests

# Run all pathology tests
lake exe AllPathologiesTests
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

This formalization targets **four key pathologies** from recent research on foundation-relativity:

### Paper Targets (ρ-degree hierarchy)

| Pathology | Logic Strength | Status | Description |
|-----------|---------------|--------|-------------|
| **Gap₂** | ρ = 1 (WLPO) | ✅ v0.3.1 | Bidual gap in Banach spaces |
| **AP_Fail₂** | ρ = 1 (WLPO) | ✅ v0.3.2 | Approximation Property failure |
| **RNP_Fail₂** | ρ = 2 (DC_ω) | ✅ v0.3.3 | Radon-Nikodým Property failure |
| **RNP_Fail₃** | ρ = 2+ (DC_{ω+1}) | ✅ v0.3.4 | Separable-dual martingale pathology |
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

## Contributing

* Fork → create a feature branch.
* Use `LEAN_ABORT_ON_SORRY=1` locally before every push.
* Open a PR — CI must be green and `scripts/verify-no-sorry.sh` clean.

## 📈 Project Status

### Sprint Progress

- ✅ **Sprint S0**: Core infrastructure (`Foundation`, `Interp`, basic functors)
- ✅ **Sprint S1**: Covariant functors (fixed mathematical impossibility of contravariant approach)  
- ✅ **Sprint S2**: Witness API (unified `WitnessCore`, migrations, CI/CD)
- ✅ **Sprint S3**: Formal proofs (Gap₂ & AP_Fail₂ require WLPO)
  - **v0.3.1**: `Gap_requires_WLPO` theorem 
  - **v0.3.2**: `AP_requires_WLPO` theorem
- ✅ **Sprint S4**: RNP_Fail₂ proof (ρ=2 DC_ω level)
  - **v0.3.3**: `RNP_requires_DCω` theorem
- ✅ **Sprint S5**: RNP₃ axiom-free proofs (ρ=2+ DC_{ω+1} level) **← COMPLETE**
  - **v0.3.4**: `RNP3_requires_DCωPlus` theorem, zero axioms in core modules
- 📅 **Sprint S6**: Spectral gap & beyond ρ-scale exploration

### Current Achievement: Complete ρ-Hierarchy

**Sprint S5 Achievement**: All pathology proofs complete with zero axioms!

```lean
-- ρ = 1 Level (WLPO)
theorem Gap_requires_WLPO : RequiresWLPO Gap2Pathology := ...     ✅
theorem AP_requires_WLPO : RequiresWLPO APPathology := ...        ✅

-- ρ = 2 Level (DC_ω)  
theorem RNP_requires_DCω : RequiresDCω RNPPathology := ...        ✅

-- ρ = 2+ Level (DC_{ω+1})
theorem RNP3_requires_DCωPlus : RequiresDCωPlus RNP3Pathology := ... ✅
```

**Next**: Spectral gap pathology (beyond ρ-scale, Gödel-incompleteness connections).

## 📄 License

This project is licensed under the Apache 2.0 License - see the [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

- The Lean 4 development team
- The mathlib4 community
- Contributors to constructive mathematics foundations

---

*"Mathematics is not about numbers, equations, computations, or algorithms: it is about understanding."* – William Paul Thurston