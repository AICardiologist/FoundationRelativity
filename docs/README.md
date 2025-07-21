# Foundation-Relativity Documentation

## 📚 Overview
This directory contains comprehensive documentation for the Foundation-Relativity project - a Lean 4 formalization of foundation-relative mathematics.

## 📖 Available Documentation

### Core Documentation
- **[Main README](../README.md)** - Project overview, quick start, and current status
- **[Development Guide](DEV_GUIDE.md)** - Setup, contribution guidelines, and best practices  
- **[Roadmap](../ROADMAP.md)** - Sprint history and future development plans
- **[Contributing](../CONTRIBUTING.md)** - How to contribute to the project

### Technical References  
- **[CITATION.cff](../CITATION.cff)** - Academic citation information
- **[License](../LICENSE)** - Apache 2.0 license details
- **[CHANGELOG](../CHANGELOG.md)** - Version history and changes

## 🎯 Current Status: Sprint S5 Complete

### ✅ **Major Achievements**
- **Complete ρ-hierarchy**: All pathology levels (ρ=1, ρ=2, ρ=2+) formally proven
- **Zero-axiom policy**: All temporary axioms replaced with rigorous theorem proofs
- **Comprehensive testing**: Full test suite with 10+ verification executables
- **Academic-ready**: Proper citation, documentation, and repository structure

### 🔬 **Mathematical Content**
```lean
-- ρ = 1 Level (Weak Limited Principle of Omniscience)
theorem Gap_requires_WLPO : RequiresWLPO Gap2Pathology        ✅
theorem AP_requires_WLPO : RequiresWLPO APPathology           ✅

-- ρ = 2 Level (Dependent Choice DC_ω)  
theorem RNP_requires_DCω : RequiresDCω RNPPathology           ✅

-- ρ = 2+ Level (Dependent Choice DC_{ω+1})
theorem RNP3_requires_DCωPlus : RequiresDCωPlus RNP3Pathology ✅
```

### 🚀 **Next Steps**
- **Sprint S6**: Spectral gap pathology (beyond ρ-scale)
- **Research connections**: Gödel incompleteness and foundational limits
- **Proof automation**: Tactics for automated ρ-degree detection

## 🤝 Getting Started
1. **New users**: Start with the [Main README](../README.md)
2. **Contributors**: Read [Contributing Guidelines](../CONTRIBUTING.md)  
3. **Developers**: Follow the [Development Guide](DEV_GUIDE.md)
4. **Researchers**: See [Academic Citation](../CITATION.cff) info

---

*Documentation last updated: Post-Sprint S5 (Repository cleanup and professionalization)*