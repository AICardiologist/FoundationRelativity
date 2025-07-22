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
- **[Technical Debt](../TECHNICAL_DEBT.md)** - Active debt tracking and resolution plans
- **[License](../LICENSE)** - Apache 2.0 license details
- **[CHANGELOG](../CHANGELOG.md)** - Version history and changes

## 🎯 Current Status: Sprint S6 Active - Milestone B Complete

### ✅ **Major Achievements**
- **Extended ρ-hierarchy**: Levels ρ=1, ρ=2, ρ=2+ proven + ρ=3 infrastructure complete
- **SpectralGap Milestone B**: Core infrastructure with concrete zero operator
- **Zero-axiom policy**: All temporary axioms replaced with rigorous theorem proofs  
- **CI optimization**: Mathlib cache enables fast builds (~45s vs 8+ min)
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

-- ρ = 3 Level (Axiom of Choice AC_ω) - Milestone B Complete
structure SpectralGapOperator := ...                              ✅
noncomputable def zeroGapOp : SpectralGapOperator := ...          ✅
```

### 🚀 **Next Steps**
- **Milestone C**: Non-trivial compact self-adjoint operators
- **Milestone D**: Constructive impossibility proof (AC_ω requirement)
- **Research connections**: Gödel incompleteness via spectral gap pathologies

## 🤝 Getting Started
1. **New users**: Start with the [Main README](../README.md)
2. **Contributors**: Read [Contributing Guidelines](../CONTRIBUTING.md)  
3. **Developers**: Follow the [Development Guide](DEV_GUIDE.md)
4. **Researchers**: See [Academic Citation](../CITATION.cff) info

---

*Documentation last updated: Sprint S6 Milestone B (SpectralGap infrastructure complete)*