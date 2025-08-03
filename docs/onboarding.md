# Foundation-Relativity Onboarding Guide

**Welcome to the Foundation-Relativity Project**  
**A Lean 4 formalization of foundation-relative mathematics**

---

## 🎯 **Quick Start Summary**

The **Foundation-Relativity** project formalizes how mathematical pathologies behave differently under various foundational assumptions. We've completed Papers 1-3 with **0 sorries total** and are now working on Paper 4.

**Current Status**: Papers 1-3 complete ✅, Paper 4 Phase 1A complete 🔧  
**Active Work**: Paper 4 discrete CPW model implementation  
**Key Achievement**: First complete formal verification of foundation-relative mathematics

---

## 📁 **Repository Layout**

```
FoundationRelativity/
├── Papers/                     # Main academic results
│   ├── P1_GBC/                # ✅ Gödel-Banach (0 sorries)
│   ├── P2_BidualGap/          # ✅ Bidual Gap (0 sorries)  
│   ├── P3_2CatFramework/      # ✅ 2-Categories (0 sorries)
│   └── P4_SpectralGeometry/   # 🔧 Spectral Geometry (61 sorries)
│       ├── Geometry/          # Neck torus definition
│       ├── Spectral/          # Variational principles
│       ├── Logic/             # Con(PA) bridge
│       └── Discrete/          # Fast-track CPW model
├── CategoryTheory/            # Foundation framework
├── Gap2/, APFunctor/, RNPFunctor/  # ρ=1,2 pathologies
├── docs/                      # This documentation
├── test/                      # Comprehensive test suite
└── scripts/                   # CI and development tools
```

---

## 📚 **Essential Documents**

### **Current Status & Planning**
1. **[Project Status](planning/project-status.md)** - Overall project status
2. **[Paper 4 Status](planning/paper4-status.md)** - Current work on Paper 4
3. **[Paper 4 Roadmap](planning/paper4-roadmap-enhanced.md)** - Fast-track implementation plan

### **Completed Papers (LaTeX Sources)**
1. **[Paper 1: Gödel-Banach](papers/P1-GBC.tex)** - Operator encoding of incompleteness
2. **[Paper 2: Bidual Gap](papers/P2-BidualGap.tex)** - WLPO equivalence  
3. **[Paper 3: 2-Categories](papers/P3-2CatFramework.tex)** - Pseudo-functor framework
4. **[Paper 4: Spectral Geometry](papers/P4-SpectralGeometry.tex)** - Undecidable eigenvalues (in progress)

### **Developer Resources**
- **[Dev Guide](reference/DEV_GUIDE.md)** - Development workflows
- **[Code Reference](CODE_REFERENCE.md)** - Mathematical implementations catalog
- **[Directory Structure](DIRECTORY_STRUCTURE.md)** - Detailed file organization

---

## ⚙️ **Technical Stack**

- **Lean Version**: 4.22.0-rc4 (pinned in `lean-toolchain`)
- **Mathlib**: Latest compatible version
- **CI/CD**: GitHub Actions with strict quality gates
- **Testing**: Comprehensive test suite in `test/`
- **Scripts**: Formatting, axiom checking, sorry allowlist

---

## 🏆 **Key Achievements**

### **Completed (Papers 1-3)**
- ✅ **24 → 0 sorries** eliminated across all papers
- ✅ **Foundation-relativity theorem** formally verified
- ✅ **Bicategorical framework** complete with coherence
- ✅ **Machine-verified proofs** of all core results

### **In Progress (Paper 4)**
- 🔧 **Discrete CPW model** infrastructure complete
- 🔧 **61 sorries** remaining in discrete implementation
- 🔧 **Consultant corrections** implemented after critical feedback
- 🔧 **Fast-track approach** targeting 6-7 weeks to completion

---

## 🚀 **Getting Started**

### **1. Setup Development Environment**
```bash
# Clone repository
git clone https://github.com/AICardiologist/FoundationRelativity.git
cd FoundationRelativity

# Install Lean toolchain
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Download mathlib cache
lake exe cache get

# Build project
lake build
```

### **2. Run Tests**
```bash
# Run all tests
lake test

# Check for unauthorized sorries
bash scripts/check-sorry-allowlist.sh

# Run specific paper tests
lake exe Paper1Tests
lake exe Paper2Tests
lake exe Paper3Tests
```

### **3. Explore the Code**
- Start with completed papers in `Papers/P1_GBC/`, `Papers/P2_BidualGap/`, `Papers/P3_2CatFramework/`
- See current work in `Papers/P4_SpectralGeometry/Discrete/`
- Review foundation framework in `CategoryTheory/`

---

## 📋 **Current Work: Paper 4**

### **What's Implemented**
- Discrete neck torus as n×n grid with periodic boundaries
- Turing machine encoding via edge weight perturbations
- Spectral gap definition using Rayleigh quotients
- Variational characterization with test functions
- Π₁ complexity proof structure

### **What's Needed**
- Complete harmonic series asymptotic bounds
- Implement Bareiss algorithm for Sturm's theorem
- Prove perturbation theory estimates
- Verify spectral gap dichotomy theorem
- Connect discrete model to continuum limit

### **Key Files to Review**
- `Papers/P4_SpectralGeometry/Discrete/ConsultantBoundsRevised.lean` - Corrected variational framework
- `Papers/P4_SpectralGeometry/Discrete/TuringEncoding.lean` - TM → spectral gap reduction
- `Papers/P4_SpectralGeometry/Discrete/Pi1Encoding.lean` - Complexity characterization

---

## 🔧 **Development Workflow**

### **Branch Strategy**
- **Main branch**: `main` (protected)
- **Feature branches**: `feature/description`
- **Documentation**: `docs/description`
- **Fixes**: `fix/description`

### **PR Process**
1. Create feature branch from main
2. Implement changes with tests
3. Run `lake build` and `lake test`
4. Check sorry allowlist: `bash scripts/check-sorry-allowlist.sh`
5. Create PR with clear description
6. Ensure CI passes
7. Get review and merge

### **Quality Standards**
- Zero sorries in completed work
- All axioms documented in allowlist
- Comprehensive test coverage
- Clear documentation
- CI must pass

---

## 🎯 **Foundation-Relativity Concepts**

### **Relativity Degrees (ρ)**
- **ρ = 1**: Requires WLPO (Weak Limited Principle of Omniscience)
- **ρ = 2**: Requires DC_ω (Countable Choice)
- **ρ = 3**: Requires AC_ω (Choice for countable families)

### **Key Results**
1. **Gödel-Banach Correspondence**: Consistency ↔ Surjectivity
2. **Bidual Gap**: Non-reflexivity ↔ WLPO
3. **Pseudo-Functor Obstruction**: Foundation-relative non-functoriality
4. **Spectral Undecidability**: TM halting ↔ Spectral gap existence (in progress)

---

## 📞 **Support & Resources**

### **Documentation**
- Project docs in `docs/`
- Paper sources in `docs/papers/`
- Sprint history in `docs/archive/`

### **Getting Help**
- GitHub Issues for bugs/features
- GitHub Discussions for design questions
- PR comments for code review

### **Key Contacts**
- Repository: [github.com/AICardiologist/FoundationRelativity](https://github.com/AICardiologist/FoundationRelativity)
- Principal: Paul Chun-Kit Lee

---

## 🎓 **Contributing**

We welcome contributions! Areas where help is especially valuable:
- Proving remaining sorries in Paper 4
- Improving documentation
- Adding more tests
- Optimizing proof strategies

See [DEV_GUIDE.md](reference/DEV_GUIDE.md) for detailed contribution guidelines.

---

**Welcome to Foundation-Relativity!**  
**Together we're formalizing the foundations of mathematics.** 🎯