# Papers-to-Sprints Mapping: Research Implementation Timeline

## Overview

This document shows how the four "Gödel in Four Acts" research papers translate into our Lean repository development timeline. Each paper contributes specific pathologies or meta-constructions that we implement in staged sprints climbing the ρ-ladder and lifting into categorical/geometric layers.

---

## 📚 **Research Papers Implementation Map**

| **Paper** | **Core Mathematical Object(s)** | **Logical Strength (ρ-level)** | **Repository Module(s)** | **Sprint(s)** |
|-----------|----------------------------------|--------------------------------|---------------------------|---------------|
| **1. Gödel–Banach Correspondence** | • Rank-one Fredholm F on ℓ²<br>• "F is surjective" ↔ Gödel sentence | ρ ≈ 4½ – 5<br>(needs Π²-reflection / DC_{ω·2}) | • `SpectralGap/GodelGap.lean` 🟡<br>• Arithmetic-encoding helpers 🟡 | **Sprint 39–41**<br>(after ρ = 4) |
| **2. Bidual Gap Across Foundations** | • Double-dual map ℓ∞ → (ℓ∞)ᵀᵀ<br>• Size of gap ↔ WLPO | ρ = 1<br>(already implemented) | • `Gap2Pathology.lean` ✓<br>• `APFunctor.lean` ✓ | **Done**<br>(Milestones A/B) |
| **3. 2-Categorical Framework** | • 2-category Found of foundations<br>• 2-functor Gap measuring pathologies<br>• Functorial-Obstruction theorem | Mirrors underlying pathology<br>(ρ = 1–5) | • `CategoryTheory/Found.lean` 🟡<br>• `CategoryTheory/GapFunctor.lean` 🟡 | **Sprint 42–45**<br>(parallel after Gödel exists) |
| **4. Undecidability in Spectral Geometry** | • Computable metric on torus with λ₁ ↔ arithmetic sentence<br>• Cheeger bottleneck operator | ρ = 2 (Radon–Nikodým style)<br>ρ ≈ 3½ (Cheeger bottleneck) | • `SpectralGap/Cheeger.lean` ✓<br>• `Geometry/GodelTorus.lean` 🟡 | • **Cheeger done** (Sprint 35)<br>• **Torus**: Sprint 46–48 |

### **Legend**
- ✓ **Present**: Implemented and verified
- 🟡 **Planned**: Scheduled for future development

---

## 📅 **Sprint Timeline Alignment**

```
┌───────────────┬──────────────────────────────────────────────┐
│ 2025 Q3       │ Sprint 36‑38: ρ = 4 "Borel‑Selector" operator │
│               │ (extends SpectralGap framework)              │
├───────────────┼──────────────────────────────────────────────┤
│ 2025 Q4       │ Sprint 39‑41: Gödel‑Gap rank‑one Fredholm     │
│               │  – Implements Paper 1, finishes ρ ≈ 4½–5      │
├───────────────┼──────────────────────────────────────────────┤
│               │ Sprint 42‑45:                                 │
│ 2025 Q4‑Q1    │   • CategoryTheory/Found  (Paper 3)           │
│ 2026          │   • Gap 2‑functor + Functorial‑Obstruction    │
├───────────────┼──────────────────────────────────────────────┤
│ 2026 Q1‑Q2    │ Sprint 46‑48: Gödelian Torus (Paper 4)        │
│               │   – uses Cheeger & categorical layer          │
└───────────────┴──────────────────────────────────────────────┘
```

---

## 🔗 **Key Dependencies**

### **1. Cheeger Foundation (ρ ≈ 3½) → Borel-Selector (ρ = 4)**
- **Status**: ✅ **Complete** (Sprint 35)  
- **Technique Reuse**: Boolean-controlled diagonal gaps pattern debugged and ready
- **Application**: Borel-Selector extends Cheeger's construction methodology

### **2. ρ = 4 Pathology → Gödel-Gap (ρ ≈ 4½-5)**  
- **Prerequisite**: ρ = 4 "Borel-Selector" operator must be merged
- **Reason**: Gödel-Gap parameterizes Fredholm operator using double gap proof pattern
- **Timeline**: Sprint 39-41 begins after Sprint 36-38 completion

### **3. Gödel-Gap → 2-Categorical Framework**
- **Logical Content**: Gödel-Gap provides the pathological object for categorical lifting
- **Functorial Obstruction**: Found 2-category attempts (and fails) to lift Gödel pathology  
- **Parallel Development**: Categorical work starts once Gödel operator skeleton exists

### **4. Cheeger + Categorical → Gödelian Torus**
- **Dual Prerequisites**:
  - **Analytic**: Cheeger bottleneck analysis (✅ already implemented)
  - **Categorical**: 2-categorical language for foundation-relative spectrum analysis
- **Integration**: "No single foundation sees the full spectrum" formalization

---

## 🎯 **Implementation Strategy by Paper**

### **Paper 1: Gödel–Banach Correspondence**
```lean
-- Anticipated architecture (Sprint 39-41)
namespace GodelGap
  -- Rank-one Fredholm on ℓ²
  def rankOneFredholm (φ : ℕ → Bool) : BoundedOp := ...
  
  -- Gödel sentence encoding
  def godelSentence : ArithmeticFormula := ...
  
  -- Core correspondence theorem
  theorem fredholm_surjective_iff_godel : 
    IsSurjective (rankOneFredholm φ) ↔ godelSentence.Provable := ...
end GodelGap
```

### **Paper 2: Bidual Gap** ✅ **COMPLETE**
```lean
-- Current implementation (Sprints S0-S3)
namespace Gap2
  def Gap₂Pathology : PathologyType := ...
  theorem Gap_requires_WLPO : RequiresWLPO Gap₂Pathology := ...
end Gap2
```

### **Paper 3: 2-Categorical Framework**
```lean
-- Planned architecture (Sprint 42-45)  
namespace CategoryTheory.Found
  -- 2-category of foundations
  def FoundationCat : Cat := ...
  
  -- 2-functor measuring pathologies
  def GapFunctor : FoundationCat ⥤ Cat := ...
  
  -- Functorial obstruction theorem
  theorem functorial_obstruction : 
    ¬ ∃ (lift : GapFunctor.Lift), ... := ...
end CategoryTheory.Found
```

### **Paper 4: Undecidability in Spectral Geometry**
```lean
-- Mixed status: Cheeger ✅ complete, Torus 🟡 planned
namespace SpectralGeometry
  -- Cheeger bottleneck (Sprint 35 ✅)
  def cheeger (β : ℝ) (b : ℕ → Bool) : BoundedOp := ...
  
  -- Gödelian torus (Sprint 46-48 🟡)
  def godelianTorus : RiemannianManifold := ...
  theorem torus_spectrum_undecidable : ... := ... 
end SpectralGeometry
```

---

## 🚨 **Critical Success Factors**

### **Sequential Dependencies**
1. **No Paper 1 work** until ρ = 4 branch merged (Sprint 36-38 completion)
2. **No Paper 3 work** until Gödel-Gap operator skeleton exists (Sprint 39+ initiation)  
3. **No Paper 4 torus work** until both Cheeger (✅) and categorical framework ready

### **Parallel Development Opportunities**
- **Sprint 39-41**: Math-Coder on Gödel-Gap proofs, SWE-AI can begin categorical scaffolding
- **Sprint 42-45**: Coordinated development on 2-categorical framework
- **Sprint 46-48**: Integration of all four papers into unified framework

### **Infrastructure Readiness**
- **CI/CD**: Keep release machinery ready for 2-3 sprint cycles per paper
- **Documentation**: Each paper maps to dedicated module documentation  
- **Quality Gates**: Zero-sorry policy maintained across all paper implementations

---

## 📊 **Progress Tracking**

### **Current Status (v1.0-rc)**
- ✅ **Paper 2**: Complete bidual gap implementation (ρ = 1)
- ✅ **Paper 4 (Part 1)**: Cheeger bottleneck (ρ ≈ 3½) 
- 🚀 **Paper 1 (Prep)**: ρ = 4 foundation (Sprint 36 active)
- ⏳ **Paper 3**: Awaiting Gödel-Gap prerequisite
- ⏳ **Paper 4 (Part 2)**: Awaiting categorical framework

### **Completion Targets**
- **Q3 2025**: Papers 1-2 complete, Paper 4 (Part 1) complete
- **Q4 2025**: Paper 1 (Gödel-Gap) complete, Paper 3 initiated  
- **Q1 2026**: Paper 3 complete, Paper 4 (Part 2) initiated
- **Q2 2026**: All four papers fully implemented and integrated

---

## 🎯 **Immediate Action Items**

### **SWE-AI (Current)**
- ✅ Sprint 36 infrastructure ready  
- 🔍 Monitor CI and release machinery
- 📋 Maintain paper-to-sprint mapping documentation

### **Math-Coder (Next)**
- 📝 Create Sprint 36 design document (ρ = 4 Borel-Selector)
- 🔧 Implement `SpectralGap/Rho4.lean` stub
- 🚀 Begin 7-day development cycle

### **Both (Strategic)**
- 🎭 No premature work on Papers 1 & 3 until dependencies satisfied
- 📈 Each paper completion enables next phase of research implementation
- 🏆 Maintain zero-sorry policy across all four paper implementations

---

## 🎓 **Research Impact Timeline**

### **Academic Milestones**
- **v1.0**: Papers 2 + 4(Part 1) → First foundation-relativity hierarchy
- **v1.1**: Paper 1 → Gödel-Banach correspondence formalized  
- **v1.2**: Paper 3 → Complete 2-categorical framework
- **v2.0**: Paper 4(Part 2) → Full spectral geometry integration

### **Community Impact**
- **Reference Implementation**: All four "Gödel in Four Acts" papers in Lean
- **Methodology**: Staged sprint approach for complex mathematical formalizations
- **Ecosystem**: Advanced techniques for foundation-sensitive mathematics

---

**Mapping Complete**: Four research papers → 48 sprints → Complete formal verification  
**Current Focus**: Sprint 36 (ρ = 4) → Gateway to Papers 1 & 3  
**Strategic Vision**: Systematic climb from ρ = 1 to full classical strength** 🎯

---

*Research-to-Implementation Mapping: Foundation-Relativity "Gödel in Four Acts" Series*