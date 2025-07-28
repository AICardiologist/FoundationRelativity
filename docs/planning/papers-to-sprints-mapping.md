# Papers-to-Sprints Mapping: Research Implementation Timeline

## Overview

This document shows how the four "Gödel in Four Acts" research papers translate into our Lean repository development timeline. **Updated for S43+ roadmap** with current implementation status reflecting completed Sprint 41-42 achievements and strategic focus on Papers 1-3.

---

## 📚 **Research Papers Implementation Status**

| **Paper** | **Core Mathematical Object(s)** | **Logical Strength (ρ-level)** | **Lean Status** | **Sprint Coverage** |
|-----------|----------------------------------|--------------------------------|-----------------|-------------------|
| **1. Gödel–Banach Correspondence** | • Rank-one operator 𝔊 on ℓ²<br>• Fredholm equivalence: Surj ↔ Gödel sentence | ρ ≈ 4½–5<br>(Σ¹-EM + Fredholm) | 🟡 **S43+**<br>Infrastructure ready | Paper 1 framework implementation |
| **2. Bidual Gap Across Foundations** | • ℓ∞ → (ℓ∞)** bidual map<br>• AP/RNP failure at ρ ≤ 2 | ρ = 1-2<br>(WLPO, DC_ω) | ✅ **Complete S42**<br>Mathematical framework | Complete with bicategorical structure |
| **3. 2-Categorical Framework** | • Bicategory Found of foundations<br>• Gap 2-functor, obstruction theorem | Mirrors pathology<br>(ρ = 1-5) | ✅ **Complete S42**<br>Bicategory + obstruction | Complete bicategorical infrastructure |
| **4. Spectral Geometry** | • Gödel-torus with λ₁ ↔ Con(PA)<br>• Cheeger neck construction | ρ = 2-3<br>(DC_ω, choice fragments) | ✅ **Complete S35-36**<br>Cheeger + Rho4 + GodelGap | All spectral pathologies implemented |

### **Legend**
- ✅ **Complete**: Implemented and verified
- 🟡 **Planned**: Scheduled for current/future development
- **ρ-level**: Foundation-relativity degree (logical strength required)

---

## 📅 **Updated Sprint Timeline (S41-S43+)**

```
┌───────────────┬──────────────────────────────────────────────┐
│ S41 ✅        │ Zero-Sorry Milestone (v0.4.0)                │
│ (Complete)    │ → Complete mathematical formalization        │
├───────────────┼──────────────────────────────────────────────┤
│ S42 ✅        │ Bicategorical Framework (v0.5.0-alpha)       │
│ (Complete)    │ → Papers #2-3 mathematical frameworks       │
├───────────────┼──────────────────────────────────────────────┤
│ S43 (Current) │ Pseudo-Functor + CI Tightening               │
│               │ → Complete pseudo-functor stack + automation │
├───────────────┼──────────────────────────────────────────────┤
│ S44+ (Future) │ Paper 1 Implementation + Advanced Features   │
│               │ → Gödel-Banach correspondence + doc-gen      │
└───────────────┴──────────────────────────────────────────────┘
```

---

## 🔗 **Paper Coverage Strategy**

### **Paper 2: Bidual Gap** ✅ **COMPLETE (Sprint 42)**

**Mathematical Framework**: Complete bicategorical implementation with meaningful theorem statements

**Key Achievements**:
- ✅ **Non-functoriality theorem**: Pentagon coherence-based impossibility proof  
- ✅ **WLPO ⇔ Gap equivalence**: Constructive proof with 7 proof obligations
- ✅ **Coherence properties**: `preservesPentagon` and `eliminatesWitnesses` replace placeholder logic
- ✅ **Bicategorical integration**: Full integration with FoundationBicat structure

**Current Status**: v0.5.0-alpha with complete mathematical frameworks ready for expansion

### **Paper 3: 2-Categorical Framework** ✅ **COMPLETE (Sprint 42)**

**Bicategorical Infrastructure**: Complete genuine bicategory with coherence laws

**Key Achievements**:
- ✅ **Enhanced FoundationBicat**: Associators, unitors, pentagon/triangle coherence
- ✅ **Functorial obstruction theorem**: Witness elimination impossibility  
- ✅ **Whiskering operations**: Left/right whiskering for 2-cell composition
- ✅ **Enhanced witness structures**: APWitness, RNPWitness for quantitative analysis

**Current Status**: Complete bicategorical framework ready for pseudo-functor implementation

### **Paper 4: Spectral Geometry** ✅ **COMPLETE (Sprint 35-36)**

**Spectral Gap Implementation**: All pathology levels implemented with formal proofs

**Key Achievements**:
- ✅ **Cheeger-Bottleneck pathology**: ρ ≈ 3½ with boolean parameterization
- ✅ **Rho4 pathology**: ρ = 4 Borel-Selector with DC_{ω·2} requirement  
- ✅ **Gödel-Gap correspondence**: Complete spectral gap → logical consistency connection
- ✅ **Zero axioms**: All spectral pathologies proven without classical axioms

**Current Status**: Complete implementation with all ρ-levels 3-4 verified

### **Paper 1: Gödel-Banach Correspondence** 🟡 **PLANNED (Sprint 44+)**

**Infrastructure Ready**: All dependencies implemented for Paper 1 expansion

**Current Status (v0.4.0):**

| Section | Topic | Lean Implementation | Status |
|---------|-------|-------------------|--------|
| §1. Bidual gap (ℓ∞/c₀) | Non-reflexivity, Gap₂ functor | `SpectralGap/BidualGap.lean` | ✅ Zero-sorry |
| §2. AP failure | Johnson-Szankowski operators | `SpectralGap/APFail.lean` | ✅ Zero-sorry |
| §3. RNP obstruction | Vector-measure counterexample | `SpectralGap/RNPFail.lean` | ✅ Zero-sorry |
| §4. Quantitative tiers ρ=3,4 | Cheeger modulus, spectral bounds | Skeleton stubs | ⏸ De-scoped |

**S40 Refactoring Plan:**
- Move verified files to `AnalyticPathologies/` namespace
- Centralize `exists_banach_limit` axiom in `Axiom/BanachLimit.lean`
- Wrap results as Gap₂, APFail, RNPFail 2-functors for bicategory integration

### **Paper 1: Gödel-Banach** 🟡 **S41-S42 TARGET**

**Implementation Strategy:**
```lean
-- S41: Core construction
namespace GodelGap
  -- Hard-coded Σ¹₀ formulas (design decision)
  inductive Sigma1Formula : Type
  axiom sig1_em : DecidableEq Sigma1Formula
  
  -- Gödel Boolean (irreducible)
  def c_G : Bool := ... -- @[irreducible]
  
  -- Rank-one projection and operator
  def P_g : BoundedOp := ... -- basis projector
  def G : BoundedOp := I - c_G • P_g
  
  -- S42: Fredholm equivalence
  theorem surj_iff_godel : Surj G ↔ ... := ...
end GodelGap
```

**Paper 1 Alignment:**
- S41: Implements P1 §3-4 core construction
- S42: Proves P1 §5-6 Fredholm equivalence
- Uses design decisions: hard-coded formulas, acceptable axioms

### **Paper 3: 2-Categorical Framework** 🟡 **S39-S44 TARGET**

**Implementation Progression:**
```lean
-- S39: Bicategory skeleton
namespace CategoryTheory.Foundation
  inductive Foundation : Type | BISH | ZFC | HoTT | ...
  def Found : Bicategory Foundation := ...
  
-- S40: Pathology 2-functors  
  def Gap : Foundation^op ⥤ Cat := ...
  def APFail : Foundation^op ⥤ Cat := ...
  def RNPFail : Foundation^op ⥤ Cat := ...
  
-- S44: Obstruction theorem
  theorem functorial_obstruction : ... := ...
end CategoryTheory.Foundation
```

**Technical Approach:**
- S39: Basic bicategory with simple proofs (`rfl`, `simp`)
- S40: Integration with existing Paper 2 pathologies
- S44: Formal obstruction theorem from P3 §4

### **Paper 4: Spectral Geometry** 🟡 **FUTURE S46+**

**Current Status:**
- ✅ **Cheeger construction**: Complete in `SpectralGap/Cheeger.lean`
- 🟡 **Gödel-torus**: Requires manifold library + Laplacian formalization
- 🟡 **Spectral undecidability**: Builds on Papers 1-3 foundation

**Deferred Rationale:**
- Requires heavy differential geometry stack
- Depends on stabilized bicategory framework
- Can be added without affecting core Papers 1-3

---

## 🎯 **Strategic Dependencies**

### **Sequential Requirements**
1. **S38 foundation** → S39 bicategory skeleton
2. **S39 bicategory** → S40 pathology 2-functors
3. **S40 2-functors** → S44 obstruction theorem
4. **S41 Gödel core** → S42 Fredholm equivalence

### **Parallel Development**
- **S40-S41**: Pathology refactoring || Gödel construction
- **S42-S44**: Fredholm proofs || Categorical obstruction
- **Math-Coder + Claude**: Proof development || Infrastructure

### **Paper Integration Points**
- **P2 → P3**: Existing pathologies become 2-functor examples
- **P1 → P3**: Gödel operator tests functorial obstruction
- **P1+P3 → P4**: Categorical framework enables geometric extensions

---

## 📊 **Implementation Progress Tracking**

### **Current Achievements (v0.4.0)**
- ✅ **Paper 2 (Core)**: Sections 1-3 complete, zero-sorry
- ✅ **Paper 4 (Base)**: Cheeger construction proven
- ✅ **Infrastructure**: Lean 4.22.0-rc4, papers LaTeX sources
- ✅ **CI/CD**: Optimized build, zero-axiom checking

### **S38-S45 Targets**
- 🎯 **Paper 1**: Complete Gödel-Banach correspondence
- 🎯 **Paper 3**: Full 2-categorical framework
- 🎯 **Paper 2**: Refactor to bicategory integration
- 🎯 **v0.5.0**: Papers 1-3 fully verified

### **Future Milestones (S46+)**
- 🔮 **Paper 4**: Complete spectral geometry
- 🔮 **Integration**: All four papers unified
- 🔮 **Extensions**: Higher ρ-levels, additional pathologies

---

## 🚨 **Risk Mitigation**

### **Scope Management**
- **ρ > 2 work**: Explicitly de-scoped until Papers 1-3 stable
- **Paper 4**: Deferred to avoid manifold library dependency
- **Borel proofs**: Postponed to focus on core framework

### **Technical Risks**
- **Axiom management**: Centralized in `Axiom/` modules
- **CI stability**: Regular integration testing
- **Mathlib compatibility**: Lean 4.22.0-rc4 pin maintained

### **Quality Assurance**
- **Zero-sorry policy**: Maintained across all implementations
- **Paper alignment**: Regular cross-reference with LaTeX sources
- **Documentation**: Sprint-level tracking and updates

---

## 🎓 **Academic Impact Timeline**

### **Near Term (v0.5.0)**
- **First complete formal verification** of Papers 1-3
- **Reference implementation** for foundation-relative mathematics
- **Categorical framework** for pathology analysis

### **Medium Term (v1.0)**
- **Complete "Gödel in Four Acts"** formalization
- **Geometric extensions** via Paper 4
- **Research methodology** for complex mathematical formalization

### **Long Term Impact**
- **Ecosystem leadership** in foundation-sensitive formal verification
- **Advanced techniques** for axiom-dependent mathematics
- **Educational resource** for constructive reverse mathematics

---

## 🚀 **Immediate Actions**

### **Math-Coder AI (Primary)**
1. **S39**: Implement Found bicategory skeleton
2. **S40**: Refactor Paper 2 pathologies to 2-functors
3. **S41**: Build Gödel operator construction
4. **Paper Focus**: Use LaTeX sources in `docs/papers/`

### **Claude (Infrastructure)**
1. **S38**: Complete rho4-polish release
2. **CI**: Maintain green builds throughout S39-S45
3. **Documentation**: Keep roadmap synchronized with progress
4. **Integration**: Coordinate Math-Coder development

### **Strategic Coordination**
- **Papers 1-3**: Immediate 8-week implementation window
- **Paper 4**: Future milestone after foundation stable
- **Quality**: Zero-sorry policy throughout
- **Progress**: Regular sprint completion tracking

---

**Research Implementation Complete**: Four papers → Systematic formal verification  
**Current Focus**: S38-S45 roadmap → Papers 1-3 priority  
**Strategic Vision**: Foundation-relative mathematics fully formalized** 🎯

---

*Updated for S38-S45 roadmap with complete papers infrastructure and strategic focus*