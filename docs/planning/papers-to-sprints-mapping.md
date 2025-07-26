# Papers-to-Sprints Mapping: Research Implementation Timeline

## Overview

This document shows how the four "Gödel in Four Acts" research papers translate into our Lean repository development timeline. **Updated for S38-S45 roadmap** with current implementation status and strategic focus on Papers 1-3.

---

## 📚 **Research Papers Implementation Status**

| **Paper** | **Core Mathematical Object(s)** | **Logical Strength (ρ-level)** | **Lean Status** | **Sprint Coverage** |
|-----------|----------------------------------|--------------------------------|-----------------|-------------------|
| **1. Gödel–Banach Correspondence** | • Rank-one operator 𝔊 on ℓ²<br>• Fredholm equivalence: Surj ↔ Gödel sentence | ρ ≈ 4½–5<br>(Σ¹-EM + Fredholm) | 🟡 **S41-S42**<br>Hard-coded Sigma1Formula | Core construction & equivalence |
| **2. Bidual Gap Across Foundations** | • ℓ∞ → (ℓ∞)** bidual map<br>• AP/RNP failure at ρ ≤ 2 | ρ = 1-2<br>(WLPO, DC_ω) | ✅ **Complete**<br>Sections 1-3 proven | S40: Refactor to 2-functors |
| **3. 2-Categorical Framework** | • Bicategory Found of foundations<br>• Gap 2-functor, obstruction theorem | Mirrors pathology<br>(ρ = 1-5) | 🟡 **S39-S44**<br>Bicategory → obstruction | Complete framework |
| **4. Spectral Geometry** | • Gödel-torus with λ₁ ↔ Con(PA)<br>• Cheeger neck construction | ρ = 2-3<br>(DC_ω, choice fragments) | 🟡 **Future S46+**<br>Cheeger base ✅ done | Requires manifold library |

### **Legend**
- ✅ **Complete**: Implemented and verified
- 🟡 **Planned**: Scheduled for current/future development
- **ρ-level**: Foundation-relativity degree (logical strength required)

---

## 📅 **Updated Sprint Timeline (S38-S45)**

```
┌───────────────┬──────────────────────────────────────────────┐
│ S38 (now+7d)  │ rho4-polish release v0.4.1 + housekeeping    │
│               │ → Clean foundation for bicategory work       │
├───────────────┼──────────────────────────────────────────────┤
│ S39 (+7+14d)  │ Found.Bicategory skeleton (Paper 3 core)     │
│               │ → Hard-coded foundations, basic 2-category    │
├───────────────┼──────────────────────────────────────────────┤
│ S40 (+14+21d) │ Pathology 2-functors: Gap, AP_Fail, RNP_Fail │
│               │ → Paper 2 refactor + categorical integration │
├───────────────┼──────────────────────────────────────────────┤
│ S41 (+21+28d) │ Gödel Boolean & rank-one operator (Paper 1)  │
│               │ → Core construction: c_G, P_g, G = I - c_G•P_g│
├───────────────┼──────────────────────────────────────────────┤
│ S42-S45       │ Paper 1 completion + Paper 3 obstruction     │
│ (+28+56d)     │ → Fredholm equivalence + functorial theorem  │
└───────────────┴──────────────────────────────────────────────┘
```

---

## 🔗 **Paper Coverage Strategy**

### **Paper 2: Bidual Gap** ✅ **ALREADY COMPLETE**

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