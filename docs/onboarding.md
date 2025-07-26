# Math-Coder AI Onboarding Guide

**Foundation-Relativity Project Handoff**  
**New Math-AI Agent Integration for S38-S45 Implementation**

---

## 🎯 **Quick Start Summary**

You are joining the **Foundation-Relativity** project to implement Papers 1-3 of the "Gödel in Four Acts" series in Lean 4. Your primary responsibility is **formal proof development** focusing on bicategory infrastructure and Gödel-Banach correspondence over the next 8 weeks (Sprints S38-S45).

**Current Status**: v0.4.0 complete with Paper 2 (bidual gap ρ ≤ 2) already verified  
**Your Mission**: Implement Papers 1 & 3 using the optimization-oriented roadmap  
**Key Resources**: Complete LaTeX sources in `docs/papers/`, detailed sprint breakdown, green CI

---

## 🔐 **1. Access & Credentials**

| **What** | **Where/How** | **Notes** |
|----------|---------------|-----------|
| **Repository** | https://github.com/AICardiologist/FoundationRelativity | Request write access |
| **Project Boards** | S38-41 Breakdown, Current Sprint, Long-term | Move cards in Current Sprint |
| **CI Status** | README.md badge | Keep main & feature branches green |
| **Documentation** | This file: `docs/onboarding.md` | Your comprehensive guide |

---

## 📁 **2. Repository Layout (Post-S40 Refactor)**

```
FoundationRelativity/
├── Axiom/                 # Isolated "allowed axioms"
│   └── BanachLimit.lean   # exists_banach_limit centralized
├── AnalyticPathologies/   # Paper 2 refactored (S40)
│   ├── BidualGap.lean
│   ├── APFail.lean
│   └── RNPFail.lean
├── CategoryTheory/        # Papers 1&3 bicategorical layer
│   ├── Found.lean         # Foundation bicategory (S39)
│   ├── GapFunctor.lean    # 2-functors (S40)
│   └── Obstruction.lean   # Functorial obstruction (S44)
├── GodelGap/             # Paper 1 implementation (S41-S42)
│   ├── Logic/Sigma1Formula.lean
│   ├── Projection.lean
│   └── Operator.lean
├── docs/
│   ├── papers/           # Complete LaTeX sources P1-P4
│   ├── roadmap-extended.md
│   └── sprint38-41-breakdown.md   # Your day-level guide
├── scripts/              # check-no-axioms.sh, formatting
└── .github/             # CI workflows
```

---

## 📚 **3. Essential Documents**

### **Strategic Planning**
1. **[Strategic Roadmap](roadmap-extended.md)** - Complete S38-S45 plan with design decisions
2. **[Sprint Breakdown](sprint38-41-breakdown.md)** - Day-level tasks for your immediate work
3. **[Papers Mapping](papers-to-sprints-mapping.md)** - How research maps to implementation

### **Research Papers (LaTeX Sources)**
1. **[Paper 1: Gödel-Banach](papers/P1-GBC.tex)** - Core for S41-S42 
2. **[Paper 2: Bidual Gap](papers/P2-BidualGap.tex)** - Already implemented, S40 refactor
3. **[Paper 3: 2-Categorical](papers/P3-2CatFramework.tex)** - Core for S39-S44
4. **[Paper 4: Spectral Geometry](papers/P4-SpectralGeometry.tex)** - Future work S46+

### **Technical References**
- **Toolchain**: Lean 4.22.0-rc4 (pinned in `lean-toolchain`)
- **Style Guide**: `scripts/fmt.sh` for formatting
- **Quality Gate**: `scripts/check-no-axioms.sh` for axiom tracking

---

## ⚙️ **4. Critical Technical Notes**

### **Design Decisions You Must Follow**

| **Decision** | **Current Status** | **Your Action** |
|--------------|-------------------|----------------|
| **Banach Limit Axiom** | `exists_banach_limit` in BidualGap.lean | S40: Centralize to `Axiom/BanachLimit.lean` |
| **Hard-coded Σ¹₀** | Design choice for Paper 1 | S41: Implement `inductive Sigma1Formula` |
| **Borel σ-algebra** | Paper mentions, Lean stubs | Provide typeclass stub, proofs by `admit` OK |
| **Universe Pattern** | `universe u v`, `Sort (max u v)` | Stick to pattern, no `ulift` hacks |
| **ρ > 2 Work** | Explicitly de-scoped | Out of scope until S46+ |

### **Axiom Policy**
- **Acceptable**: `exists_banach_limit`, `sig1_em` (Σ¹₀ decidability)
- **Monitoring**: `scripts/check-no-axioms.sh` must pass CI
- **Centralization**: Move axioms to `Axiom/` modules in S40

---

## 📋 **5. Immediate Sprint Tasks (S38-S41)**

### **Sprint 39: Found.Bicategory Skeleton** 
**Your first major deliverable**

| Day | Task | Est. LoC | Paper Reference |
|-----|------|----------|-----------------|
| 1 | `CategoryTheory.Foundation` enum (BISH, ZFC, etc.) | 40 | P3 §2.1 |
| 1-2 | `Structure Interpretation` with stub fields | 70 | P3 §2.2 |
| 3 | Category instance on Foundation | 50 | P3 §2.3 |
| 4 | `Bicategory Found` with simple coherence | 90 | P3 §2.4 |
| 5 | `FoundTest.lean` verification | 20 | Test framework |

**Key Points:**
- Use mathlib `Bicategory.Basic` 
- All proofs by `rfl` or `simp` (no complex category theory yet)
- Leave I1b field as `PreservesBorel : Prop` stub

### **Sprint 40: Pathology 2-Functors**
**Refactor existing Paper 2 work**

| Day | Task | Focus | Paper Integration |
|-----|------|-------|------------------|
| 1 | `Pathology/GAP.lean` groupoid | ContinuousLinearMap only | P2 §1 → P3 §3 |
| 2-3 | APFail, RNPFail groupoids | Classical proofs OK | P2 §2-3 → P3 §3 |
| 4 | `GapFunctor.lean` contravariant | `Found^op → Cat` | P3 §3.1 |
| 5 | Testing and verification | Sanity checks | Integration test |

### **Sprint 41: Gödel Boolean & Operator**
**Core Paper 1 construction**

| Day | Task | Implementation | Paper Reference |
|-----|------|---------------|-----------------|
| 1 | `Logic/Sigma1Formula.lean` | Inductive type + Gödel numbering | P1 §3.1 |
| 1 | `Logic/Sigma1EM.lean` | `axiom sig1_em : DecidableEq` | P1 §3.2 |
| 2 | `logicGodelBool.lean` | `def c_G : Bool` `@[irreducible]` | P1 §3.3 |
| 3 | `GodelGap/Projection.lean` | `P_g : BoundedOp` basis projector | P1 §4.1 |
| 4 | `GodelGap/Operator.lean` | `G := I - c_G • P_g` | P1 §4.2 |
| 5 | Spectrum lemma | Two-point spectrum `{0,1}` | P1 §4.3 |

---

## 🔧 **6. Development Workflow**

### **Branch & PR Policy**
- **Main branch**: `master` (protected, squash-merge only)
- **Feature branches**: `feat/<topic>` for your work
- **PR size**: Keep under 800 LoC diff when possible
- **Review process**: Claude (SWE-AI) reviews all PRs

### **Pre-Merge Checklist**
1. ✅ `lake build && lake test` succeeds locally
2. ✅ `scripts/fmt.sh` run (formatting)
3. ✅ `scripts/check-no-axioms.sh` returns clean
4. ✅ CI green (except non-blocking mathlib bump)
5. ✅ CHANGELOG.md updated if user-visible
6. ✅ Claude approval on PR

### **Communication Protocol**
- **Daily sync**: Brief progress update (2 min bullets)
- **Design questions**: Use GitHub Discussions for Lean architecture
- **Bugs/enhancements**: GitHub Issues (no TODO comments)
- **Decisions**: Document in `docs/decisions/` if needed

---

## 🚨 **7. What to Avoid**

**Critical Mistakes to Prevent:**
- ❌ **New global axioms** (other than approved Banach limit, Σ¹₀-EM)
- ❌ **Toolchain changes** (Lean 4.22.0-rc4 is pinned)
- ❌ **Massive reformatting** (keep formatting separate from logic)
- ❌ **Bypassing axiom check** (`scripts/check-no-axioms.sh` must pass)
- ❌ **Working on ρ > 2** (explicitly out of scope)
- ❌ **Paper 4 geometric work** (requires manifold library)

---

## 📊 **8. Paper Implementation Status**

### **Your Responsibility Matrix**

| **Paper** | **Status** | **Your Role** | **Timeline** |
|-----------|------------|---------------|--------------|
| **P1: Gödel-Banach** | 🎯 **Primary target** | S41-S42 core implementation | 2-3 weeks |
| **P2: Bidual Gap** | ✅ Sections 1-3 done | S40 refactor to 2-functors | 1 week |
| **P3: 2-Categorical** | 🎯 **Primary target** | S39-S44 complete framework | 4-6 weeks |
| **P4: Spectral Geometry** | ⏸ **Out of scope** | Future milestone S46+ | Not your focus |

### **Current Lean Verification Status**

| **Section** | **Mathematical Content** | **Lean Status** | **Notes** |
|-------------|-------------------------|-----------------|-----------|
| **P2 §1-3** | Bidual/AP/RNP at ρ ≤ 2 | ✅ Complete, zero-sorry | Refactor to categorical |
| **P2 §4** | ρ = 3-4 quantitative tiers | ⏸ Skeleton stubs | De-scoped for now |
| **P1 core** | Gödel-operator construction | 🟡 Your S41 target | Hard-coded approach |
| **P3 bicategory** | Foundation 2-category | 🟡 Your S39 target | mathlib integration |

---

## 🎯 **9. Success Metrics & Exit Criteria**

### **Sprint 39 Success** 
- ✅ `CategoryTheory.Foundation` compiles without errors
- ✅ Basic bicategory laws verified (associator, unitors)
- ✅ No `sorry` statements
- ✅ CI integration working

### **Sprint 40 Success**
- ✅ Three pathology 2-functors: Gap, APFail, RNPFail
- ✅ Integration with Foundation bicategory
- ✅ Axiom centralized to `Axiom/BanachLimit.lean`
- ✅ No new axioms introduced

### **Sprint 41 Success**
- ✅ Gödel Boolean `c_G` defined (irreducible)
- ✅ Rank-one operator `G = I - c_G • P_g` implemented
- ✅ Basic spectral properties proven
- ✅ Foundation for Paper 1 Fredholm work

### **Overall S38-S45 Target**
- 🎯 **v0.5.0**: Papers 1-3 fully verified
- 🎯 **Zero-sorry**: All proofs formally complete
- 🎯 **Paper alignment**: Core theorems match LaTeX sources
- 🎯 **Infrastructure**: Ready for Paper 4 extensions

---

## 🚀 **10. Getting Started Action Plan**

### **Week 1 (Sprint 39): Foundation Bicategory**
1. **Study**: Read Paper 3 §2 (2-categorical framework basics)
2. **Code**: Implement `CategoryTheory.Foundation` enum and basic structure
3. **Build**: Create bicategory instance using mathlib primitives
4. **Test**: Verify basic category laws with simple proofs
5. **Integrate**: Ensure CI remains green throughout

### **Week 2 (Sprint 40): Pathology Integration**
1. **Refactor**: Move existing pathology files to new namespace
2. **Centralize**: Create `Axiom/BanachLimit.lean` module
3. **Wrap**: Implement 2-functor wrappers for existing pathologies
4. **Verify**: Ensure integration with bicategory framework
5. **Document**: Update module organization and dependencies

### **Week 3 (Sprint 41): Gödel Construction**
1. **Design**: Study Paper 1 §3-4 for operator construction
2. **Implement**: Build Σ¹₀ formula framework (hard-coded approach)
3. **Construct**: Define Gödel Boolean and rank-one operator
4. **Prove**: Basic spectral analysis (two-point spectrum)
5. **Prepare**: Set foundation for Fredholm equivalence work

### **Ongoing Throughout**
- **Daily sync**: Brief progress updates
- **Quality**: Maintain zero-sorry policy
- **CI**: Keep builds green
- **Documentation**: Update as you progress

---

## 📞 **11. Support & Escalation**

### **Technical Questions**
- **Lean architecture**: GitHub Discussions tab
- **Paper interpretation**: Cross-reference LaTeX sources in `docs/papers/`
- **CI issues**: Tag Claude (SWE-AI) for infrastructure support

### **Blocked Situations**
- **Axiom questions**: Coordinate with Claude on axiom policy
- **Mathlib changes**: Check if toolchain upgrade needed
- **Scope creep**: Refer back to roadmap for explicit de-scoping

### **Regular Check-ins**
- **Sprint boundaries**: Review progress with Claude
- **Paper alignment**: Verify theorems match research sources
- **Quality gates**: Ensure zero-sorry and axiom policies maintained

---

## 🎓 **12. Success Vision**

By the end of S38-S45, you will have:

✅ **Built the first complete formal verification** of foundation-relative mathematics  
✅ **Implemented Papers 1-3** of the "Gödel in Four Acts" series  
✅ **Created a bicategory framework** for analyzing mathematical pathologies  
✅ **Established methodology** for complex mathematical formalization  
✅ **Set foundation** for geometric extensions (Paper 4) in future milestones

Your work directly contributes to advancing formal verification of axiom-sensitive mathematics and establishing Foundation-Relativity as a reference implementation for constructive reverse mathematics.

---

**Welcome to the Foundation-Relativity project!**  
**Ready to formalize the Gödel-Banach correspondence and 2-categorical framework.** 🎯

---

*Onboarding complete - Math-Coder AI integration for S38-S45 implementation*