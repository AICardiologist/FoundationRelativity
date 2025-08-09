# Foundation Relativity Roadmap v3.2

## 🎯 Recent Achievement: Gap → WLPO (Axiom-Clean!)

**Status**: ✅ **COMPLETED** - The forward direction (Strong Bidual Gap ⇒ WLPO) is now **proof-complete** and **axiom-clean** in Lean.

- **File**: `Papers/P2_BidualGap/Constructive/Ishihara.lean`
- **Axioms**: Only standard classical axioms (`Classical.choice`, `propext`, `Quot.sound`)
- **Zero sorries** in the mathematical implementation
- **API-robust** proofs that survive mathlib version drift

---

## A) Paper Alignment (v3.1 → v3.2) 

### ✅ **COMPLETED**: Updated LaTeX Document

**File**: `docs/paper-v3.2.tex`

**Changes Made**:
1. **Added Contribution (C5)**: "Axiomatic calibration (Lean)" highlighting the Gap ⇒ WLPO result
2. **New Section 6.1**: "Axiomatic calibration (Lean)" with Proposition 6.2 and proof sketch
3. **Updated Abstract**: Mentions the classical Lean calibration
4. **Status Table**: Added row for Prop. 6.2 (Gap ⇒ WLPO) marked as "OK"
5. **Appendix**: Updated Lean status table and file references

---

## B) Repo Hygiene and Stability

### 1. **Extract API Shims** 🔄 **NEXT PRIORITY**

**Goal**: Create `Papers/P2_BidualGap/Constructive/Shims.lean` with reusable utilities

**Content**:
- Unit sphere normalization helpers (`normalize`, `normalize_norm`, `smul_normalize`)
- Stable inverse cancellation via `simp` patterns  
- abs↔norm bridge lemmas (`abs_y_apply`)
- Operator norm bound utilities (`opNorm_le_of_unitBall_bound`)

**Benefits**: 
- Future-proofs against mathlib API drift
- Makes proofs more readable and reusable
- Centralizes fragile API dependencies

### 2. **CI: Axiom Gate** 🔄 **HIGH PRIORITY**

**File**: `.github/workflows/axiom-check.yml` (new)

**Content**:
```yaml
name: Axiom Check
on: [push, pull_request]
jobs:
  axiom-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Install Lean
        # ... lean setup ...
      - name: Build project
        run: lake build
      - name: Check axioms
        run: |
          lake env lean Scripts/AxiomCheck.lean > axioms.log
          if grep -q "sorryAx" axioms.log; then
            echo "❌ Found sorryAx contamination!"
            cat axioms.log
            exit 1
          fi
          echo "✅ Axiom-clean!"
```

**Benefits**: Prevents regressions, catches sorry contamination early

### 3. **Documentation & Cross-Links** 🔄 **MEDIUM PRIORITY**

**Update README.md** with:
- Lean status table mirroring the paper
- Direct links to Lean files for each theorem
- Quick start guide for verification

---

## C) Next Formalization Targets (Safe, Incremental)

### 4. **Generalize to IsROrC** 🔄 **LOW PRIORITY**

**Goal**: Port Gap ⇒ WLPO from `ℝ` to `[IsROrC 𝕜]`

**Changes**:
- Replace `Real.norm_eq_abs` with `IsROrC.abs_*` lemmas
- Update type signatures to work for both `ℝ` and `ℂ`
- Add tests for complex case

**Benefits**: Mathematical completeness, broader applicability

### 5. **Finite Lattice Embedding API** 🔄 **LOW PRIORITY**

**Goal**: Expose clean API for finite distributive lattice embeddings

**Content**:
- Function: `finite_lattice_embedding : FiniteDistributiveLattice L → (L ↪ ℓ∞/c₀)`
- Partition utilities for disjoint infinite sets
- Examples and tests

### 6. **Bibliography Cross-References** 🔄 **LOW PRIORITY**

**Goal**: Link paper results to Lean symbol names

**Content**: Appendix table mapping theorem numbers to exact Lean declarations

---

## D) Research Directions (Bigger Bites)

### 7. **Formalize Translator Obstruction** 🔄 **RESEARCH**

**Status**: Statement precise, formalization deferred

**Requirements**:
- Constructive/realizability setting for WLPO reduction
- Translator typeclass definition
- Meta-theorem mechanization

**Timeline**: Future work, depends on constructive Lean environment

### 8. **Classical Anchors** 🔄 **OPTIONAL**

**Goal**: Classical Banach limit construction (ultrafilter route)

**Status**: Optional for v3.2, keep separate from constructive core

**Benefits**: Complete the classical picture, complement the Gap ⇒ WLPO direction

---

## Concrete Next Steps (Priority Order)

### **Phase 1** (Week 1-2): Infrastructure
1. ✅ **DONE**: Update LaTeX paper to v3.2
2. 🔄 **Create `Constructive/Shims.lean`** - Refactor API utilities
3. 🔄 **Set up CI axiom check** - Prevent regressions
4. 🔄 **Update README** - Documentation alignment

### **Phase 2** (Week 3-4): Polish
5. 🔄 **IsROrC generalization** - Extend to complex numbers  
6. 🔄 **Finite lattice API** - Clean embedding interface
7. 🔄 **Cross-references** - Paper ↔ Lean mapping

### **Phase 3** (Future): Research
8. 🔄 **Translator obstruction** - Constructive formalization
9. 🔄 **Classical anchors** - Ultrafilter-based constructions

---

## Current Status Summary

| Component | Status | File | Axioms |
|-----------|--------|------|--------|
| **Gap ⇒ WLPO** | ✅ **Complete** | `Constructive/Ishihara.lean` | Clean |
| Finite surrogates | ✅ Planned | `Basics/FiniteCesaro.lean` | Clean |  
| Cesàro bounds | ✅ Planned | `Basics/FiniteCesaro.lean` | Clean |
| Lattice embedding | ✅ Planned | `Gap/FiniteEmbedding.lean` | Clean |
| WLPO ⇒ Gap | 🔄 Pending | | TBD |
| Paper v3.2 | ✅ **Complete** | `docs/paper-v3.2.tex` | N/A |

---

## Key Success Metrics

- ✅ **Axiom-clean proofs** - No `sorryAx` contamination
- ✅ **API stability** - Survives mathlib version changes  
- ✅ **Paper-repo alignment** - LaTeX and Lean in sync
- 🔄 **CI protection** - Automated regression detection
- 🔄 **Reusable components** - Clean shim layer

**Bottom Line**: The core mathematical achievement (Gap ⇒ WLPO) is complete and axiom-clean. The roadmap focuses on infrastructure, polish, and incremental extensions rather than major mathematical breakthroughs.