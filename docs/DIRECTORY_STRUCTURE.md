# Foundation-Relativity Directory Structure

## 📁 Project Organization

```
FoundationRelativity/
├── Papers/                           # 📚 Main academic implementations
│   ├── P1_GBC/                      # ✅ Gödel-Banach (0 sorries)
│   │   ├── Core.lean                # Operator definitions and spectrum
│   │   ├── Statement.lean           # Main theorems and proofs
│   │   ├── LogicAxioms.lean         # Gödel axiomatization
│   │   └── Correspondence.lean      # Logic-analysis bridge
│   ├── P2_BidualGap/                # ✅ Gap → WLPO AXIOM-CLEAN!
│   │   ├── Basic.lean               # Core definitions (BidualGapStrong, WLPO)
│   │   ├── WLPO_Equiv_Gap.lean      # Main equivalence (forward complete)
│   │   ├── Constructive/            # Implementation complete
│   │   │   ├── Ishihara.lean        #   ✅ Gap → WLPO (0 sorries, axiom-clean)
│   │   │   └── DualStructure.lean   #   🔧 API bridges (3 sorries)
│   │   └── documentation/           # 📄 Papers, reports, status
│   │       ├── paper-v3.2.tex       #   📄 LaTeX with Lean results
│   │       ├── README.md             #   📄 Paper overview
│   │       └── implementation_details/ # 📄 Technical details
│   ├── P3_2CatFramework/            # 📋 Framework ready (6 sorries)
│   │   ├── Basic.lean               # Pseudo-functor infrastructure
│   │   └── FunctorialObstruction.lean # Non-functoriality results
│   └── P4_SpectralGeometry/         # 🔧 Active development (61 sorries)
│       ├── Geometry/                # Neck torus definition
│       ├── Spectral/                # Variational principles
│       ├── Logic/                   # Con(PA) undecidability bridge
│       └── Discrete/                # 🔧 CPW discrete model (85% complete)
│           ├── NeckGraph.lean       #   Discrete n×n torus graph
│           ├── TuringEncoding.lean  #   TM → edge weights encoding
│           └── IntervalBookkeeping.lean # Spectral band arithmetic
│
├── CategoryTheory/                  # 🏗️ Foundation framework
│   ├── Found.lean                   # Foundation type and morphisms
│   ├── BicatFound.lean              # Bicategorical structure
│   ├── PseudoFunctor.lean           # Pseudo-functor implementation
│   └── Witness.lean                 # Witness type framework
│
├── Gap2/                            # 🎯 ρ=1 pathologies (WLPO-level)
├── APFunctor/                       # 🎯 ρ=1 pathologies (WLPO-level)
├── RNPFunctor/                      # 🎯 ρ=2+ pathologies (DC_ω-level)
│
├── Scripts/                         # 🔧 Utilities and verification
│   └── AxiomCheck.lean             # Axiom usage verification
│
├── test/                           # 🧪 Regression and verification tests
└── docs/                           # 📚 Comprehensive documentation
    ├── README.md                   # Main documentation overview
    ├── planning/                   # 📋 Roadmaps and status
    │   ├── ROADMAP-v3.2.md         #   Current roadmap with axiom-clean status
    │   ├── project-status.md       #   Overall project status
    │   └── paper4-status.md        #   Paper 4 discrete model status
    ├── papers/                     # 📄 LaTeX sources (legacy)
    ├── analysis/                   # 🔬 Formalization insights
    ├── sprints/                    # 🏃 Sprint completion reports
    ├── archive/                    # 📦 Historical documentation
    └── reference/                  # 🛠️ Developer guides
        ├── DEV_GUIDE.md            #   Setup and workflows
        └── TOOLCHAIN_UPGRADE.md    #   Lean toolchain management
```

## 🎯 Current Status Overview

### ✅ **Completed Papers**
- **Paper 1**: Gödel-Banach Correspondence - Complete (0 sorries)
- **Paper 2 Forward**: Gap → WLPO - **AXIOM-CLEAN** (0 sorries)

### 🔧 **Active Development**  
- **Paper 2 Reverse**: WLPO → Gap - Pending (1 sorry)
- **Paper 3**: 2-Categorical Framework - Ready for implementation (6 sorries)
- **Paper 4**: Spectral Geometry Discrete Model - 85% complete (61 sorries)

## 📁 Key Directory Details

### `Papers/P2_BidualGap/` - Axiom-Clean Achievement
- **`Constructive/Ishihara.lean`**: Main breakthrough - axiom-clean Gap → WLPO
- **`documentation/paper-v3.2.tex`**: Academic paper with Lean results  
- **`documentation/implementation_details/`**: Technical architecture and status
- **`documentation/old_files/`**: Pre-breakthrough historical documentation

### `Scripts/`
- **`AxiomCheck.lean`**: Verification script for axiom usage
- Confirms axiom-clean status: only `Classical.choice`, `propext`, `Quot.sound`

### `docs/`
- **Current active documentation** reflecting axiom-clean breakthrough
- **`old_files/`**: Obsolete pre-breakthrough documentation
- **`archive/`**: Complete historical development record

## 🔍 Navigation Patterns

### **For the Axiom-Clean Achievement**
1. **Main theorem**: `Papers/P2_BidualGap/Constructive/Ishihara.lean`
2. **Academic paper**: `Papers/P2_BidualGap/documentation/paper-v3.2.tex`
3. **Technical details**: `Papers/P2_BidualGap/documentation/implementation_details/`
4. **Axiom verification**: `Scripts/AxiomCheck.lean`

### **For Current Development**
1. **Project status**: `docs/planning/project-status.md`
2. **Current roadmap**: `docs/planning/ROADMAP-v3.2.md`  
3. **Paper 4 progress**: `docs/planning/paper4-status.md`
4. **Developer setup**: `docs/reference/DEV_GUIDE.md`

### **For Historical Context**
1. **Development history**: `docs/archive/` (sprint reports, etc.)
2. **Pre-breakthrough docs**: Various `old_files/` directories  
3. **Legacy papers**: `docs/papers/` (superseded by paper-specific docs)

## 🏗️ Build Targets

### **Main Results**
```bash
# Axiom-clean theorem
lake build Papers.P2_BidualGap.Constructive.Ishihara

# Complete Paper 1  
lake build Papers.P1_GBC.Statement

# Paper 4 discrete model
lake build Papers.P4_SpectralGeometry.Discrete
```

### **Verification**
```bash
# Axiom checking
lake env lean Scripts/AxiomCheck.lean

# Full project build
lake build
```

## 📊 File Statistics

| Component | Files | Status | Key Achievement |
|-----------|-------|--------|------------------|
| **Paper 1** | ~15 | ✅ Complete | Full formalization |
| **Paper 2** | ~10 | ✅ Forward Complete | **Axiom-clean Gap → WLPO** |
| **Paper 3** | ~8 | 📋 Ready | Framework complete |
| **Paper 4** | ~25 | 🔧 85% Complete | Discrete model active |
| **Core Framework** | ~20 | ✅ Stable | Category theory foundation |
| **Documentation** | 100+ | 📚 Comprehensive | Includes complete history |

---

This directory structure reflects the evolution from initial research through the major **axiom-clean breakthrough** in Paper 2's Gap → WLPO direction, while maintaining complete historical documentation and supporting active development of remaining components.