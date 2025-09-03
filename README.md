# Axiom-Calibration

[![CI](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml)
[![Nightly](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml)
[![Paper 3A/3B Complete](https://img.shields.io/badge/Paper%203A%2F3B-Complete-brightgreen)](Papers/P3_2CatFramework/)
[![Paper 2 WLPO↔Gap](https://img.shields.io/badge/Paper%202%20WLPO%E2%86%94Gap-3%20sorries-green)](Papers/P2_BidualGap/)
[![Paper 1 Rank-One](https://img.shields.io/badge/Paper%201%20Rank--One-14%20sorries-yellow)](Papers/P1_GBC/)

🎯 Current Status (September 2025)

• Paper 3A/3B core framework: ✅ Stable, 0 sorries on 3A/3B code paths
  – Paper 3A (Framework & Calibrators): active development (WLPO/FT axes complete)
  – Paper 3B (Proof-theoretic scaffold): ❄️ FROZEN at 21 axioms (RFN_Σ₁ ⇒ Con proved)

• Paper 2 (WLPO ↔ Bidual Gap): ✅ Main equivalence done; 3 WLPO-conditional sorries remain
• Paper 1 (Rank-One Toggle Kernel): 🔧 ~14 sorries (mathlib-dependent sections)
• Paper 4 (Spectral Geometry): ⚠️ SUSPENDED (archived code: ~61 sorries; not built in CI)

## 🎯 Overview

A Lean 4 formalization project that calibrates the exact logical strength required for mathematical theorems. The project demonstrates **axiom calibration (AxCal)**: measuring precisely which axioms are needed for classical results that fail constructively.

> **Key Insight**: Many classical theorems become unprovable in constructive mathematics (BISH). We formalize exact equivalences between analytical "pathologies" and logical principles, providing precise calibrations of their axiom requirements.

### 📄 LaTeX Documents

All Paper 3 LaTeX documents are consolidated in [`Papers/P3_2CatFramework/latex/`](Papers/P3_2CatFramework/latex/):
- **Paper3_Main.tex** - Comprehensive framework document
- **Paper3A_Publication.tex** - Paper 3A with integrated DCω axis
- **Paper3B_Publication.tex** - Paper 3B proof-theoretic scaffold
- **Paper3_Lean_Formalization.tex** - Technical formalization details

### Papers and Results

1. **Paper 1: Rank-One Toggle on Hilbert Spaces** 🔧
   - Minimal operator-theoretic core around orthogonal projections
   - Sherman-Morrison inverse formula for rank-one perturbations
   - Lean formalization: ~14 sorries (pending mathlib updates)

2. **Paper 2: WLPO ↔ Bidual Gap Equivalence** ✅
   - Main theorem: Detecting bidual gap has exactly WLPO strength
   - Complete Lean 4 formalization with only 3 WLPO-conditional sorries
   - Constructive finite-dimensional surrogates via Cesàro means

**Papers 3A & 3B: Axiom Calibration Framework** ✅ **CORE STABLE**

• Paper 3A (Framework): Active
  – Uniformizability + height theory complete
  – WLPO axis (bidual gap) and FT axis (uniform continuity) calibrated
  – Stone Window API: 100+ Boolean algebra lemmas
  – DC_ω/Baire: Work package (axiomatized), earmarked for future 3C; not in CI

• Paper 3B (Scaffold): ❄️ Frozen at 21 axioms
  – Stage-based ladders resolve circularities
  – RFN_Σ₁ → Con: proved schematically
  – Con → Gödel: axiomatized (documented in AXIOM_INDEX.md)

4. **Paper 4: Spectral Geometry** ⚠️ **SUSPENDED**
   - Original goal: Undecidable eigenvalues on manifolds
   - Status: Suspended due to mathematical issues in the approach

### Axiom Calibration Methodology

We measure the logical strength of a statement by its height along a chosen axis. Heights are per-axis; a theorem has an orthogonal profile (one height per axis).
- **Height 0 (on an axis)**: Provable constructively (no use of that axis)
- **Height 1 (on an axis)**: Requires the first step on that axis
  (e.g., WLPO on the WLPO axis; FT on the FT axis)
- **Height ≥ 2 (on an axis)**: Requires iterates/stronger fragments on that same axis
  (e.g., stronger omniscience or bar/choice schemes, depending on the axis)

Our framework provides orthogonal calibration axes:
- **WLPO axis**: Bidual gap, double-dual embedding phenomena
- **FT axis**: Fan Theorem, uniform continuity theorems (UCT)
- **DC_ω axis**: Work package for Paper 3C (axiomatized, not in CI)

Examples: Bidual gap has profile (WLPO, FT, DC_ω) = (1, 0, 0); UCT has (0, 1, 0).

## 📚 Papers & Formalization Status

### Complete Papers
- **[Papers 3A & 3B: Axiom Calibration Framework](Papers/P3_2CatFramework/)** ✅ **CORE STABLE**
  - **Paper 3A**: AxCal framework with calibrated WLPO/FT axes (active development)
  - **Paper 3B**: Proof-theoretic scaffold with 21 axioms (❄️ FROZEN)
  - **🚨 IMPORTANT**: See [`MASTER_DEPENDENCY_CHART.md`](Papers/P3_2CatFramework/documentation/MASTER_DEPENDENCY_CHART.md) for separation guide
  - Use `Papers.P3_2CatFramework.Paper3A_Main` or `Papers.P3_2CatFramework.Paper3B_Main` aggregators (NOT both)

### Nearly Complete
- **[Paper 2: WLPO ↔ Bidual Gap](Papers/P2_BidualGap/)** ✅ **Main theorem complete (3 conditional sorries)**
  - Full equivalence: Gap_∃ ↔ WLPO formalized
  - Witness space: c₀ (sequences vanishing at infinity)
  - Remaining sorries: Only in optional completeness module

### In Progress
- **[Paper 1: Rank-One Toggle Kernel](Papers/P1_GBC/)** 🔧 **Core complete (~14 sorries)**
  - Sherman-Morrison formula verified
  - Spectrum/Fredholm sections pending mathlib updates

### Suspended
- **[Paper 4: Spectral Geometry](Papers/P4_SpectralGeometry/)** ⚠️ **SUSPENDED**
  - Mathematical issues detected in approach
  - Archived code exists (~61 sorries) but not built in CI
  - Work halted pending theoretical resolution

## 🏗️ Project Structure

```
FoundationRelativity/
├── Papers/
│   ├── P1_GBC/                    # 🔧 Paper 1 (rank-one; WIP)
│   ├── P2_BidualGap/              # ✅ Paper 2 (WLPO ↔ BidualGap)
│   └── P3_2CatFramework/          # 3A/3B/3C codebase
│       ├── latex/                     # 📄 ALL LaTeX documents (consolidated)
│       ├── Paper3A_Main.lean          # 📘 Paper 3A aggregator (ACTIVE)
│       ├── Paper3B_Main.lean          # 📙 Paper 3B aggregator (FROZEN)
│       ├── MASTER_DEPENDENCY_CHART.md
│       ├── Phase1-3_*.lean            # 3A framework
│       ├── P3C_DCwAxis/               # 📗 Paper 3C materials (DCω/Baire)
│       ├── P4_Meta/
│       │   ├── ProofTheory/           # ❄️ 3B (21 axioms; frozen)
│       │   ├── StoneWindow_SupportIdeals.lean  # 3A (100+ lemmas)
│       │   ├── FT_UCT_*.lean          # 3A FT axis
│       │   └── DCw_*.lean             # 3C DCω/Baire infrastructure
│       └── documentation/
└── docs/
    ├── planning/
    └── reference/
```

## 🚀 Quick Start

### Prerequisites

• Lean: use the pinned toolchain in `lean-toolchain` (elan will install it)
• Lake (Lean package manager)
• (Optional) mathlib cache: `lake exe cache get` if enabled in this repo

### Build Instructions

```bash
git clone https://github.com/AICardiologist/FoundationRelativity.git
cd FoundationRelativity

# Install pinned Lean toolchain automatically
elan toolchain install $(cat lean-toolchain) || true

# (Optional) get mathlib cache
lake exe cache get || true

# Build per-paper targets (recommended)
lake build Papers.P3_2CatFramework.Paper3A_Main   # Paper 3A: Axiom Calibration Framework (active)
lake build Papers.P3_2CatFramework.Paper3B_Main   # Paper 3B: Proof-Theoretic Scaffold (frozen)

# Optional: build everything (may include archived components)
# lake build
```

### Explore the Results

```bash
# Paper 1: Rank-One (selected modules; WIP)
lake build Papers.P1_GBC.RankOneToggle.ShermanMorrison

# Paper 2: WLPO ↔ Bidual Gap (core equivalence)
lake build Papers.P2_BidualGap.HB.WLPO_to_Gap_HB

# Paper 3A: Axiom Calibration (use aggregator)
lake build Papers.P3_2CatFramework.Paper3A_Main

# Paper 3B: Proof-Theoretic Scaffold (use aggregator)
lake build Papers.P3_2CatFramework.Paper3B_Main

# Paper 4: Spectral Geometry (SUSPENDED; not built in CI)
# See docs for archived paths; building is unsupported at present.
```

**Note**: We recommend building per-paper targets during development. `lake build` builds everything, including archived code, and is not necessary for day-to-day work.

## 📖 Key Theorems

### Paper 1: Rank-One Toggle Kernel
```lean
-- Sherman-Morrison formula for projections (COMPLETE - 0 sorries)
theorem sherman_morrison_proj {α : 𝕜} (hα : (1 : 𝕜) + α ≠ 0) :
    ((ContinuousLinearMap.id 𝕜 H) + α • P).comp (
      (ContinuousLinearMap.id 𝕜 H) - (α / (1 + α)) • P) = 
    ContinuousLinearMap.id 𝕜 H
```

### Paper 2: WLPO ↔ BidualGap
```lean
-- Main equivalence theorem (3 WLPO-conditional sorries)
theorem gap_equiv_wlpo : BidualGapStrong.{0} ↔ WLPO
```

### Paper 3: Axiom Calibration
```lean
-- Bidual gap has uniformization height = 1
theorem gap_has_height_one : uniformization_height gap = 1

-- Orthogonality of axes
axiom ft_independent_of_wlpo : FT ⊬ WLPO
axiom wlpo_independent_of_ft : WLPO ⊬ FT
```

## 📊 Sorry Count Summary

| Component | Sorries | Status | Notes |
|-----------|---------|--------|-------|
| **Paper 3A** | **0** | ✅ **Complete** | **Active development** |
| **Paper 3B** | **0** (21 axioms) | ✅ **Frozen** | **Proof-theoretic limit** |
| **Paper 2** | **3** | ✅ **Main theorem done** | **WLPO-conditional only** |
| **Paper 1** | **~14** | 🔧 **Core complete** | **Pending mathlib updates** |
| **Paper 4** | **~61** | ⚠️ **Suspended** | **Not built in CI** |

## 🤝 Contributing

See [`CONTRIBUTING.md`](docs/CONTRIBUTING.md) for development guidelines.

## 📄 License

This project is licensed under the Apache 2.0 License - see the [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

- Lean 4 development team for the proof assistant
- mathlib4 contributors for the mathematical library
- The constructive mathematics community for foundational insights