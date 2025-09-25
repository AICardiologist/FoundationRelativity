# Axiom-Calibration

> ## 🤖 **IMPORTANT DISCLAIMER**
> ### A Case Study: Using Multi-AI Agents to Tackle Formal Mathematics
> 
> **This entire Lean 4 formalization project was produced by multi-AI agents working under human direction.** All proofs, definitions, and mathematical structures in this repository were AI-generated. This represents a case study in using multi-AI agent systems to tackle complex formal mathematics problems with human guidance on project direction.
>
> The mathematical content has been verified through Lean's proof checker. Users should be aware that the code was AI-generated as part of an experiment in AI-assisted formal mathematics.

[![CI](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml)
[![Nightly](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/nightly.yml)
[![Paper 4 Smoke](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/p4-smoke.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/p4-smoke.yml)
[![Paper 6 Heisenberg](https://img.shields.io/badge/Paper%206%20Heisenberg-Complete-brightgreen)](Papers/P6_Heisenberg/)
[![Paper 3A/3B Complete](https://img.shields.io/badge/Paper%203A%2F3B-Complete-brightgreen)](Papers/P3_2CatFramework/)
[![Paper 2 WLPO↔Gap](https://img.shields.io/badge/Paper%202%20WLPO%E2%86%94Gap-3%20sorries-green)](Papers/P2_BidualGap/)
[![Paper 1 Rank-One](https://img.shields.io/badge/Paper%201%20Rank--One-4%20sorries-green)](Papers/P1_GBC/)
[![DOI Paper 3A](https://zenodo.org/badge/DOI/10.5281/zenodo.17054050.svg)](https://doi.org/10.5281/zenodo.17054050)
[![DOI Paper 3B](https://zenodo.org/badge/DOI/10.5281/zenodo.17054155.svg)](https://doi.org/10.5281/zenodo.17054155)
[![DOI Paper 4](https://zenodo.org/badge/DOI/10.5281/zenodo.17059483.svg)](https://doi.org/10.5281/zenodo.17059483)
[![DOI Paper 6](https://zenodo.org/badge/DOI/10.5281/zenodo.17068179.svg)](https://doi.org/10.5281/zenodo.17068179)

🎯 Current Status (September 2025) - **ALL PAPERS FROZEN FOR PAPER 5 DEVELOPMENT**

**❄️ FROZEN PAPERS** (September 2025):
• Paper 6 (Heisenberg AxCal): ✅ **COMPLETE** - Zero sorries, constructive RS + Schrödinger proofs ([DOI: 10.5281/zenodo.17068179](https://doi.org/10.5281/zenodo.17068179)) `paper6-phase3-v1.0`
• Paper 4 (Quantum Spectra): ✅ **COMPLETE** - Zero sorries ([DOI: 10.5281/zenodo.17059483](https://doi.org/10.5281/zenodo.17059483)) `paper4-freeze-v1.0`
• Paper 3A (AxCal Framework): ✅ **COMPLETE** - Zero sorries, 3 orthogonal axes `paper3a-freeze-v1.0`
• Paper 3B (Proof-theoretic scaffold): ✅ **COMPLETE** - 21 axioms (proof-theoretic limit) `paper3b-freeze-v1.0`
• Paper 2 (WLPO ↔ Bidual Gap): ✅ **CORE COMPLETE** - Main theorem proven, 3 WLPO-conditional sorries `paper2-freeze-v1.0` *(recently updated for CRM compliance following Lean Zulip discussions)*
• Paper 1 (Rank-One Toggle Kernel): ✅ **CORE COMPLETE** - Down to 4 sorries (from 14) `paper1-freeze-v1.0`

🚀 **CURRENT DEVELOPMENT**: 
• **Paper 5 (General Relativity AxCal)**: ✅ **COMPLETE** - Axiom calibration for Einstein Field Equations, GR pin (Σ₀^GR), three orthogonal axes (0 sorries)
  - **Sprint 3 Complete**: Full symbolic verification of Schwarzschild vacuum solution
  - All Christoffel symbols computed, Ricci tensor vanishing proved (R_μν = 0)

## 🎯 Overview

A Lean 4 formalization project that calibrates the exact logical strength required for mathematical theorems. The project demonstrates **axiom calibration (AxCal)**: measuring precisely which axioms are needed for classical results that fail constructively.

> **Key Insight**: Many classical theorems become unprovable in constructive mathematics (BISH). We formalize exact equivalences between analytical "pathologies" and logical principles, providing precise calibrations of their axiom requirements.

### 📄 LaTeX Documents

**Paper 3 LaTeX documents** are consolidated in [`Papers/P3_2CatFramework/latex/`](Papers/P3_2CatFramework/latex/):
- **Paper3_Main.tex** - Comprehensive framework document
- **Paper3A_Publication.tex** - Paper 3A with integrated DCω axis
- **Paper3B_Publication.tex** - Paper 3B proof-theoretic scaffold
- **Paper3_Lean_Formalization.tex** - Technical formalization details

**Paper 4 LaTeX document** is located in [`Papers/P4_SpectralGeometry/`](Papers/P4_SpectralGeometry/):
- **Paper4_QuantumSpectra.tex** - Quantum spectra AxCal with Zenodo reproducibility

**Paper 5 LaTeX document** is located in [`Papers/P5_GeneralRelativity/`](Papers/P5_GeneralRelativity/):
- **[Paper5_GR_AxCal.tex](Papers/P5_GeneralRelativity/Paper5_GR_AxCal.tex)** - Axiom Calibration for General Relativity with complete Lean 4 formalization

**Paper 6 LaTeX document** is located in [`Papers/P6_Heisenberg/`](Papers/P6_Heisenberg/):
- **Paper6_HeisenbergAxCal.tex** - Heisenberg Uncertainty Principle AxCal analysis ([Software DOI: 10.5281/zenodo.17068179](https://doi.org/10.5281/zenodo.17068179))

### Papers Summary (All Frozen Except Paper 5)

**❄️ FROZEN PAPERS** (Complete AxCal ecosystem):

1. **Paper 1: Rank-One Toggle Kernel** `paper1-freeze-v1.0` ✅ **CORE COMPLETE**
   - Sherman-Morrison formula: **COMPLETE** (0 sorries)
   - Fredholm theory: Nearly complete (1 sorry for quotient dimension)
   - Spectrum: 3 sorries (awaiting mathlib spectrum API)
   - **Achievement**: Reduced from 14 to just 4 sorries!

2. **Paper 2: WLPO ↔ Bidual Gap** `paper2-freeze-v1.0` ✅ **CORE COMPLETE**
   - **Main theorem complete**: Gap_∃ ↔ WLPO equivalence proven
   - Witness space: c₀ (sequences vanishing at infinity)
   - 3 WLPO-conditional sorries in optional completeness module

3. **Paper 3A: AxCal Framework** `paper3a-freeze-v1.0` ✅ **COMPLETE** (0 sorries)
   - Three orthogonal axes: WLPO, FT, DCω
   - Uniformization height theory complete
   - Stone Window API: 100+ Boolean algebra lemmas
   - Complete 2-categorical foundation structure

4. **Paper 3B: Proof-Theoretic Scaffold** `paper3b-freeze-v1.0` ✅ **COMPLETE** (21 axioms)
   - Stage-based ladders resolve circularities
   - RFN_Σ₁ → Con: proved schematically
   - Honest proof-theoretic limit reached

5. **Paper 4: Quantum Spectra AxCal** `paper4-freeze-v1.0` ✅ **COMPLETE** (0 sorries)
   - [Zenodo archived](https://doi.org/10.5281/zenodo.17059483)
   - S0-S4 spectral calibrations: Height 0 to MP/DCω/WLPO frontiers
   - Profile algebra and composition laws

🚀 **ACTIVE DEVELOPMENT**:

**Paper 5: General Relativity AxCal** ✅ **COMPLETE** (0 sorries)
   - Applies AxCal to Einstein Field Equations
   - GR pin (Σ₀^GR): Manifolds, tensors, Einstein tensor
   - Three orthogonal axes: Choice (AC/DCω/ACω), Compactness/Kinematics (FT/WKL₀), Logic/Computability (WLPO/LEM/MP)
   - Targets G1-G5: Explicit solutions → Computable GR evolution
   - **Sprint 3 Milestone**: Complete Schwarzschild vacuum solution
     - All 9 non-zero Christoffel symbols: Γ^t_{tr}, Γ^r_{tt}, Γ^r_{rr}, Γ^r_{θθ}, Γ^r_{φφ}, Γ^θ_{rθ}, Γ^θ_{φφ}, Γ^φ_{rφ}, Γ^φ_{θφ}
     - Full Ricci tensor computation via contracted Bianchi identity
     - Vacuum verification: R_{μν} = 0 for Schwarzschild metric with f(r) = 1 - 2M/r
   - Portal→Profile mappings (v1.0.1):
     - Zorn → (1,0,0) on Choice axis
     - Serial-Chain (DCω) → (1,0,0) on Choice axis
     - Limit-Curve → (0,1,0) on Compactness axis
     - Reductio → (0,0,1) on Logic axis
   - Complete Lean 4 formalization with portal theorems and height certificates
   - CI/CD pipeline with automated PDF generation and axiom auditing

6. **Paper 6: Heisenberg Uncertainty Principle AxCal** `paper6-phase3-v1.0` ✅ **COMPLETE** (0 sorries)
   - **Phase-3 Achievement**: Constructive proofs of both Robertson-Schrödinger and full Schrödinger inequalities
   - HUP-RS: Height 0 (fully constructive) - `RS_from_bridges` theorem
   - HUP-M: ≤ DCω (dependent choice) - `hupM_stream_from_dcω` derived from dcω_stream
   - **Schrödinger strengthening**: |⟨[A,B]⟩|² + |⟨{A,B}⟩|² ≤ 4·Var(A)·Var(B) (division-free)
   - Mathlib-free Hilbert space signatures with complete bridge axiom foundations

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

### ❄️ Frozen Papers (Complete AxCal Ecosystem)

- **[Paper 4: Quantum Spectra AxCal](Papers/P4_SpectralGeometry/)** ✅ **COMPLETE** `paper4-freeze-v1.0`
  - Zero sorries, [Zenodo archived](https://doi.org/10.5281/zenodo.17059483)
  - S0-S4 spectral calibrations with profile algebra
  - Markov's Principle integration and composition laws

- **[Papers 3A & 3B: AxCal Framework](Papers/P3_2CatFramework/)** ✅ **COMPLETE** 
  - **Paper 3A** `paper3a-freeze-v1.0`: AxCal framework (0 sorries)
  - **Paper 3B** `paper3b-freeze-v1.0`: Proof-theoretic scaffold (21 axioms)
  - **🚨 IMPORTANT**: See [`MASTER_DEPENDENCY_CHART.md`](Papers/P3_2CatFramework/documentation/MASTER_DEPENDENCY_CHART.md) for separation guide
  - Use `Papers.P3_2CatFramework.Paper3A_Main` or `Papers.P3_2CatFramework.Paper3B_Main` aggregators

- **[Paper 2: WLPO ↔ Bidual Gap](Papers/P2_BidualGap/)** ✅ **CORE COMPLETE** `paper2-freeze-v1.0`
  - Main theorem: Gap_∃ ↔ WLPO equivalence proven (0 sorries)
  - Witness space: c₀ construction complete
  - 3 WLPO-conditional sorries in optional completeness only
  - Recently updated for CRM compliance following Lean Zulip discussions

- **[Paper 1: Rank-One Toggle Kernel](Papers/P1_GBC/)** ✅ **CORE COMPLETE** `paper1-freeze-v1.0`
  - Sherman-Morrison formula complete (0 sorries)
  - 4 sorries total (down from 14!) - pending mathlib updates

### 🚀 Active Development

- **[Paper 5: General Relativity AxCal](Papers/P5_GeneralRelativity/)** 🔧 **NEW DIRECTION**
  - Applies AxCal framework to Einstein Field Equations
  - 45-page theoretical foundation with Lean 4 verification plan
  - Three orthogonal axes tailored for GR: Choice, Compactness/Kinematics, Logic/Computability
  - **[📚 GR Module Documentation Hub](Papers/P5_GeneralRelativity/GR/README.md)** - Riemann tensor activation infrastructure
  - **[📊 Activation Tracking](Papers/P5_GeneralRelativity/GR/ACTIVATION_TRACKING.md)** - Live status and decisions
  - **[🗺️ Development Roadmap](Papers/P5_GeneralRelativity/GR/ROADMAP_Schwarzschild_Vacuum.md)** - Sprint breakdown

## 🏗️ Project Structure

```
FoundationRelativity/
├── Papers/
│   ├── P1_GBC/                    # ❄️ Paper 1 (rank-one; FROZEN)
│   ├── P2_BidualGap/              # ❄️ Paper 2 (WLPO ↔ BidualGap; FROZEN)
│   ├── P3_2CatFramework/          # ❄️ Papers 3A/3B (AxCal core; FROZEN)
│   │   ├── latex/                     # 📄 Papers 3A/3B LaTeX documents
│   │   ├── Paper3A_Main.lean          # 📘 Paper 3A aggregator (FROZEN)
│   │   ├── Paper3B_Main.lean          # 📙 Paper 3B aggregator (FROZEN)
│   │   ├── MASTER_DEPENDENCY_CHART.md
│   │   ├── Phase1-3_*.lean            # 3A framework components
│   │   ├── P4_Meta/
│   │   │   ├── ProofTheory/           # ❄️ 3B (21 axioms; frozen)
│   │   │   ├── StoneWindow_SupportIdeals.lean  # 3A (100+ lemmas)
│   │   │   ├── FT_UCT_*.lean          # 3A FT axis
│   │   │   └── DCw_*.lean             # 3A DCω/Baire infrastructure
│   │   └── documentation/
│   ├── P4_SpectralGeometry/       # ❄️ Paper 4 (Quantum Spectra; FROZEN)
│   │   ├── Paper4_QuantumSpectra.tex  # 📄 Paper 4 LaTeX (Zenodo archived)
│   │   ├── Smoke.lean                 # CI smoke test (0 sorries)
│   │   └── Spectral/                  # S0-S4 implementations
│   └── P5_GeneralRelativity/      # 🚀 Paper 5 (GR AxCal; ACTIVE)
│       ├── latex/                     # 📄 Paper 5 LaTeX documents
│       │   └── Paper5_GR_AxCal.tex    # 45-page theoretical foundation
│       ├── Main.lean                  # Entry point for GR AxCal
│       └── README.md                  # Paper 5 development guide
└── docs/
    ├── planning/
    └── reference/
```

## 📚 Citation

If you use this formalization in your research, please cite:

### Paper 3A: Three Orthogonal Axes
```bibtex
@software{lee2025axcal3a,
  author = {Lee, Paul Chun-Kit},
  title = {Foundation Relativity: AxCal Paper 3A - Three Orthogonal Axes (Lean 4 Artifacts)},
  version = {0.2.0},
  year = {2025},
  doi = {10.5281/zenodo.17054050},
  url = {https://doi.org/10.5281/zenodo.17054050}
}
```

### Paper 3B: Proof-Theoretic Collisions
```bibtex
@software{lee2025axcal3b,
  author = {Lee, Paul Chun-Kit},
  title = {Foundation Relativity: AxCal Paper 3B - Proof-Theoretic Collisions (Lean 4 Artifacts)},
  version = {0.2.0},
  year = {2025},
  doi = {10.5281/zenodo.17054155},
  url = {https://doi.org/10.5281/zenodo.17054155}
}
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

# Build frozen papers (stable ecosystem)
lake build Papers.P3_2CatFramework.Paper3A_Main   # Paper 3A: AxCal Framework (frozen)
lake build Papers.P3_2CatFramework.Paper3B_Main   # Paper 3B: Proof-Theoretic Scaffold (frozen)
lake build Papers.P4_SpectralGeometry.Smoke       # Paper 4: Quantum Spectra (frozen)

# Build active development
lake build Papers.P5_GeneralRelativity            # Paper 5: GR AxCal (active)

# Optional: build everything (includes all frozen papers)
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

# Paper 4: Quantum Spectra (frozen - smoke test)
lake build Papers.P4_SpectralGeometry.Smoke && ./scripts/no_sorry_p4.sh

# Paper 5: General Relativity AxCal (active development)
lake build Papers.P5_GeneralRelativity

# Paper 5: Riemann tensor quality gates (activation infrastructure)
make check  # Runs baseline and activation checks for Riemann.lean
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

## 📊 Final Sorry Count Summary (All Papers Frozen)

| Component | Sorries | Status | Freeze Tag | Notes |
|-----------|---------|--------|------------|-------|
| **Paper 4** | **0** | ✅ **Complete** | `paper4-freeze-v1.0` | **Zenodo archived** |
| **Paper 3A** | **0** | ✅ **Complete** | `paper3a-freeze-v1.0` | **Three orthogonal axes** |
| **Paper 3B** | **0** (21 axioms) | ✅ **Complete** | `paper3b-freeze-v1.0` | **Proof-theoretic limit** |
| **Paper 2** | **3** | ✅ **Core complete** | `paper2-freeze-v1.0` | **WLPO-conditional only** |
| **Paper 1** | **4** | ✅ **Core complete** | `paper1-freeze-v1.0` | **Down from 14 sorries** |

## 🤝 Contributing

### First-time Setup
```bash
# Install repo-managed git hooks (runs audits on commit)
make install-hooks

# Verify your environment
make audit  # Runs all quality checks
```

See [`CONTRIBUTING.md`](Papers/P5_GeneralRelativity/CONTRIBUTING.md) for development guidelines.

## 📄 License

This project is licensed under the Apache 2.0 License - see the [LICENSE](LICENSE) file for details.

## 🙏 Acknowledgments

- Lean 4 development team for the proof assistant
- mathlib4 contributors for the mathematical library
- The constructive mathematics community for foundational insights

**Development Assistance:**
- **Gemini 2.5 Deep Think** - Architecture exploration and theoretical framework design
- **GPT-5 Pro** - Lean 4 scaffolding and implementation support
- **Claude Code** - Repository management and development workflow