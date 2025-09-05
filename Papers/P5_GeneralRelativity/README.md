# Paper 5: Axiom Calibration for General Relativity

## Status: Development Starting

### 📄 LaTeX Document

**Main Paper**: [`latex/Paper5_GR_AxCal.tex`](latex/Paper5_GR_AxCal.tex) - "Axiom Calibration for General Relativity (Paper 5): Empirical Axioms, Computability, and Constructive Profiles with Lean 4 Verification Plan"

See [`latex/README.md`](latex/README.md) for compilation instructions.

**Development Start**: September 2025  
**Current Phase**: Planning and initial development

## Overview

Paper 5 represents a new direction in the Axiom Calibration (AxCal) framework, building on the complete foundational work from Papers 1-4:

- **Paper 1**: Rank-One Toggle Kernel (core complete, 4 sorries) ❄️ `paper1-freeze-v1.0`
- **Paper 2**: WLPO ↔ Bidual Gap (main theorem complete, 3 conditional sorries) ❄️ `paper2-freeze-v1.0`  
- **Paper 3A**: AxCal Framework (complete, 0 sorries) ❄️ `paper3a-freeze-v1.0`
- **Paper 3B**: Proof-Theoretic Scaffold (complete, 21 axioms) ❄️ `paper3b-freeze-v1.0`
- **Paper 4**: Quantum Spectra AxCal (complete, 0 sorries, Zenodo archived) ❄️ `paper4-freeze-v1.0`

## Inherited Infrastructure

Paper 5 has access to the complete AxCal framework:

### From Paper 3A (AxCal Framework)
- Three orthogonal axes: WLPO, FT, DCω
- Uniformization height theory
- Stone Window API with 100+ Boolean algebra lemmas
- Complete 2-categorical foundation structure

### From Paper 3B (Proof Theory)  
- Stage-based ladder system
- 21 axioms representing proof-theoretic limits
- RFN_Σ₁ → Con schematic proof
- Collision theory framework

### From Paper 4 (Quantum Applications)
- S0-S4 spectral calibrations
- Profile algebra and composition laws
- Markov's Principle (MP) integration
- Advanced certificate system

## Development Goals

Paper 5 applies the AxCal framework to General Relativity:

### Research Direction
- **GR Pin**: Manifolds, tensors, Einstein Field Equations (Σ₀^GR)
- **Three Orthogonal Axes**: 
  - Choice (AC/DCω/ACω)
  - Compactness/Kinematics (FT/WKL₀)
  - Logic/Computability (WLPO/LEM/MP)
- **Calibration Targets (G1-G5)**:
  - G1: Explicit solutions (Height 0)
  - G2: Cauchy problem (MGHD)  
  - G3: Singularity theorems
  - G4: Maximal extensions
  - G5: Computable GR evolution

### Verification Strategy
- **Schematic Lean layer**: Structural height certification
- **Imported axioms**: Heavy GR mathematics via verification ledger
- **Targeted formalization**: G1 (Schwarzschild vacuum check)

## Build Commands

```bash
# Paper 5 development target (when implemented)
lake build Papers.P5_NewDirection.Main

# Inherited infrastructure available
lake build Papers.P3_2CatFramework.Paper3A_Main  # AxCal framework
lake build Papers.P4_SpectralGeometry.Smoke      # Quantum spectra patterns
```

## Structure

```
P5_NewDirection/
├── README.md                    # This file
├── Main.lean                    # Entry point (TBD)
└── [To be defined]
```

## Connection to Previous Work

Paper 5 leverages the complete AxCal ecosystem:
- **Calibration methodology** from Papers 3A/3B
- **Operational examples** from Papers 1, 2, 4
- **Proof-theoretic boundaries** established in 3B
- **Implementation patterns** proven in 4

The frozen state of Papers 1-4 provides a stable foundation for new research directions.