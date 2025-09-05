# Paper 5: LaTeX Documents

This directory contains the LaTeX documentation for Paper 5: "Axiom Calibration for General Relativity".

## Files

- **Paper5_GR_AxCal.tex** - Main Paper 5 document: "Axiom Calibration for General Relativity (Paper 5): Empirical Axioms, Computability, and Constructive Profiles with Lean 4 Verification Plan"

## Compilation

The LaTeX file has been prepared to compile without errors:

```bash
cd Papers/P5_NewDirection/latex/
pdflatex Paper5_GR_AxCal.tex
pdflatex Paper5_GR_AxCal.tex  # Run twice for references
```

## Paper Content Overview

This paper applies the AxCal framework from Papers 3A/3B to General Relativity, featuring:

- **GR-specific pin**: Σ₀^GR with manifolds, tensors, Einstein Field Equations
- **Three orthogonal axes**: Choice (AC/DCω/ACω), Compactness/Kinematics (FT/WKL₀), Logic/Computability (WLPO/LEM/MP)
- **Calibration targets (G1-G5)**: From explicit solutions (Height 0) to computable GR evolution
- **Detailed Lean 4 verification plan**: Structural certification with imported axioms
- **Literature integration**: Robb, Reichenbach, Ehlers-Pirani-Schild foundations

## Relationship to Frozen Papers

This paper builds on the complete AxCal ecosystem:
- **Paper 3A**: Core AxCal framework (frozen at `paper3a-freeze-v1.0`)
- **Paper 3B**: Proof-theoretic scaffold (frozen at `paper3b-freeze-v1.0`) 
- **Paper 4**: Quantum spectral patterns (frozen at `paper4-freeze-v1.0`)

The frozen foundation provides stable infrastructure for this new GR direction.