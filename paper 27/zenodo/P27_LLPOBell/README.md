# Paper 27: The Logical Cost of Root-Finding

**LLPO, the Intermediate Value Theorem, and Bell Angle Optimization -- A Lean 4 Formalization**

## Overview

This paper formalizes the connection between:
- **LLPO** (Lesser Limited Principle of Omniscience)
- **IVT** (Intermediate Value Theorem)
- **Bell angle optimization** for general quantum states

The main result is a three-level stratification:
1. **BISH**: CHSH bound and specific-angle violations are computable.
2. **LLPO**: Finding general optimal measurement angles requires IVT.
3. **Hierarchy**: WLPO -> LLPO strictly, so angle-finding is strictly easier than gap detection (Paper 26).

## Key Results

| Theorem | Statement |
|---------|-----------|
| `llpo_iff_exactIVT` | LLPO <-> ExactIVT (Bridges-Richman 1987) |
| `llpo_finds_crossing` | LLPO -> threshold crossing angles findable |
| `angle_stratification` | Three-level stratification theorem |
| `mechanism_explanation` | Connecting Paper 21 to IVT |
| `S_quantum_gt_two` | 2*sqrt(2) > 2 (quantum violation exceeds classical) |

## Module Structure

```
Papers/P27_LLPOBell/
  Basic.lean            -- LLPO, WLPO, LPO, hierarchy proofs
  IVT.lean              -- ExactIVT, ApproxIVT, generalized IVT
  BellCorrelation.lean  -- Continuous correlations, CHSH, singlet
  AngleFinding.lean     -- IVT instances, threshold crossings
  Calibration.lean      -- Calibration chain, stratification
  Main.lean             -- Aggregator, axiom audit
```

## Build

```bash
lake update
lake build
```

Requires `leanprover/lean4:v4.28.0-rc1` (see `lean-toolchain`).

## Axiom Audit

6 custom axioms, all with published citations:

| Axiom | Citation |
|-------|----------|
| `exact_ivt_iff_llpo` | Bridges-Richman 1987, Ishihara 1989 |
| `llpo_real_sign` | Ishihara 2006 |
| `classical_chsh_bound` | Paper 21 (discrete); axiomatized for continuous |
| `singlet_violates` | Tsirelson bound; Paper 11 (matrix form) |
| `chsh_slice_sign_change` | Physical: continuous angle interpolation |
| `chsh_slice_neg_sign_change` | Symmetric negative version |

**Sorry count: 0**

The main theorem `paper27_main` depends on 3 of these: `exact_ivt_iff_llpo`, `singlet_violates`, `chsh_slice_sign_change`.

## Connection to Other Papers

- **Paper 21**: Proved LLPO <-> BellSignDecision (abstract sign encoding). Paper 27 explains the *mechanism*: IVT is why LLPO appears.
- **Paper 26**: Proved gap detection in bidual quotient calibrates at WLPO. Paper 27 shows angle-finding calibrates one level lower at LLPO.
- **Paper 11**: Proved quantum CHSH violation in matrix form. Paper 27 uses the continuous formulation.

## LaTeX Paper

```bash
pdflatex paper27_llpo_bell.tex
pdflatex paper27_llpo_bell.tex  # second pass for references
```

Produces `paper27_llpo_bell.pdf` (8 pages).

## Author

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com)

AI-assisted formalization (Claude, Anthropic).

DOI: [10.5281/zenodo.18615459](https://doi.org/10.5281/zenodo.18615459)
