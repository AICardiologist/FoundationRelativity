# Paper 69: The Modularity Theorem is BISH + WLPO

The BCDT Extension Adds No Logical Cost
(Paper 69, Constructive Reverse Mathematics Series)

Author: Paul Chun-Kit Lee, New York University
Date: February 2026

## Overview

This paper extends the constructive reverse mathematics audit of the modularity
theorem from the semistable case (Paper 68) to all elliptic curves over Q
(Breuil-Conrad-Diamond-Taylor 2001). The three BCDT extensions -- Breuil's
classification of finite flat group schemes, the Diamond-Taylor 3-5 switching
argument, and Conrad's local-global compatibility -- are all BISH. The overall
classification remains BISH + WLPO, identical to the semistable case.

### Main Results

| Result | Statement | Strength |
|--------|-----------|----------|
| Theorem A | BCDT extensions (Breuil, 3-5 switch, Conrad) are BISH | BISH |
| Theorem B | Full modularity theorem is BISH + WLPO | BISH + WLPO |
| Theorem C | Zero marginal cost: CRM(BCDT) = CRM(Wiles) = BISH + WLPO | BISH + WLPO |

The key structural observation is that PGL_2(F_3) = S_4 is solvable, so the
icosahedral case (A_5 in PGL_2(F_5)) never arises. Every invocation of
Langlands-Tunnell in the BCDT proof occurs at p = 3.

## Contents

```
zenodo/
  README.md                          This file
  metadata.txt                       Plain-text Zenodo metadata
  LICENSE                            Dual license (Apache 2.0 / CC-BY 4.0)
  paper69.tex                        LaTeX source (13 pages)
  paper69.pdf                        Compiled PDF
  P69_BCDT/
    lean-toolchain                   leanprover/lean4:v4.29.0-rc1
    lakefile.lean                    Lake build configuration
    lake-manifest.json               Mathlib4 dependency lock
    Papers.lean                      Root import file
    Papers/P69_BCDT/
      Paper69_CRMBase.lean           CRM hierarchy, Paper 68 stage defs (120 lines)
      Paper69_Classification.lean    BCDT classification theorems (204 lines)
```

Total: 324 lines of Lean 4, zero sorry, zero warnings, zero errors.

## How to Build (Lean)

Requires Lean 4 (v4.29.0-rc1) and an internet connection for Mathlib download.

```bash
cd P69_BCDT
lake update    # fetch Mathlib4 (first time only)
lake build     # build both files
```

Expected output: Build completed successfully, 0 errors, 0 warnings.

## How to Build (LaTeX)

```bash
pdflatex paper69.tex
pdflatex paper69.tex   # second pass for references
pdflatex paper69.tex   # third pass for TOC
```

## Axiom Inventory

The Paper 69 formalization declares NO opaque types and NO axioms.
All stage classifications are definitional (def), and all theorems
reduce by simp [join]. The CRM hierarchy is a finite inductive type
with decidable equality. All proof obligations are decided by
exhaustive case analysis.

Definitions (from Paper 68 as established results):
- stage1_class = WLPO (Langlands-Tunnell)
- stage2_class = BISH (Deformation ring)
- stage3_class = BISH (Hecke algebra)
- stage4_class = BISH (Numerical criterion)
- stage5_class = BISH (Taylor-Wiles patching)

New definitions (Paper 69):
- breuil_class = BISH (Breuil's finite flat group schemes)
- switch35_class = BISH (Diamond-Taylor 3-5 switch)
- conrad_class = BISH (Conrad's local-global compatibility)

## CRM Series Context

Paper 69 is part of the Constructive Reverse Mathematics program
(Papers 1-69). It completes the CRM audit of the modularity theorem
for GL_2/Q: Paper 68 handled the semistable case; Paper 69 handles the
general case. Together, they establish that the bridge between Galois
representations and automorphic forms has logical cost BISH + WLPO.

## License

Lean 4 code: Apache License 2.0
LaTeX paper and PDF: CC-BY 4.0
Copyright 2026 Paul Chun-Kit Lee

## Acknowledgments

Lean 4 formalization produced using AI code generation (Claude Code)
under human direction. Deep mathematics is due to Wiles, Taylor,
Diamond, Breuil, Conrad, Langlands, Tunnell, and Brochard.
