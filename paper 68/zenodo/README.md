# Paper 68: Fermat's Last Theorem is BISH

A Constructive Reverse Mathematics Audit
(Paper 68, Constructive Reverse Mathematics Series)

Author: Paul Chun-Kit Lee, New York University
Date: February 2026
DOI: 10.5281/zenodo.18749965

## Overview

This paper performs a stage-by-stage constructive reverse mathematics (CRM)
audit of Wiles's proof of Fermat's Last Theorem. There are two main findings:

**Finding 1 (Asymmetry).** Stages 2–5 of Wiles's proof are fully constructive
(BISH), while Stage 1 (Langlands–Tunnell) requires WLPO. The non-constructive
content is concentrated entirely at the entry point.

**Finding 2 (Bypass).** The WLPO is eliminable. The 21st-century proof route
(Kisin 2009, Khare–Wintenberger 2009) replaces Wiles's p = 3 base case
(octahedral, trace formula, WLPO) with a p = 2 base case (dihedral, Hecke
theta series, BISH). An equivalent bypass uses potential modularity
(Taylor, Buzzard–Taylor).

**Main result:**

    CRM(FLT) = BISH

The WLPO in Wiles's original argument was the cost of a specific proof
strategy (the choice of p = 3), not a property of the theorem. The community
unknowingly produced a constructive proof of Fermat's Last Theorem.

### Main Results

| Result | Statement | Strength |
|--------|-----------|----------|
| Theorem A | Stage 5 (Taylor-Wiles patching) is BISH | BISH |
| Theorem B | Stages 2–4 (deformation ring, Hecke algebra, numerical criterion) are BISH | BISH |
| Theorem C | Stage 1 (Langlands–Tunnell) requires WLPO | WLPO |
| Theorem D | Asymmetry: Wiles's proof is BISH + WLPO, localised in Stage 1 | BISH + WLPO |
| Theorem E | Bypass: Kisin/Khare–Wintenberger route is BISH throughout | BISH |
| Corollary | CRM(FLT) = BISH | BISH |

The Stage 5 classification exploits Brochard's proof of de Smit's conjecture
(2017), which eliminates the Fan Theorem, and unconditional effective
Chebotarev bounds (LMO 1979, Ahn–Kwon 2019), which make the Taylor–Wiles
prime search a bounded computation.

## Contents

```
zenodo/
  README.md                          This file
  metadata.txt                       Plain-text Zenodo metadata
  paper68.tex                        LaTeX source (18 pages)
  paper68.pdf                        Compiled PDF
  P68_WilesFLT/
    lean-toolchain                   leanprover/lean4:v4.29.0-rc1
    lakefile.lean                    Lake build configuration
    lake-manifest.json               Mathlib4 dependency lock
    Papers.lean                      Root import file
    Papers/P68_WilesFLT/
      Paper68_Axioms.lean            Opaque types, axioms B1-B3, CRM hierarchy (132 lines)
      Paper68_Stage5.lean            Target 1: Stage 5 is BISH (178 lines)
      Paper68_Asymmetry.lean         Target 2: Asymmetry Theorem (183 lines)
```

Total: 493 lines of Lean 4, zero sorry, zero warnings, zero errors.

## How to Build (Lean)

Requires Lean 4 (v4.29.0-rc1) and an internet connection for Mathlib download.

```bash
cd P68_WilesFLT
lake update    # fetch Mathlib4 (first time only)
lake build     # build all three files
```

Expected output: Build completed successfully, 0 errors, 0 warnings.

## How to Build (LaTeX)

```bash
pdflatex paper68.tex
pdflatex paper68.tex   # second pass for references
```

## Axiom Inventory

12 opaque declarations (types and properties) + 8 theorem-level axioms.
Deep theorems are axiomatized with literature references; Lean verifies
the logical assembly only.

Load-bearing axioms:
- B1: Brochard's finite-level criterion (Compositio Math. 2017)
- B2: Effective Chebotarev (LMO 1979; Ahn-Kwon 2019)

Documentation axiom:
- B3: Discriminant computability (standard ANT)

Bridge axioms (4-8): twConjClass, frob_implies_tw_conditions,
construct_patching_data, patching_data_valid, patching_data_edim.

## CRM Series Context

Paper 68 is part of the Constructive Reverse Mathematics program
(Papers 1–68). It establishes that FLT, a Π⁰₁ sentence about natural
numbers, has a BISH proof — consistent with the CRM thesis that logical
cost is intrinsic to theorems, not to proofs. The de-omniscientizing
descent of Stage 5 (MP + FT → BISH over 1995–2017) parallels patterns
identified in Paper 50 (atlas survey).

## License

Lean 4 code: Apache License 2.0
LaTeX paper and PDF: CC-BY 4.0
Copyright 2026 Paul Chun-Kit Lee

## Acknowledgments

Lean 4 formalization produced using AI code generation (Claude Code)
under human direction. Deep mathematics is due to Wiles, Taylor,
Diamond, Langlands, Tunnell, Kisin, Khare, Wintenberger, Brochard,
Hecke, and Lagarias–Odlyzko.
