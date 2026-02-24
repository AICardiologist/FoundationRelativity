# Paper 70: The Archimedean Principle

**Why Physics and Number Theory Share a Logical Architecture**

Paper 70, Constructive Reverse Mathematics Series

## Overview

This capstone paper identifies a single structural principle underlying 70 papers of Constructive Reverse Mathematics: the real numbers are the sole source of logical difficulty in mathematical physics and arithmetic geometry. The mechanism is u(R) = infinity, and three fields independently exploit it via the same architecture.

## Contents

- `paper70.tex` — LaTeX source (16 pages, 2 figures)
- `paper70.pdf` — Compiled PDF
- `P70_Archimedean/` — Lean 4 + Mathlib formalization (545 lines, 0 sorry, 0 errors)
- `metadata.txt` — Zenodo metadata

## Lean 4 Formalization

Six modules, zero sorry, zero custom axioms for core theorems:

| File | Lines | Content |
|------|-------|---------|
| `Defs.lean` | 104 | CRM hierarchy, descent types, domain profiles |
| `WeilRH.lean` | 47 | Weil RH from CRM axioms (motivic two-liner) |
| `Ramanujan.lean` | 101 | Automorphic CRM incompleteness (Z-witness) |
| `SpectralGaps.lean` | 92 | Three spectral gaps as Sigma^0_2 + MP gap |
| `ArchimedeanPrinciple.lean` | 150 | DPT assembly + main theorem |
| `Main.lean` | 46 | Root module + #check audit |

## Build

```bash
# Lean
cd P70_Archimedean && lake update && lake build

# LaTeX
pdflatex paper70.tex && pdflatex paper70.tex
```

## Requirements

- Lean: `leanprover/lean4:v4.28.0-rc1`
- Mathlib4 (fetched automatically by `lake update`)

## DOI

https://doi.org/10.5281/zenodo.18750992

## License

- Lean 4 code: Apache-2.0
- LaTeX paper and PDF: CC-BY 4.0

Copyright 2026 Paul Chun-Kit Lee
