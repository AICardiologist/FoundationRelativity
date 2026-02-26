# Paper 77: Automated De-Omniscientisation — Reverse-Engineering Classical Proofs via DAG Surgery

**Paper 77, Constructive Reverse Mathematics Series**

Author: Paul Chun-Kit Lee (NYU)
Date: February 2026
DOI: [10.5281/zenodo.18779210](https://doi.org/10.5281/zenodo.18779210)

## Summary

This paper introduces the **CRMLint Squeeze**, a systematic protocol for reverse-engineering classical proofs into constructive ones. The method identifies the Classical Boundary Node (CBN) — the exact lemma where a classical proof invokes an omniscience principle — excises it, and replaces it with an explicit algebraic witness verified by compiled rational arithmetic (`native_decide`).

## Main Results

| Result | Statement | CRM Level |
|--------|-----------|-----------|
| **Theorem A** | No exotic Weil classes on E^4 (dim Hodge = dim div. products = 36) | BISH |
| **Theorem B** | Complete Constructive Hodge Theorem: all 36 Hodge basis vectors decomposed into explicit Q-linear combinations of cup products, verified by `native_decide` | BISH |
| **Theorem C** | CRMLint Squeeze Protocol: Scaffold -> X-Ray -> Excise -> Squeeze | Methodological |

## Contents

```
paper 77/
  paper77.tex                        LaTeX source
  paper77.pdf                        Compiled PDF
  README.md                          This file
  metadata.txt                       Zenodo metadata
  solve_hodge.py                     Main computation + Lean emission
  emit_lean.py                       Sparse re-emitter
  compute_cm.py                      Original CM diagonalisation
  hodge_data.json                    Intermediate computation data
  P77_DAGSurgery/
    lean-toolchain                   leanprover/lean4:v4.29.0-rc2
    lakefile.lean                    Lake build configuration
    Papers.lean                      Root import file
    Papers/P77_DAGSurgery/
      HodgeBasisData.lean            798 lines, auto-generated (36 decompositions)
      Paper77_CMFourfold.lean        CRM metadata, CM defs, classical axiom (unused)
```

## How to Build (Lean)

Requires Lean 4 (v4.29.0-rc2) and an internet connection for Mathlib download.

```bash
cd P77_DAGSurgery
lake update    # fetch Mathlib4 (first time only)
lake build     # 3121 jobs; ~15s for project files after Mathlib cache
```

**0 sorry. 0 axiom in the constructive path. 0 noncomputable.**

## How to Build (LaTeX)

```bash
pdflatex paper77.tex
pdflatex paper77.tex   # second pass for references
```

Output: 16 pages, 0 errors.

## How to Run the Computation (Python)

```bash
python3 solve_hodge.py    # Full computation + Lean emission
python3 emit_lean.py      # Re-emit with sparse encoding (if needed)
```

Requires Python 3.9+ (standard library only: `fractions`, `itertools`, `json`).

## Axiom Inventory

| Axiom | CRM Level | Used by constructive path? | Role |
|-------|-----------|---------------------------|------|
| `hodge_conjecture_H22_existence` | CLASS | No | CBN (deliberately excised) |
| `propfunext` | Infrastructure | Yes | Lean kernel primitive |
| `Quot.sound` | Infrastructure | Yes | Lean kernel primitive |

`Classical.choice` does NOT appear in `#print axioms` for any of the 36 constructive theorems.

## Key Technical Innovation: Asymmetric Offloading

Python CAS computes exact Q-linear algebra -> emits Lean 4 source with hardcoded rational defs -> Lean kernel verifies via `native_decide`. The sparse match encoding reduces the emitted file from 6020 lines to 798 lines.

## Series Context

Paper 77 continues the diagnostic-to-generative pipeline:
- **Paper 75:** Conservation gap detection (Genestier-Lafforgue LLC calibration)
- **Paper 76:** CRMLint automated analysis
- **Paper 77:** Automated constructivisation (this paper)

Future targets:
- Paper 78: Explicit Local Langlands for wildly ramified representations
- Paper 79: Standard Conjecture D for simple CM abelian fourfolds

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)
Copyright 2026 Paul Chun-Kit Lee

## Acknowledgments

Lean 4 formalization and Python computation produced using AI code generation
(Claude Code) under human direction. Deep mathematics is due to Anderson, Weil,
Hodge, Lieberman, and the arithmetic geometry community.
