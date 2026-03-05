# Paper 38: Wang Tiling and the Origin of Physical Undecidability (Berger's Theorem Is LPO)

**Paper 38 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

## Overview

Every undecidability result in quantum many-body physics descends from the
undecidability of Wang tiling (Berger 1966). This paper establishes that Wang
tiling itself is Turing-Weihrauch equivalent to LPO, proving that the entire
genealogy of physical undecidability --- from Berger through Cubitt --- lives at
a single logical stratum.

The key insight is the Sigma-1-zero ceiling: all physical constructions reduce
to halting (which is Sigma-1-zero-complete), so Wang tiling and all its
descendants cost exactly LPO.

## Main Results

| Theorem | Statement | Level |
|---------|-----------|-------|
| `wang_tiling_iff_lpo` | Wang tiling decision <-> LPO | LPO |
| `aperiodicity_iff_lpo` | Aperiodicity detection <-> LPO | LPO |
| `genealogy_theorem` | All physical undecidabilities factor through Wang tiling | LPO |
| `sigma1_ceiling` | Sigma-1-zero is the ceiling for physical undecidability | -- |

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper38.pdf`). To recompile:

```bash
pdflatex paper38.tex
pdflatex paper38.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [elan](https://github.com/leanprover/elan) (Lean version
manager) and ensure `lake` is available. Requires ~8 GB disk space for Mathlib cache.

```bash
cd P38_WangTiling
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 38 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

## Contents

```
README.md                                This file
paper38.tex                              LaTeX source
paper38.pdf                              Compiled paper
P38_WangTiling/                          Lean 4 formalization
  lakefile.lean                          Package configuration
  lean-toolchain                         leanprover/lean4:v4.28.0-rc1
  Papers.lean                            Root import
  Papers/P38_WangTiling/
    Defs.lean                            Wang tile, tiling, LPO definitions
    TilingDecision.lean                  Tiling decision <-> LPO
    Aperiodicity.lean                    Aperiodicity detection <-> LPO
    BridgeLemmas.lean                    Physics bridge axioms
    Ceiling.lean                         Sigma-1-zero ceiling theorem
    Genealogy.lean                       Undecidability genealogy
    Main.lean                            Master theorem
```

7 Lean source files.

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
