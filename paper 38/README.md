# Paper 38: Wang Tiling and the Origin of Physical Undecidability (Berger's Theorem Is LPO)

**Paper 38 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

DOI: [10.5281/zenodo.18642804](https://doi.org/10.5281/zenodo.18642804)

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
| `genealogy_theorem` | All 7 physical undecidabilities factor through Wang tiling | LPO |
| `sigma1_ceiling` | Sigma-1-zero is the ceiling for physical undecidability | -- |

**Note on Watson-Cubitt exclusion:** Watson-Cubitt (2022) ground state energy
density is a QMA-hardness (complexity) result for finite lattices, not an
undecidability result. The ground state energy at finite volume is a
BISH-computable finite eigenvalue problem (Paper 37). Earlier versions of this
paper incorrectly included it in the genealogy; this has been corrected.

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

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` plus
explicitly cited bridge axioms.

**Bridge axioms:**

| Axiom | Content |
|-------|---------|
| `wang_tileset` | Berger-Robinson encoding M -> W(M) |
| `br_encoding_computable` | Encoding is computable |
| `br_tiles_iff_not_halts` | W(M) tiles <-> M does not halt |
| `br_aperiodic_of_not_halts` | Not halts -> tiles aperiodically |
| `has_valid_patch` / `has_valid_patch_decidable` | Finite patch checking (BISH) |
| `tiling_compactness` | Konig's lemma (compactness bridge) |
| `no_patch_seq_spec` / `no_patch_seq_false_spec` | Blocking sequence specs |
| `tm_from_seq` / `tm_from_seq_halts` | Sequence-to-TM encoding |
| `halting_problem_undecidable` | Halting problem |
| `aperiodic_encoded_iff_all_false` | Aperiodicity encoding |

**Zero sorry.**

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
    Defs.lean              139 lines     Wang tile, tiling, LPO definitions
    BridgeLemmas.lean       81 lines     Berger-Robinson encoding axioms
    TilingDecision.lean     76 lines     Theorem 1: tiling decision <-> LPO
    Aperiodicity.lean       71 lines     Theorem 2: aperiodicity <-> LPO
    Genealogy.lean          80 lines     Theorem 3: undecidability genealogy (7 entries)
    Ceiling.lean            65 lines     Theorem 4: Sigma-1-zero ceiling
    Main.lean               65 lines     Master theorem + axiom audit
```

7 Lean source files, 577 lines total.

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
