# Paper 62: The Hodge Level Boundary — Archimedean Decidability for Mixed Motives

**Constructive Reverse Mathematics Series**

Paul C.-K. Lee (NYU), February 2026

DOI: [10.5281/zenodo.18736965](https://doi.org/10.5281/zenodo.18736965)

## Overview

This paper (a merge of original Papers 62 and 63) identifies the sharp
boundary between Markov's Principle (MP) and the Limited Principle of
Omniscience (LPO) for decidability of Ext^1(Q(0), M) in the category of
mixed motives.  The boundary is the Hodge level l of the motive M.

When l <= 1, the intermediate Jacobian J^p is an abelian variety, the
Northcott property transfers via the Abel-Jacobi map, and decidability
requires at most MP.  When l >= 2, the intermediate Jacobian is a
non-algebraic complex torus, Northcott fails, and decidability escalates
to LPO.

The main novelty is the proof that no intermediate condition ("weak
Northcott") prevents this escalation: each degree-d slice of the cycle
space is BISH-decidable, but quantifying over all degrees requires LPO.

Combined with Papers 59-61, the full Decidable Polarized Tannakian (DPT) hierarchy for mixed motives is
governed by three invariants: analytic rank r, Hodge level l, and the
effective Lang constant c.

## Main Results

| Theorem | Statement |
|---------|-----------|
| A (Algebraic Case) | l <= 1 => J^p algebraic => MP suffices |
| B (Non-Algebraic Case) | l >= 2 => J^p non-algebraic => LPO required |
| C (Four-Way Equivalence) | Algebraic <-> Gap <-> Northcott <-> MP |
| D (Isolation Gap) | Gap geometry characterizes the boundary |
| E (No Weak Northcott) | LPO <-> deciding saturation for all graded cycle spaces |

### Concrete Examples:

| Motive | Hodge level | Logic |
|--------|-------------|-------|
| Elliptic curve E/Q | 1 | MP |
| Cubic threefold | 1 | MP |
| K3 surface (divisors) | 0 | MP |
| Quintic CY3 | 3 | LPO |

## Repository Contents

```
README.md                                This file
CITATION.cff                             Citation metadata
.zenodo.json                             Zenodo upload metadata
paper62.tex                              LaTeX source (14 pages)
paper62.pdf                              Compiled paper

P62_NorthcottLPO/                        Lean 4 formalization — Bundle 1
                                         (original Paper 62: Northcott boundary)
  lakefile.lean                          Package configuration
  lean-toolchain                         leanprover/lean4:v4.29.0-rc1
  Papers.lean                            Root import
  lake-manifest.json                     Dependency lock file
  Papers/P62_NorthcottLPO/
    Defs.lean                            LPO, MP, Northcott, Hodge level, AJ target (121 lines)
    NorthcottTransfer.lean               Theorem A: abelian target -> Northcott (105 lines)
    NorthcottFailure.lean                Theorem B: CY3 -> Northcott fails (110 lines)
    NoWeakNorthcott.lean                 Theorem C: LPO reduction (main result) (139 lines)
    HodgeBoundary.lean                   Theorem D: sharp boundary + examples (141 lines)
    IsolationGap.lean                    Theorem E: isolation gap duality (155 lines)
    Main.lean                            Summary, hierarchy, axiom audit (183 lines)
  7 files, 954 lines total.

P62_HodgeLevelBoundary/                  Lean 4 formalization — Bundle 2
                                         (original Paper 63: intermediate Jacobian
                                          obstruction and four-way equivalence)
  lakefile.lean                          Package configuration
  lean-toolchain                         leanprover/lean4:v4.29.0-rc1
  Papers.lean                            Root import
  lake-manifest.json                     Dependency lock file
  Papers/P62_HodgeLevelBoundary/
    Basic.lean                           Definitions and Hodge structures (181 lines)
    IntermediateJacobian.lean            Intermediate Jacobian construction (84 lines)
    AbelJacobi.lean                      Abel-Jacobi map properties (64 lines)
    AlgebraicCase.lean                   Theorem A: algebraic J^p => MP (110 lines)
    NonAlgebraicCase.lean                Theorem B: non-algebraic J^p => LPO (211 lines)
    Equivalence.lean                     Theorem C: four-way equivalence (97 lines)
    IsolationGap.lean                    Theorem D: isolation gap geometry (167 lines)
    NoWeakNorthcott.lean                 Theorem E: no weak Northcott (125 lines)
    Classification.lean                  Motive classification (104 lines)
    Main.lean                            Summary and axiom audit (224 lines)
  10 files, 1367 lines total.
```

**Note:** This paper merges the results of original Papers 62 and 63.
Both Lean bundles are included to preserve reproducibility of the two
originally separate formalizations.  Bundle 1 (P62_NorthcottLPO) covers
the Northcott boundary and No Weak Northcott theorem.  Bundle 2
(P62_HodgeLevelBoundary) covers the intermediate Jacobian obstruction,
the four-way equivalence, and the full classification.

## How to Build

### LaTeX

```bash
pdflatex paper62
pdflatex paper62
```

### Lean 4

Both bundles build independently.  Prerequisites: Lean 4 (v4.29.0-rc1)
and `lake`.

```bash
cd P62_NorthcottLPO
lake build    # 0 errors, 0 warnings, 0 sorry

cd ../P62_HodgeLevelBoundary
lake build    # 0 errors, 0 warnings, 0 sorry
```

First build downloads Mathlib (~30-60 min).  Subsequent builds are fast.

## Axiom Audit

**Three custom axioms** (all classical results from the literature):

1. `neronTate_northcott` -- Neron-Tate height satisfies Northcott on abelian varieties (Neron 1965, Northcott 1949)
2. `mumford_infinite_dim` -- Mumford's infinite-dimensionality theorem (Mumford 1969)
3. `baker_lower_bound` -- Baker's theorem on linear forms in logarithms (Baker 1966)

Infrastructure axioms: `propext`, `Classical.choice` (Mathlib's R infrastructure), `Quot.sound`.

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)
