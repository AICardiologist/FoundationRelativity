# Paper 60: Analytic Rank Stratification of Mixed Motives --- Completing the DPT Framework

**Paper 60 in the Constructive Reverse Mathematics and Arithmetic Geometry Series**

Paul Chun-Kit Lee, New York University (dr.paul.c.lee@gmail.com), February 2026

## Overview

This paper proves two results:

**A. DPT completeness for numerical equivalence** (Theorem 2.1).
The decidability of numerical equivalence on CH*(X) for smooth projective
varieties over Q requires only Axioms 1--3 (Paper 50) plus de Rham
decidability at finite primes (Paper 59). No mixed motive axiom is needed,
because numerical equivalence is a property of the quotient
CH*(X) --> NS*(X), and the extension groups Ext^1 governing the kernel
CH*(X)_hom are invisible to this quotient.

**B. Analytic rank stratification for Ext^1** (Theorem 4.1).
For a motive M over Q possessing the Northcott property, the logical
complexity of computing Ext^1(Q(0), M) is determined by the analytic rank
r = ord_{s=s0} L(M, s):

| r    | Decidability | Mechanism                                                          |
|------|--------------|--------------------------------------------------------------------|
| 0    | BISH         | Ext^1 = 0; verify L(M, s0) != 0 to finite precision               |
| 1    | BISH         | 1-dim regulator; Bloch-Kato + Northcott bound the search           |
| >= 2 | MP           | Covolume cannot bound basis vectors (Minkowski)                    |

The rank >= 2 obstruction is structural (geometry of numbers): lattice
covolumes do not bound individual basis vectors in dimension >= 2.
The only known path to BISH at rank >= 2 is Lang's Height Lower Bound
Conjecture (open).

There is NO Lean formalization for this paper --- it is a purely mathematical
argument (LaTeX and PDF only).

## CRM Classification

- r = 0: BISH
- r = 1: BISH (conditional on Bloch-Kato)
- r >= 2: MP (Markov's Principle)

## How to Open

### LaTeX Paper

The compiled PDF is included (`paper60.pdf`). To recompile:

```bash
pdflatex paper60.tex
pdflatex paper60.tex
```

### Lean Formalization

There is no Lean formalization for this paper. The arguments involve
real-valued L-functions, Arakelov heights, and lattice geometry, which
do not admit the integer arithmetic treatment of Papers 50--59.

## Contents

```
README.md              This file
paper60.tex            LaTeX source
paper60.pdf            Compiled paper (9 pages)
zenodo_metadata.txt    Zenodo upload metadata
CITATION.cff           Citation metadata
```

## Complete Paper List

Papers in the Constructive Reverse Mathematics Series (see Zenodo for current files):

- Paper 1: Withdrawn
- Paper 2: Bidual gap and WLPO -- DOI: 10.5281/zenodo.17107493
- Paper 3: Withdrawn
- Paper 4: Quantum spectra axiom calibration -- DOI: 10.5281/zenodo.17059483
- Paper 5: Schwarzschild curvature verification -- DOI: 10.5281/zenodo.18489703
- Paper 6: Heisenberg uncertainty (v2, CRM over Mathlib) -- DOI: 10.5281/zenodo.18519836
- Paper 7: Physical bidual gap, trace-class operators -- DOI: 10.5281/zenodo.18527559
- Paper 8: 1D Ising model and LPO -- DOI: 10.5281/zenodo.18516813
- Paper 9: Ising formulation-invariance -- DOI: 10.5281/zenodo.18517570
- Paper 10: Logical geography of mathematical physics -- DOI: 10.5281/zenodo.18580342
- Paper 11: Entanglement, CHSH, Tsirelson bound -- DOI: 10.5281/zenodo.18527676
- Paper 12: Constructive history of mathematical physics -- DOI: 10.5281/zenodo.18581707
- Paper 13: Event horizon as logical boundary -- DOI: 10.5281/zenodo.18529007
- Paper 14: Quantum decoherence -- DOI: 10.5281/zenodo.18569068
- Paper 15: Noether theorem -- DOI: 10.5281/zenodo.18572494
- Paper 16: Technical note: Born rule -- DOI: 10.5281/zenodo.18575377
- Paper 17: Bekenstein-Hawking formula -- DOI: 10.5281/zenodo.18597306
- Paper 18: Yukawa RG constructive stratification -- DOI: 10.5281/zenodo.18626839
- Paper 19: WKB tunneling and LLPO -- DOI: 10.5281/zenodo.18602596
- Paper 20: Observable-dependent logical cost, 1D Ising magnetization and WLPO -- DOI: 10.5281/zenodo.18603079
- Paper 21: Bell nonlocality and LLPO -- DOI: 10.5281/zenodo.18603251
- Paper 22: Markov's Principle and radioactive decay -- DOI: 10.5281/zenodo.18603503
- Paper 23: Fan Theorem and optimization -- DOI: 10.5281/zenodo.18604312
- Paper 24: Kochen-Specker contextuality and LLPO -- DOI: 10.5281/zenodo.18604317
- Paper 25: Choice axis (CC, DC) and ergodic theorems -- DOI: 10.5281/zenodo.18615453
- Paper 26: Bidual gap arithmetic route, WLPO -- DOI: 10.5281/zenodo.18615457
- Paper 27: Bell angle optimisation via IVT, LLPO -- DOI: 10.5281/zenodo.18615459
- Paper 28: Newton vs. Lagrange vs. Hamilton -- DOI: 10.5281/zenodo.18616620
- Paper 29: Fekete's Subadditive Lemma and LPO
- Paper 60: Analytic rank stratification of mixed motives -- This paper

## License

This work is part of the Constructive Reverse Mathematics series.
CC-BY-4.0.
