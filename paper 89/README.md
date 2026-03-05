# Paper 89: Absolute Hodge Classes for the Universal Hyperelliptic Weil Locus

**Paper 89 of the Constructive Reverse Mathematics Series**

## Main Results

The exotic Weil class on the Jacobian of the universal genus-4 hyperelliptic Weil family

    C_{a,b,c} : y^2 = x^9 + ax^7 + bx^5 + cx^3 + x

is a **global flat section** of the Gauss-Manin connection over the full 3-dimensional parameter space Q(a,b,c). The trace of the connection on the eigenvalue-i eigenspace V_+ vanishes identically in all three parameter directions:

    tau_+(a,b,c) = 0  for d/da, d/db, d/dc

Conditional on the Variational Hodge Conjecture (Grothendieck 1966), the exotic Weil class is algebraic across the entire hyperelliptic Weil locus, anchored at the Fermat point (0,0,0) where algebraicity follows from Shioda's theorem (1982).

**CRM classification:** CLASS (conditional on VHC). Eleventh CRMLint Squeeze application.

## Contents

- `paper89.tex` / `paper89.pdf` -- LaTeX source and compiled paper (13 pages, 26 references)
- `P89_UniversalSqueeze/` -- Lean 4 formal verification bundle
- `verify_universal_family.py` -- Python CAS script (Griffiths pole reduction over Q(a,b,c))
- `emit_lean_data.py` -- Lean 4 code generator from CAS output
- `p89_matrices.txt` -- Full 8x8 connection matrices M_a, M_b, M_c
- `p89_vplus_blocks.txt` -- 4x4 V_+ blocks for each parameter direction
- `PROOF_INSTRUCTION_P89.md` -- Proof blueprint

## Lean 4 Bundle

### Build Instructions

```bash
cd P89_UniversalSqueeze
lake update
lake build
```

### Source Files

- `Papers/P89_UniversalSqueeze/UniversalData.lean` -- Polynomial identities: oddness, factorization, palindromic obstruction, specializations, Fermat pullback data, dimensions
- `Papers/P89_UniversalSqueeze/TraceData.lean` -- Six trace vanishing theorems (auto-generated from CAS)
- `Papers/P89_UniversalSqueeze/Paper89_UniversalSqueeze.lean` -- Main squeeze theorem (18 conjuncts), CRM classification

### Axiom Inventory

**Declared axioms (CLASS boundary):**
- `shioda_fermat_hodge` -- Shioda 1982, Hodge for Fermat quotients
- `variational_hodge_conjecture` -- Grothendieck 1966, algebraicity spreading

**Infrastructure (Lean/Mathlib):**
- `propext`, `Quot.sound`, `Classical.choice` -- not classical content

**Sorry count: 0**

## Dependencies

- Paper 80: Griffiths pole reduction pipeline
- Paper 84: Gauss-Manin block decomposition for palindromic family
- Paper 85: Computational trace vanishing for 1-parameter family
- Paper 86: Kani-Rosen splitting on palindromic locus
- Paper 88: Fermat anchor + VHC framework

## CAS Pipeline

Total computation time: ~45 seconds (SymPy, M-series Mac).

1. Extended GCD over Q(a,b,c)[x] for Bezout identity (0.4s)
2. Three 8x8 connection matrices via Griffiths pole reduction (12-19s each)
3. Trace extraction and denominator clearing
4. Lean code emission
