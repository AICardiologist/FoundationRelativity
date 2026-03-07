# Paper 50: Three Axioms for the Motive

**Full title:** Three Axioms for the Motive (Paper 50, Constructive Reverse Mathematics Series)

**Author:** Paul Chun-Kit Lee, New York University, Brooklyn, NY

## Summary

This paper introduces the DPT (Decidable Polarized Tannakian) axiom framework and the u-invariant mechanism u(R) = infinity that explains why the real numbers are the unique source of non-constructive content in arithmetic geometry. The Archimedean completion R, unlike any non-Archimedean completion Q_p, admits positive-definite forms in every dimension—this forces the LPO/WLPO cost of sign decisions that pervades the CRM hierarchy.

## Main Results

- **DPT Axiom Framework:** Three axioms (cycle class decidability, spectral decidability, polarization decidability) that together make motivic computations BISH-decidable.
- **u(R) = infinity:** The u-invariant of R is infinite, meaning positive-definite forms exist in every dimension. Over Q_p, u(Q_p) = 4 (finite), so the relevant lattice computations are BISH.
- **Archimedean Stratification (Remark 2.4):** The CRM hierarchy maps onto the algebraic hierarchy of R: R-as-ring = BISH, R-as-ordered-field = LPO/WLPO, R-as-complete-ordered-field = CLASS.

## Lean 4 Bundle

```bash
cd P50_Universal
lake update && lake build
```

## Build LaTeX

```bash
pdflatex paper50.tex && pdflatex paper50.tex
```

## DOI

https://doi.org/10.5281/zenodo.18705837

## License

- Lean 4 code: Apache-2.0
- LaTeX paper and PDF: CC-BY 4.0

Copyright 2026 Paul Chun-Kit Lee
