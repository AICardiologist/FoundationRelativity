# Paper 65: Self-Intersection Patterns Beyond Cyclic Cubics

**Author:** Paul Chun-Kit Lee
**Series:** Foundations of Constructive Relativity, Paper 65
**DOI:** [10.5281/zenodo.18743151](https://doi.org/10.5281/zenodo.18743151)
**Date:** February 2026

## Main Result

For a CM abelian fourfold A_{K,F} built from an imaginary quadratic field
K = Q(sqrt(-d)) and a totally real cyclic cubic F of conductor f, the
self-intersection degree h of the exotic Weil class satisfies the
**Steinitz--conductor identity**:

    h * Nm(A) = f

where A is the Steinitz ideal class of the Weil lattice W_int (an
O_K-module of rank 1). This identity is verified across all 1,220
pairs (K, F) with d <= 200 and f <= 200, with zero exceptions.

- **738 pairs** have free lattices (h = f, Nm(A) = 1).
- **482 pairs** require a Steinitz twist (Nm(A) > 1).
- The Steinitz twist is forced precisely when f is not represented
  by the principal binary quadratic form of K.
- When f is inert in K, the lattice is necessarily free.
- For non-cyclic (S_3) cubics, the scalar identity breaks:
  h^2 = disc(F) never holds.

## Repository Contents

### Paper
- `paper65.tex` -- LaTeX source (10 pages)
- `paper65.pdf` -- compiled PDF

### Computation
- `p65_compute.py` -- self-contained Python computation script
  (all integer arithmetic, no external APIs)

### Generated Data
- `p65_class_numbers.csv` -- class numbers for 122 squarefree d <= 200
- `p65_cyclic_cubics.csv` -- 10 cyclic cubic polynomials found
- `p65_family3_results.csv` -- all 1,220 (K, F) pair results
- `p65_family1_cubics.csv` -- 24 non-cyclic cubics (disc <= 1000)
- `p65_family1_gram_candidates.csv` -- 216 Gram matrix analyses
- `p65_raw_data.json` -- summary statistics
- `p65_computation_report.md` -- detailed computation report

### Plots
- `p65_family3_verification.png` -- h*Nm(A) vs f scatter plot
- `p65_forcing_heatmap.png` -- Steinitz forcing heatmap
- `p65_class_numbers.png` -- class number distribution
- `p65_family1_h_vs_disc.png` -- non-cyclic h values vs discriminant

## Reproducing the Computation

```bash
python3 p65_compute.py
```

Requirements: Python 3.8+ with `matplotlib` (for plots only; computation
is pure integer arithmetic with no dependencies beyond the standard library).

## CRM Level

BISH + WLPO (the representability criterion involves deciding membership
in the principal genus, which requires WLPO for the relevant decidability).

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)
