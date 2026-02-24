# Paper 18 — A BISH-Complete Domain: Yukawa Renormalization as a Finite Discrete Map

**Author:** Paul Chun-Kit Lee (New York University)
**Date:** February 2026
**Series:** Constructive Reverse Mathematics for Mathematical Physics

## Abstract

The Standard Model Yukawa coupling renormalization group, treated as a finite discrete map (N steps of a fixed-step RK4 integrator), is shown to lie entirely within Bishop's constructive mathematics (BISH). Every operation — the beta functions, the integrator, the quasi-fixed-point convergence check, and the mass-ratio extraction — is a finite, terminating computation on rationals. No omniscience principle (LPO, WLPO, or BMC) is required. This provides the first BISH-complete domain in the constructive reverse mathematics programme, complementing five prior domains where the LPO boundary appears.

## Contents

```
paper18_writeup.tex       LaTeX source (7 pages)
paper18_writeup.pdf       Compiled PDF
rg_mass_hierarchy.py      Python numerical investigation (~600 lines)
plots/                    10 output plots
  plot01_top_qfp.png          Top Yukawa quasi-fixed-point convergence
  plot02_btau_ratio_hist.png  b/τ Yukawa ratio distribution
  plot03_btau_heatmap.png     b/τ ratio heatmap over initial conditions
  plot04_hierarchy_scatter.png Mass hierarchy scatter plot
  plot05_hierarchy_error.png  Hierarchy prediction errors
  plot06_1loop_vs_2loop_qfp.png  1-loop vs 2-loop QFP comparison
  plot07_btau_1L_vs_2L.png   b/τ ratio: 1-loop vs 2-loop
  plot08_koide.png           Koide relation exploration
  plot09_discrete_vs_continuous.png  Discrete vs continuous RG comparison
  plot10_qfp_basin_N.png     QFP basin of attraction vs step count
```

## Running the Code

### Dependencies

- Python 3.9+
- NumPy
- SciPy
- Matplotlib

### Execution

```bash
python3 rg_mass_hierarchy.py
```

**Runtime:** approximately 16 minutes on a modern laptop.

**Output:** 10 PNG plots saved to `plots/` directory, plus console summary with numerical results.

### Key Results

| Quantity | Value | Note |
|----------|-------|------|
| Top Yukawa QFP | y_t ≈ 1.04 | Pendleton–Ross fixed point |
| b/τ Yukawa ratio | y_b/y_τ ≈ 2.25 | At EW scale |
| Mass hierarchy | 5 orders of magnitude | From O(1) initial conditions |
| QFP convergence | Q₅ < 10⁻⁸ | BISH-certifiable |

## Note on Formalization

This is a **numerical investigation**, not a Lean formalization. The BISH-completeness claim is argued analytically in the paper (every operation is finite arithmetic on rationals with bounded iteration). A formal Lean certificate is not provided; the paper serves as a diagnostic complement to the formalized Papers 8, 13, 14, 15, and 17.

## Series

Paper 18 in the Constructive Reverse Mathematics series.
Full archive: [Zenodo DOI 10.5281/zenodo.18600243](https://doi.org/10.5281/zenodo.18600243)

## License

This work is released for academic use.
