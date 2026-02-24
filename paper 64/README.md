# Paper 64: Uniform p-Adic Decidability for Elliptic Curves

**Constructive Reverse Mathematics Series**

Paul C.-K. Lee (NYU), February 2026

DOI: [10.5281/zenodo.18737090](https://doi.org/10.5281/zenodo.18737090)

## Overview

This paper determines the uniform p-adic precision bound N_M = v_p(#E(F_p))
for crystalline decidability of elliptic curves E/Q.

MAIN RESULT: N_M <= 2 for all (E, p), with N_M = 2 only possible at p = 2,
and N_M <= 1 for every p >= 3. For p >= 5, equality N_M = 1 holds if and
only if E is anomalous at p (i.e., a_p = 1). The proof is a short argument
from the Hasse bound |a_p| <= 2*sqrt(p).

The principal consequence is that p-adic crystalline decidability for elliptic
curves requires at most two digits of p-adic precision at p = 2 and at most
one digit everywhere else. The p-adic side of the decidability problem is
thus uniformly trivial, contrasting sharply with the Archimedean side, where
rank creates genuine stratification (Papers 59, 61).

Computational verification: 1,812 elliptic curves across 15 primes,
covering 23,454 (E, p) pairs. Zero exceptions.

No Lean formalization for this paper (purely computational Python + short
proof from the Hasse bound).

## Repository Contents

```
README.md                           This file
paper64.tex                         LaTeX source (10 pages)
paper64.pdf                         Compiled paper
p64_compute.py                      Python computation script
p64_N_M_table.csv                   Full (E, p, N_M) table (23,454 rows)
p64_curve_summary.csv               Per-curve summary (1,812 rows)
p64_prime_summary.csv               Per-prime summary
p64_hasse_analysis.csv              Hasse bound analysis
p64_curves_raw.json                 Raw curve data from LMFDB
p64_computation_report.md           Computation report with all findings
p64_hasse_bound_comparison.png      Hasse bound comparison plot (in paper)
p64_histogram_max_NM.png            Histogram of max N_M (in paper)
p64_small_primes.png                Small primes analysis plot (in paper)
p64_NM_by_rank.png                  N_M by rank (supplementary)
p64_NM_by_torsion.png               N_M by torsion group (supplementary)
p64_scatter_NM_vs_conductor.png     N_M vs conductor scatter (supplementary)
```

## How to Reproduce

### LaTeX

```bash
pdflatex paper64
pdflatex paper64
```

### Computation

Requires Python 3 with matplotlib and numpy. No SageMath or external
database access needed. Point counting is by direct enumeration modulo p.

```bash
python3 p64_compute.py
```

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)
