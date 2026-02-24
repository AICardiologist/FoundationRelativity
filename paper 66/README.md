# Paper 66: Form-Class Resolution for Non-Cyclic Totally Real Cubics — The Trace-Zero Lattice Invariant

**Paper 66 of the Constructive Reverse Mathematics (CRM) Series**

Author: Paul Chun-Kit Lee, New York University, Brooklyn, NY
Date: February 2026
DOI: [10.5281/zenodo.18745722](https://doi.org/10.5281/zenodo.18745722)

---

## Summary

This paper identifies the trace-zero sublattice as the correct arithmetic invariant for non-cyclic (S_3) totally real cubic fields, resolving the form-class question left open by Paper 65.

For a totally real cubic field F/Q, the trace-zero sublattice Lambda_0 = {x in O_F : Tr(x) = 0} is a rank-2 positive-definite Z-lattice. Its Gram matrix G satisfies det(G) = 3 * disc(F), and its GL_2(Z)-equivalence class is a well-defined arithmetic invariant of F.

**Key results:**

- **Theorem A** (Determinant Identity): det(G) = 3 * disc(F) for all monogenic cubics.
- **Theorem B** (Cyclic Reduction): For cyclic cubics of conductor f, the trace-zero form is 2f * (1,1,1) — the hexagonal form scaled by 2f.
- **Theorem C** (Non-Cyclic Uniqueness): Among 51 non-cyclic cubics with disc(F) <= 2000 and index 1, all reduced forms are pairwise distinct.
- **Observation D** (No Simpler Predictor): The form is never the principal form; no closed-form formula in terms of the resolvent decomposition alone determines the class.

All computations are performed in exact integer arithmetic (no floating point). The constructive strength of all results is BISH (Bishop-style constructive mathematics) — no appeal to LPO, WLPO, or any non-constructive principle.

---

## Repository Contents

### Paper
| File | Description |
|------|-------------|
| `paper66.tex` | LaTeX source (15 pages) |
| `paper66.pdf` | Compiled PDF |

### Computation
| File | Description |
|------|-------------|
| `p66_compute_v2.py` | Main computation script (Python 3.9 + SymPy 1.14) |
| `p66_results.csv` | Complete dataset: 51 cubics with discriminants, Gram forms, resolvents |

### Figures
| File | Description |
|------|-------------|
| `p66_form_analysis.png` | Form entries (a, b, c) vs disc(F) for all 51 cubics |
| `p66_det_verification.png` | Verification plot: all points on det(G) = 3 * disc(F) |

### Supporting Files
| File | Description |
|------|-------------|
| `PAPER66_WORK_ORDER.md` | Original computational task specification |
| `p66_analysis.md` | Auto-generated analysis report from computation |

---

## How to Reproduce

### Requirements
- Python >= 3.9
- SymPy >= 1.14
- NumPy >= 1.26
- Matplotlib >= 3.9

### Run
```bash
cd paper\ 66/
python3 p66_compute_v2.py
```

This will:
1. Validate trace-form shortcut on known cyclic/non-cyclic cases (Phase 1)
2. Enumerate all monic x^3 + px^2 + qx + r with |p| <= 5, |q| <= 12, |r| <= 12 (Phase 2)
3. Compute trace-zero forms, validate det(G) = 3*disc(F), reduce via Gauss algorithm
4. Run pattern analysis and generate CSV, plots, and analysis report (Phase 3)

Runtime: ~30 seconds on a standard laptop.

### Compile Paper
```bash
pdflatex paper66.tex && pdflatex paper66.tex
```
Two passes needed for cross-references.

---

## Relationship to the CRM Series

This paper is a companion to Paper 65 ("Self-Intersection Patterns Beyond Cyclic Cubics"), which established h * Nm(A) = f for 1,220 cyclic cubic pairs with zero exceptions but found that the scalar identity fails for all non-cyclic cubics.

Paper 66 resolves the non-cyclic case: the scalar h is replaced by the full GL_2(Z) form class of the trace-zero sublattice, which is the "F-side" of the Weil lattice invariant.

The broader context is the atlas of exotic Weil class computations (Papers 50-53, 56-58, 65-66), which calibrates the constructive content of intersection-theoretic identities on CM abelian varieties.

---

## Data Format (p66_results.csv)

| Column | Description |
|--------|-------------|
| `disc` | Field discriminant = polynomial discriminant (index 1) |
| `poly_a, poly_b, poly_c` | Coefficients of x^3 + ax^2 + bx + c |
| `gram_a, gram_b, gram_c, gram_d` | Gram matrix [[a,b],[c,d]] of trace-zero lattice |
| `red_a, red_b, red_c` | Reduced BQF coefficients (ax^2 + bxy + cy^2) |
| `bqf_disc` | BQF discriminant = -12 * disc(F) |
| `n_classes` | Number of form classes of this discriminant |
| `D_resolvent` | Fundamental discriminant of quadratic resolvent Q(sqrt(disc)) |
| `f_artin` | Conductor: disc(F) = D_resolvent * f_artin^2 |
| `gcd` | Content g = gcd(a, b, c) of the non-primitive form |
| `prim_a, prim_b, prim_c` | Primitive part of the form (divided by g) |

---

## License

This work is released under CC BY 4.0.
