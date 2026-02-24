# Paper 10 v1.1: The Logical Geography of Mathematical Physics

**Constructive Calibration from Density Matrices to the Event Horizon**

Paul Chun-Kit Lee, New York University

---

## What's New in v1.1

- **New Section 3 "Methodology: Formalization in a Classical Metatheory"**: the
  series-wide certification methodology with three levels (mechanically certified,
  structurally verified, intentional classical content), the Mathlib question,
  the role of minimal artifacts, and limitations.
- **Expanded calibration table**: five new entries from Papers 11 (Bell nonlocality,
  entanglement entropy, partial trace — all BISH) and Paper 13 (Schwarzschild
  interior BISH, geodesic incompleteness LPO).
- **Strengthened working hypothesis**: evidence now spans functional analysis,
  statistical mechanics, quantum information, and general relativity.
- **Domain invariance discussion**: Papers 8 and 13 use BMC equiv LPO in
  unrelated physical domains (statistical mechanics vs. general relativity).
- **Two new open problems**: infinite-dimensional entanglement entropy (Problem 7)
  and singularity calibration beyond Schwarzschild (Problem 8).
- **Updated abstract, conclusion, and bibliography** for expanded scope.
- **Fixed TikZ diagram**: MP no longer shown as implying WLPO (they are independent).
- **Fixed van Wierst bibliography**: corrected page range (1863--1884).
- **Updated DOIs**: Paper 7 (10.5281/zenodo.18527559), Paper 11 (10.5281/zenodo.18527676).
- **Affiliation updated** to New York University.
- **Title updated** to "from Density Matrices to the Event Horizon" (was "to the
  Thermodynamic Limit").

Paper 10 is a synthesis/conceptual paper with no Lean formalization of its own.

---

## Compile the Paper

```bash
pdflatex paper10_logical_geography.tex    # pass 1
pdflatex paper10_logical_geography.tex    # pass 2
pdflatex paper10_logical_geography.tex    # pass 3
```

The precompiled `paper10_logical_geography.pdf` (23 pages) is included.

---

## File Organization

```
paper10_v1_1/
├── README.md                          this file
├── paper10_logical_geography.tex      LaTeX source (v1.1)
└── paper10_logical_geography.pdf      compiled paper (23 pages)
```

---

## Citation

```bibtex
@unpublished{Lee2026Paper10,
  author = {Lee, Paul Chun-Kit},
  title  = {The Logical Geography of Mathematical Physics:
            Constructive Calibration from Density Matrices
            to the Event Horizon},
  year   = {2026},
  note   = {Preprint, v1.1. Companion to the constructive
            calibration programme (Paper~10)},
  url    = {https://github.com/quantmann/FoundationRelativity}
}
```

---

## License

CC-BY 4.0 (paper).
