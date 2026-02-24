# Paper 12: The Map and the Territory

**A Constructive History of Mathematical Physics**

**Version 1.1 (02/09/2026)**

Paul Chun-Kit Lee, New York University

---

## Description

This essay tells the story of 150 years of mathematical physics from an unfamiliar angle. A machine-verified research programme — approximately 11,000 lines of formally checked proofs in the Lean 4 proof assistant — has established that every empirical prediction of quantum and statistical mechanics examined so far can be derived using only the most elementary constructive logic, without the law of excluded middle or any principle of omniscience. The elaborate classical superstructure of modern physics — infinite-dimensional Hilbert spaces, thermodynamic limits, path integrals, singularity theorems — enters only through idealizations that no finite laboratory can instantiate.

This essay traces how classical logic was progressively imported into mathematical physics from the 1870s onward, what it cost at each stage, what constructive alternatives existed or could have been used instead, and what the pattern implies for the current state of theoretical physics. The calibration covers quantum states, static structures, and exactly solvable models; time evolution, scattering amplitudes, and real-time path integrals remain uncalibrated.

Paper 12 in the Constructive Calibration Programme, a companion to the formal synthesis (Paper 10), written for a broader audience. The essay covers five acts: (I) the Weierstrass-Boltzmann era and the import of LPO into analysis and statistical mechanics; (II) quantum mechanics, where density matrices, spectral bounds, and uncertainty relations live at BISH; (III) general relativity, where singularity theorems require LEM but all observational content is constructive; (IV) quantum field theory, where every confirmed prediction is a finite BISH computation despite the infinite-dimensional formalism; and (V) post-Standard-Model physics and the structural correlate between logical altitude and empirical disconnection.

Features 16 TikZ figures illustrating key conceptual relationships, 10 highlighted key-message boxes, and a detailed bibliography connecting to the formally verified papers in the series.

### What's new in Version 1.1

Version 1.1 adds new interpretive material, 5 new TikZ figures (16 figures total), and editorial refinements, without altering the paper's structure or formal claims.

**New figures and analysis:**

- **Heisenberg split** (Fig. 5): The uncertainty principle is decomposed into a constructive geometric core (preparation uncertainty, BISH) and a statistical superstructure (measurement uncertainty, Dependent Choice).

- **Spectrum as idealization** (Fig. 6): A three-level pyramid — from finite measurements (BISH) through exact spectral membership (Markov's Principle) to complete spectral decomposition (LPO+).

- **Singularity derivation chain** (Fig. 9): Horizontal flow tracing Schwarzschild geodesic incompleteness step by step — Raychaudhuri ODE, geodesic focusing, curvature growth (all BISH) — showing exactly where LPO enters through Bounded Monotone Convergence.

- **Undecidability grid** (Fig. 13): A 2x2 grid mapping the constructive and computability hierarchies as orthogonal axes agreeing on the finite/infinite boundary (Cubitt et al. spectral gap, Ji et al. MIP*=RE).

- **Safe vs. possibly pathological idealizations** (Fig. 15): Two-column flow diagram distinguishing safe idealizations (predictions independently extractable at BISH) from possibly pathological ones (non-constructive output propagates downstream as physical input).

**New content:**

- **Cognitive value of idealization**: Idealizations are cognitively essential (they convert processes into composable mathematical objects) but computationally empty (every number is extractable at BISH). The calibration table is reinterpreted as a cost-benefit ledger.

- **Safety criterion**: A diagnostic distinguishing safe from possibly pathological idealizations, with the thermodynamic limit and Schwarzschild singularity as contrasting examples.

- **Quantum gravity open question**: Whether BISH-level empirical content across both gravitational and quantum theories constrains viable quantum gravity programmes.

- **Revised Batterman response**: Explicit position on "essential idealizations" — cognitively essential, computationally empty.

**Editorial refinements (v1.1 final):**

- **Scope clarification**: Abstract now explicitly states what remains uncalibrated (time evolution, scattering amplitudes, real-time path integrals).

- **Terminology standardisation**: "program" → "programme" throughout.

- **LPO formal footnote**: Formal binary-sequence characterisation of LPO added at first use.

- **Precision fixes**: Paper 13 scope clarified to Schwarzschild case (not general Penrose theorem). Figure 10 and Figure 15 captions refined accordingly. Information paradox propagation claim marked as unformalised.

- **Wilsonian RG acknowledgment**: New passage recognising the irony that the RG — itself an LPO-level construction — is the framework that explains why the cellar is stable.

- **Yang-Mills refinement**: Mass gap passage rewritten to distinguish the Millennium Problem (map-territory matching) from the lattice predictions (already confirmed at BISH).

- **Act V citations**: Bousso-Polchinski (string landscape), Susskind (anthropic landscape), and AMPS (firewall paradox) added.

- **Structural conclusion cut**: "Return to the Cellar" trimmed by ~50%, removing recapitulations of material already covered with figures. Retains the rhetorical frame (return to g-2), the key intellectual claim (the hierarchy answers physics questions it wasn't designed for), and the falsifiability statement.

---

## Contents

```
paper 12/v1.1/
|-- essay_constructive_history.tex    LaTeX source (33 pages, 16 TikZ figures)
|-- essay_constructive_history.pdf    compiled PDF
|-- ZENODO_DESCRIPTION.md             this file
```

This paper contains no Lean 4 code. The formal proofs it discusses are archived separately as Papers 2, 6-11, and 13 in the Constructive Calibration Programme.

---

## Relationship to Other Papers

| Paper | Title | Role |
|-------|-------|------|
| 2 | WLPO Equivalence of the Bidual Gap | Singular states calibration |
| 6 | Heisenberg Uncertainty in CRM | Preparation vs. measurement HUP |
| 7 | Non-Reflexivity of S_1(H) | WLPO dispensability |
| 8 | LPO-Equivalence of 1D Ising (Transfer Matrix) | Thermodynamic limit calibration |
| 9 | Formulation-Invariance (Combinatorial Ising) | Domain invariance evidence |
| 10 | Formal Synthesis | Machine-verified summary of all calibrations |
| 11 | Tsirelson Bound and Bell Entropy | Quantum entanglement at BISH |
| **12** | **The Map and the Territory (this paper)** | **Narrative essay for broad audience** |
| 13 | Schwarzschild Geodesic Incompleteness | GR singularity calibration |

---

## Other papers in the Constructive Reverse Mathematics Series

See Zenodo for current files:

- Paper 1: Withdrawn
- Paper 2: Bidual gap and WLPO — DOI: 10.5281/zenodo.17107493
- Paper 3: Withdrawn
- Paper 4: Quantum spectra axiom calibration — DOI: 10.5281/zenodo.17059483
- Paper 5: Schwarzschild curvature verification — DOI: 10.5281/zenodo.18489703
- Paper 6: Heisenberg uncertainty (v2, CRM over Mathlib) — DOI: 10.5281/zenodo.18519836
- Paper 7: Physical bidual gap, trace-class operators — DOI: 10.5281/zenodo.18527559
- Paper 8: 1D Ising model and LPO — DOI: 10.5281/zenodo.18516813
- Paper 9: Ising formulation-invariance — DOI: 10.5281/zenodo.18517570
- Paper 10: Logical geography of mathematical physics — DOI: 10.5281/zenodo.18527877
- Paper 11: Entanglement, CHSH, Tsirelson bound — DOI: 10.5281/zenodo.18527676
- Paper 12: Constructive history of mathematical physics — DOI: 10.5281/zenodo.18563230
- Paper 13: Event horizon as logical boundary — DOI: 10.5281/zenodo.18529007

Note: GitHub repository is not maintained; please see Zenodo for current files.

---

## Citation

```bibtex
@unpublished{Lee2026Paper12,
  author = {Lee, Paul Chun-Kit},
  title  = {The Map and the Territory:
            A Constructive History of Mathematical Physics},
  year   = {2026},
  note   = {Paper 12 in the Constructive Calibration Programme, Version 1.1},
  url    = {https://github.com/quantmann/FoundationRelativity}
}
```

---

## License

CC-BY 4.0
