# Paper 28: Newton vs. Lagrange vs. Hamilton --- Constructive Stratification of Classical Mechanics

**Paper 28 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

DOI: [10.5281/zenodo.18616620](https://doi.org/10.5281/zenodo.18616620)

## Overview

This Lean 4 formalization proves that the three textbook formulations of classical
mechanics --- Newtonian (equation-of-motion), Lagrangian (variational/optimization), and
Hamiltonian (phase-space) --- are **constructively stratified**: they require different
logical principles in constructive reverse mathematics.

For the discrete harmonic oscillator with N=2 time steps:

- **BISH half**: The Euler-Lagrange equation (8m-k)q = 4m(A+B) has a unique explicit
  solution q* = 4m(A+B)/(8m-k). The proof is purely algebraic --- no Fan Theorem, no
  excluded middle. This is the Newtonian (equation-of-motion) content.

- **Hamilton half (BISH)**: Hamilton's equations for N=2 have a unique solution. The
  position is determined by the EL equation; the momentum by the Legendre relation
  p = 2m(q-A). All proofs are purely algebraic --- no Fan Theorem needed.

- **Legendre bridge (BISH)**: The discrete Legendre transform between Lagrangian and
  Hamiltonian formulations is explicitly invertible. This is a BISH bridge connecting
  the two equation-solving formulations.

- **FT half**: The assertion that every continuous function on [0,1] attains its minimum
  (and in particular that the action S attains its minimum) is equivalent to the Fan
  Theorem. This is the Lagrangian (variational) content.

All equation-solving is BISH. All optimization is FT. The bridge between formulations is BISH.

## Main Results

| Theorem | Statement | CRM Level |
|---------|-----------|-----------|
| `el_unique_solution_N2` | EL equation has unique solution under CFL condition | BISH |
| `elSolution_satisfies` | Explicit solution satisfies the EL equation | BISH |
| `hamilton_unique_solution` | Hamilton's equations have unique solution | BISH |
| `legendre_invertible` | Discrete Legendre transform is left-invertible | BISH |
| `legendre_invertible'` | Discrete Legendre transform is right-invertible | BISH |
| `legendre_consistency` | Lagrangian and Hamiltonian solutions are Legendre-related | BISH |
| `minimizer_of_ft` | Fan Theorem implies action minimizer exists | FT (hypothesis) |
| `minimizer_iff_ft` | Universal minimizer existence on [0,1] iff Fan Theorem | pure logic |
| `stratification` | BISH solves EL and minimizer existence iff FT | BISH + FT |
| `stratification_triad` | Three-way stratification: EL + Hamilton + Legendre (BISH) and minimizer (FT) | BISH + FT |
| `ft_dispensable_for_el` | FT not needed for EL solution | BISH |
| `ft_needed_for_minimizer` | Minimizer existence implies FT | pure logic |

## Physical Interpretation

| Formulation | Physical Content | CRM Level |
|-------------|-----------------|-----------|
| Newtonian (EOM) | Solve (8m-k)q = 4m(A+B) | BISH |
| Hamiltonian (phase-space) | Solve Hamilton's equations for (q*, p*) | BISH |
| Legendre bridge | q ↦ p = 2m(q-A), invertible | BISH |
| Lagrangian (variational) | Assert minimizer of S(q) exists on [0,1] | FT |

**All equation-solving formulations are constructive (BISH); the optimization formulation requires the Fan Theorem.**

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper28_newton_lagrange.pdf`). To recompile:

```bash
pdflatex paper28_newton_lagrange.tex
pdflatex paper28_newton_lagrange.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version 4.28.0-rc1) and ensure `lake` is available.

```bash
cd P28_NewtonLagrange
lake exe cache get && lake build
```

The first build may take 30-60 minutes to download and compile Mathlib dependencies.
Subsequent builds are fast. Build status: **0 errors, 0 warnings**.

To explore interactively, open the `P28_NewtonLagrange` folder in VS Code with the
Lean 4 extension installed.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]`.
`Classical.choice` is a Lean metatheory axiom from Mathlib's real number construction
(classical Cauchy completion) --- not an object-level non-constructive principle.

The constructive stratification is established by proof content:

- **BISH half (EL + Hamilton + Legendre)**: Uses explicit witness construction
  (`elSolution`, `discreteMomentum`, `legendreInverse`) and algebraic manipulation
  (`field_simp`, `linarith`, `ring`). `FanTheorem` does NOT appear as hypothesis.
- **FT half**: Carries `FanTheorem` as an explicit hypothesis; proof reduces minimizer
  existence to EVT_min, which is equivalent to FT = EVT_max.

**Zero custom axioms. Zero sorry.**

## Contents

```
README.md                              This file
paper28_newton_lagrange.tex            LaTeX source (1399 lines)
paper28_newton_lagrange.pdf            Compiled paper (17 pages)
P28_NewtonLagrange/                    Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import
  Papers/P28_NewtonLagrange/
    Defs.lean              81 lines    Core definitions: FT, EVT, HOParams, action
    BISHHalf.lean          87 lines    BISH: EL unique solution
    FTHalf.lean           104 lines    FT: minimizer iff Fan Theorem
    HamiltonBISH.lean     171 lines    BISH: Hamilton equations, Legendre transform
    Stratification.lean   158 lines    Main theorems + three-way stratification
    Main.lean              20 lines    Root aggregator
```

6 Lean source files, 621 lines total.

## Complete Paper List

Other papers in the Constructive Reverse Mathematics Series (see Zenodo for current files):

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
- Paper 18: Fermion mass hierarchy and scaffolding principle -- DOI: 10.5281/zenodo.18600243
- Paper 19: WKB tunneling and LLPO -- DOI: 10.5281/zenodo.18602596
- Paper 20: Observable-dependent logical cost, 1D Ising magnetization and WLPO -- DOI: 10.5281/zenodo.18603079
- Paper 21: Bell nonlocality and LLPO -- DOI: 10.5281/zenodo.18603251
- Paper 22: Markov's Principle and radioactive decay -- DOI: 10.5281/zenodo.18603503
- Paper 23: Fan Theorem and optimization -- DOI: 10.5281/zenodo.18604312
- Paper 24: Kochen-Specker contextuality and LLPO -- DOI: 10.5281/zenodo.18604317
- Paper 25: Choice axis (CC, DC) and ergodic theorems -- DOI: 10.5281/zenodo.18607498
- Paper 26: Axiom of Choice and path integrals -- DOI: 10.5281/zenodo.18610985
- Paper 27: Constructive quantum field theory -- DOI: 10.5281/zenodo.18613925
- Paper 28: Newton vs. Lagrange vs. Hamilton, constructive stratification -- This paper

## License

This work is part of the Constructive Reverse Mathematics series.
