# Paper 25: The Choice Axis in Constructive Reverse Mathematics

**Calibrating Ergodic Theorems and Laws of Large Numbers against Countable and Dependent Choice**

Paper 25 in the Constructive Reverse Mathematics Series
Paul C.-K. Lee (NYU), February 2026

## Overview

This Lean 4 formalization opens a second axis in the CRM calibration of mathematical
physics: the **choice hierarchy** AC₀ < CC < DC. The main result is that the mean
ergodic theorem (von Neumann, 1932) is equivalent over BISH to Countable Choice (CC).

The formalization was developed in two phases:

- **Phase 1** (11 files, 1410 lines): Forward direction fully formalized (CC → Mean Ergodic,
  600+ lines of Hilbert space analysis); classically trivial reverse directions; Birkhoff ↔ DC
  calibration; weak and strong laws of large numbers; separation results.
- **Phase 2** (Computable.lean, 395 lines): Non-trivial Type-level reverse direction where
  the Mean Ergodic hypothesis is genuinely used, via an explicit ℓ²(ℕ×ℕ) encoding with a
  diagonal reflection operator.

## Main Results

| Theorem | Statement | Status |
|---------|-----------|--------|
| `meanErgodic_of_cc` | CC → Mean Ergodic Theorem | Fully proved (600+ lines) |
| `meanErgodic_implies_cc` | Mean Ergodic → CC (Prop-level) | Fully proved (classically trivial) |
| `meanErgodicComputableAll_implies_cc` | MeanErgodicComputableAll → CC_N (Type-level) | Fully proved (395 lines, hypothesis used) |
| `meanErgodic_iff_cc` | CC ↔ Mean Ergodic Theorem | Fully proved |
| `birkhoff_iff_dc` | DC ↔ Birkhoff's Ergodic Theorem | 1 custom axiom (Birkhoff not in Mathlib) |
| `weakLLN_of_cc` | CC → Weak Law of Large Numbers | Fully proved |
| `strongLLN_of_dc` | DC → Strong Law of Large Numbers | Fully proved |
| `birkhoff_above_mean_ergodic` | Birkhoff strictly above Mean Ergodic | Fully proved |

## Physical Interpretation

The calibration reveals a clean physical separation:

| Physical Layer | Principle | Convergence Type |
|---------------|-----------|-----------------|
| Mean ergodic theorem | ≡ CC | L²-convergence (ensemble averages) |
| Weak law of large numbers | CC | Convergence in probability |
| Birkhoff's ergodic theorem | ≡ DC | Pointwise a.e. convergence |
| Strong law of large numbers | DC | Almost sure convergence |

**Ensemble/average behavior requires CC; individual trajectory behavior requires DC.**

## The Type-Level Reverse Direction (Phase 2)

The key methodological contribution: in Lean's classical logic, CC is provable outright,
so the Prop-level reverse (Mean Ergodic → CC) is trivially true. To overcome this,
`Computable.lean` introduces a Type-level `MeanErgodicComputable` structure providing
projections and convergence moduli as **data** (not mere existence claims).

The extraction theorem `meanErgodicComputableAll_implies_cc` encodes a choice problem
A : ℕ → Set ℕ into ℓ²(ℕ×ℕ) via:
1. A diagonal reflection operator U_A (eigenvalues ±1, isometry)
2. A probe vector x₀(n,m) = 1/(2ⁿ·2ᵐ) with all nonzero coordinates
3. Cesàro stability at A-coordinates → projection inherits nonzero values
4. Deterministic extraction via `Nat.find` on nonzero coordinates

The hypothesis is genuinely used — it cannot be discarded.

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper25_choice_axis.pdf`). To recompile:

```bash
pdflatex paper25_choice_axis.tex
pdflatex paper25_choice_axis.tex
```

### Lean 4 Formalization

**Prerequisites:** Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version 4.28.0-rc1) and ensure `lake` is available.

```bash
cd P25_ChoiceAxis
lake exe cache get && lake build
```

The first build may take 30-60 minutes to download and compile Mathlib dependencies.
Subsequent builds are fast. Build status: **0 errors**, 2 warnings (permanent
model-theoretic sorries).

To explore interactively, open the `P25_ChoiceAxis` folder in VS Code with the
Lean 4 extension installed.

## Axiom Audit

All theorems have axiom profile `[propext, Classical.choice, Quot.sound]` except:

- `cc_n_iff_cc_seq`, `cc_n_of_dc`: `[propext, Quot.sound]` (no Classical.choice — purely constructive)
- `birkhoff_iff_dc`: additionally depends on `birkhoff_of_dc` (1 custom axiom)

`Classical.choice` in the profiles is a Lean metatheory axiom from Mathlib's analysis
infrastructure — not an object-level choice principle.

**Type-level reverse**: `meanErgodicComputableAll_implies_cc` has the same profile
`[propext, Classical.choice, Quot.sound]`, but the hypothesis `h : MeanErgodicComputableAll`
is genuinely used (not discarded). Classical.choice enters only through Mathlib infrastructure.

## Contents

```
README.md                              This file
paper25_choice_axis.tex                LaTeX source
paper25_choice_axis.pdf                Compiled paper (18 pages)
P25_ChoiceAxis/                        Lean 4 formalization
  lakefile.lean                        Package configuration
  lean-toolchain                       leanprover/lean4:v4.28.0-rc1
  lake-manifest.json                   Dependency lock file
  Papers.lean                          Root import
  Papers/P25_ChoiceAxis/
    Basic.lean               131 lines  Core definitions: CC, DC, AC₀, hierarchy
    CesaroAverage.lean       172 lines  Cesàro averages: definition + 5 lemmas
    MeanErgodic.lean         268 lines  CC → Mean Ergodic Theorem (main proof)
    MeanErgodicReverse.lean   80 lines  Mean Ergodic → CC + equivalence
    Computable.lean          395 lines  Type-level reverse: MeanErgodicComputableAll → CC
    PointwiseErgodic.lean    133 lines  Birkhoff ↔ DC (axiom + reverse)
    PointwiseErgodicReverse.lean 54 lines  DC > CC hierarchy proof
    WeakLaw.lean             142 lines  CC → Weak LLN
    StrongLaw.lean           116 lines  DC → Strong LLN (wraps Mathlib)
    Separation.lean           88 lines  AC₀ ↛ CC ↛ DC + DC ceiling
    CalibrationTable.lean     54 lines  Two-axis calibration table
    Main.lean                172 lines  Aggregator + #print axioms audit
```

12 Lean files, 1805 lines total.

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
- Paper 10: Logical geography of mathematical physics -- DOI: 10.5281/zenodo.18580342 [v 2.0 Technical Synthesis of Papers 1-16]
- Paper 11: Entanglement, CHSH, Tsirelson bound -- DOI: 10.5281/zenodo.18527676
- Paper 12: Constructive history of mathematical physics -- DOI: 10.5281/zenodo.18581707 [v 2.0 Historical Synthesis of Papers 1-16]
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
- Paper 25: Choice axis (CC, DC) and ergodic theorems -- This paper

## License

This work is part of the Constructive Reverse Mathematics series.
