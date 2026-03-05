# Constructive Reverse Mathematics Series

> **Disclaimer**: This Lean 4 formalization was produced by multi-AI agents under human direction. All proofs are verified by Lean's kernel. The mathematical content — theorems, calibrations, and the programme's conclusions — is the work of Paul Chun-Kit Lee.

[![CI](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml)
[![Series DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17054050.svg)](https://doi.org/10.5281/zenodo.17054050)

**Author:** Paul Chun-Kit Lee (New York University)

**75 papers. ~89,000 lines Lean 4. One finding:**

**The logical cost of mathematics is the logical cost of the real numbers.**

Every non-constructive principle required by any physical theory or arithmetic theorem enters through one place: the real number line. Remove ℝ and everything collapses to Bishop-style constructive mathematics (BISH), where every object is computable and every proof carries an algorithm.

---

## The Logical Hierarchy

```
BISH  ⊂  BISH + MP  ⊂  BISH + LLPO  ⊂  BISH + WLPO  ⊂  BISH + LPO  ⊂  CLASS
```

| Principle | What it decides |
|-----------|----------------|
| **BISH** | Nothing — every existential witness is computed, every disjunction is decided by the proof |
| **MP** (Markov) | ¬¬∃ → ∃ for decidable predicates: if an unbounded search cannot fail, it succeeds |
| **LLPO** | For every real x: x ≤ 0 or x ≥ 0 (sign is decidable) |
| **WLPO** | For every real x: x = 0 or x ≠ 0 (equality to zero is decidable) |
| **LPO** | For every binary sequence: it is identically zero or it contains a 1 (omniscience) |

Two independent principles — the **Fan Theorem** (FT, every bar is uniform: compact spaces behave classically) and **Dependent Choice** (DC, sequential choices along a total relation) — sit outside this chain.

---

## Part One: Physics (Papers 2–44)

### The finding

**BISH + LPO is the complete logical constitution of empirically accessible physics.** Forty-three papers audit the logical content of quantum mechanics, general relativity, quantum field theory, statistical mechanics, quantum information, the Standard Model, AdS/CFT, and cosmology. Every empirical prediction lands at or below BISH + LPO. Classical logic is never needed.

LPO enters through exactly one door: the spectral theorem for unbounded self-adjoint operators on L²(ℝⁿ). That is the sole non-constructive ingredient in all of physics.

### What is surprising

**The ceiling is uniform.** You might expect different physical theories to scatter across the hierarchy — QM at one level, GR at another, QFT somewhere else. They don't. They all hit the same ceiling. The logical constitution of the Standard Model is the logical constitution of the 1D Ising model.

**The cost is genuine.** Fekete's Subadditive Lemma — the workhorse behind thermodynamic limits, free energy convergence, and phase-transition arguments — is *equivalent* to LPO (Paper 29). You cannot eliminate the non-constructive cost. It is not an artefact of a particular proof strategy.

**FT and DC are dispensable.** The Fan Theorem (compact optimisation, action minimisers) and Dependent Choice (ergodic theorems, strong law of large numbers) are logically independent of the omniscience spine. Both are physically dispensable: every empirical prediction they yield is recoverable in BISH + LPO (Papers 30–31). The variational formulation of mechanics is logically unnecessary for any prediction.

**The Landau pole is BISH.** QED's Landau pole — naively the most "non-constructive" object in renormalisation — is fully constructive. The closed-form solution provides an explicit Cauchy modulus. No omniscience required (Paper 32).

**Confinement is free.** QCD confinement (mass gap, WLPO) is subsidised by the LPO already paid for the continuum limit. Once you pay for the thermodynamic limit, confinement adds zero logical cost (Paper 33).

**All undecidability is LPO.** Cubitt's spectral gap undecidability, phase diagram uncomputability, 1D spectral gaps, uncomputable RG flows — every quantum undecidability result traces back to Wang tiling, which is LPO. Quantum undecidability introduces nothing beyond thermodynamic limits (Papers 36–38).

**The measurement problem dissolves.** Copenhagen (WLPO), Many-Worlds (DC), Bohmian mechanics (LPO) sit at provably distinct positions in the hierarchy. The "measurement problem" is not one problem but three logically incompatible commitments (Paper 44).

### Physics synthesis papers

| Paper | Title | Role |
|-------|-------|------|
| **10** | Logical Geography of Mathematical Physics | First atlas — 50 calibration entries across 11 domains |
| **12** | Constructive History of Mathematical Physics | 150-year narrative through the CRM lens |
| **40** | Logical Constitution of Physical Reality | Monograph proving the BISH + LPO ceiling (~35k lines Lean 4) |

---

## Part Two: Arithmetic Geometry (Papers 45–75)

### The finding

The same framework that classifies physics classifies arithmetic geometry. Five major conjectures (Hodge, Tate, BSD, Fontaine–Mazur, Weight-Monodromy) each exhibit a *de-omniscientising descent*: geometric origin converts LPO-dependent claims to BISH-decidable ones. The residual that survives is Markov's Principle — the cost of unbounded search.

### The Decidable Polarized Tannakian (DPT) framework (Paper 50)

Three axioms distil Grothendieck's category of numerical motives:
1. **Decidable morphisms** (Standard Conjecture D)
2. **Algebraic spectrum** (eigenvalues in Q̄)
3. **Archimedean polarisation** (positive-definite bilinear form)

These three axioms are exactly what de-omniscientisation requires. They are also exactly what the Archimedean place provides: u(ℝ) = ∞ guarantees positive-definite forms in every dimension. At every finite prime p, u(ℚₚ) = 4 blocks this in dimension ≥ 5.

### Three-invariant hierarchy (Papers 59–63)

Three numbers classify the logical cost of cycle-search for any motive:
- **Rank r**: analytic rank of the L-function. r = 0 or 1 → BISH. r ≥ 2 → MP (Minkowski forces unbounded search).
- **Hodge level ℓ**: ℓ ≤ 1 → intermediate Jacobian is algebraic → Northcott bounds search → MP. ℓ ≥ 2 → non-algebraic complex torus → LPO.
- **Lang constant c**: effective height lower bound converts MP to BISH by bounding the search.

### The h = f identity (Papers 56–58, 65–66)

A new arithmetic identity, not a CRM classification: the Faltings height times the norm of the Steinitz class equals the conductor on CM abelian fourfolds. Verified on 1,220 pairs with zero exceptions.

### The trilogy (Papers 68–70) — confirmation, not surprise

**Paper 68: FLT is BISH.** The Wiles path costs BISH + WLPO (weight-1 obstruction). Kisin's 2009 bypass avoids it. Net cost: BISH. This confirms the DPT prediction that major arithmetic theorems are cheaper than they look.

**Paper 69: Function field Langlands is BISH.** Predicted by the absence of an Archimedean place. The one genuine discovery: the CRM boundary is algebraic-vs-transcendental spectral parameters, not discrete-vs-continuous spectrum.

**Paper 70: The Archimedean Principle.** Synthesis, not discovery. Names the mechanism (u(ℝ) = ∞), formalises the projection-vs-search gap, explains why physics and Langlands share an architecture.

**Paper 71: Applications.** Lattice cryptography is Archimedean-hard; SVP phase transition sits at the projection/search boundary.

### Arithmetic synthesis papers

| Paper | Title | Role |
|-------|-------|------|
| **50** | Three Axioms for the Motive | DPT framework — three axioms for Grothendieck's motives |
| **67** | The Motive Is a Decidability Certificate | Arithmetic monograph — (r, ℓ, c) classify all motives (Papers 45–75) |
| **70** | The Archimedean Principle | Capstone — u(ℝ) = ∞ unifies physics and arithmetic |
| **72–74** | DPT Biconditional Trilogy | Each DPT axiom is uniquely necessary — canonical, not merely minimal |
| **75** | Conservation Test | External validation: GL LLC statement WLPO, proof CLASS |

---

## What Connects the Two Halves

The mechanism is **u(ℝ) = ∞**: positive-definite quadratic forms exist over ℝ in every dimension. Three fields independently exploit this via the same architecture:

| Field | Inner-product structure | How it uses u(ℝ) = ∞ |
|-------|------------------------|----------------------|
| Physics | Hilbert space ⟨ψ,φ⟩ | Spectral theorem → measurement → projection |
| Arithmetic geometry | Rosati involution on abelian varieties | Néron–Tate height → bounded search |
| Automorphic theory | Petersson inner product | Trace formula → spectral decomposition |

Physics descends by *projection* (→ BISH). Arithmetic descends by *search* (→ BISH + MP). The gap is exactly Markov's Principle. That is why number theory is harder than physics.

---

## What Is Genuinely New

| Old (known before this programme) | New (established here) |
|---|---|
| ℝ is logically hard (Brouwer 1907, Bishop 1967) | Uniform calibration across physics AND arithmetic in one framework |
| Constructive mathematics avoids LEM | u(ℝ) = ∞ identified as the *specific mechanism* forcing positive-definite descent |
| Physics is "more constructive" than pure math (folk intuition) | Projection vs. search as precise explanation, with the gap being exactly MP |
| Langlands programme connects automorphic forms and Galois representations | Physics-Langlands connections explained as shared logical constraint from ℝ |
| Individual constructive proofs exist for individual theorems | Systematic classification of 70 theorems revealing a single architectural pattern |

---

## Complete Paper List

Every paper with its bottom line. Papers 1 and 3 withdrawn; Papers 60 and 62 retired (merged into 59 and 63).

### Physics Papers

#### Foundations (Papers 2–6)

| # | Title | Bottom line |
|---|-------|------------|
| 2 | The Bidual Gap and WLPO | Banach space non-reflexivity detection ≡ WLPO |
| 4 | Axiom Calibration for Quantum Spectra | Five spectral properties stratified BISH → WLPO+MP |
| 5 | Schwarzschild Curvature Verification | GR curvature calibrated across five loci, BISH → LPO |
| 6 | Heisenberg Uncertainty (v2) | Preparation uncertainty BISH; measurement uncertainty DC |

#### Physical Calibrations (Papers 7–28)

| # | Title | Bottom line |
|---|-------|------------|
| 7 | Physical Bidual Gap | Trace-class non-reflexivity ≡ WLPO |
| 8 | 1D Ising Model and LPO | Finite-size bounds BISH; thermodynamic limit ≡ LPO |
| 9 | Ising Formulation-Invariance | Same LPO cost from combinatorial and transfer-matrix routes |
| **10** | **Logical Geography of Mathematical Physics** | **Synthesis: 50 entries across 11 domains** |
| 11 | Entanglement, CHSH, Tsirelson Bound | Tsirelson bound and entanglement entropy are BISH |
| **12** | **Constructive History of Mathematical Physics** | **Synthesis: 150-year narrative** |
| 13 | Event Horizon as Logical Boundary | Interior geometry BISH; singularity LPO |
| 14 | Quantum Decoherence | Finite-step BISH; completed limit LPO |
| 15 | Noether's Theorem | Local conservation BISH; global energy LPO |
| 16 | Born Rule | Single-trial BISH; frequentist convergence DC |
| 17 | Bekenstein–Hawking Formula | Finite entropy BISH; density convergence LPO |
| 18 | Yukawa RG Stratification | RG step BISH; thresholds WLPO; global coupling LPO |
| 19 | WKB Tunneling and LLPO | Amplitude BISH; turning points LLPO; semiclassical limit LPO |
| 20 | Observable-Dependent Logical Cost | Same system, different questions → different costs |
| 21 | Bell Nonlocality and LLPO | CHSH violation BISH; disjunctive conclusion LLPO |
| 22 | Markov's Principle and Radioactive Decay | "Nonzero decay → eventual detection" ≡ MP |
| 23 | Fan Theorem and Optimisation | EVT ≡ FT; physically dispensable |
| 24 | Kochen–Specker and LLPO | KS uncolourability BISH; sign decision LLPO (≡ Bell) |
| 25 | Choice Axis: Ergodic Theorems | Mean ergodic ≡ CC; Birkhoff pointwise ≡ DC |
| 26 | Bidual Gap Arithmetic Route | Second WLPO-completeness proof via Gödel sequences |
| 27 | Bell Angle Optimisation | LLPO ≡ exact IVT; strictly below WLPO |
| 28 | Newton vs. Lagrange vs. Hamilton | Equations of motion BISH; action minimisation FT (dispensable) |

#### Ceiling and Dispensability (Papers 29–35)

| # | Title | Bottom line |
|---|-------|------------|
| 29 | Fekete's Subadditive Lemma and LPO | Fekete ≡ LPO; the cost is genuine |
| 30 | Dispensability of the Fan Theorem | Every FT prediction recoverable in BISH + LPO |
| 31 | Dispensability of Dependent Choice | Every DC prediction recoverable in BISH + LPO |
| 32 | QED Renormalisation: Landau Pole | Landau pole is BISH; thresholds WLPO |
| 33 | QCD Renormalisation and Confinement | Confinement free — subsidised by LPO for continuum limit |
| 34 | Scattering Amplitudes | Fixed-order Bhabha cross section pure BISH |
| 35 | Logical Constitution: Metatheorem | BISH + LPO ceiling; three mechanisms equivalent |

#### Undecidability and Beyond (Papers 36–44)

| # | Title | Bottom line |
|---|-------|------------|
| 36 | Spectral Gap Undecidability = LPO | Cubitt ≡ LPO |
| 37 | Undecidability Landscape = LPO | Three further results, all LPO |
| 38 | Wang Tiling | All quantum undecidability from Wang tiling (LPO) |
| 39 | Physics Reaches Σ⁰₂: Physical Stratification | Epistemic mode determines arithmetic level; exact observables reach Σ⁰₂ |
| **40** | **Logical Constitution of Physical Reality** | **Monograph: BISH + LPO is the complete constitution** |
| 41 | AdS/CFT Diagnostic | Holographic dictionary axiom-preserving; bulk ≡ boundary |
| 42 | Cosmological Constant Problem | 10¹²⁰ discrepancy adds no new logical resources |
| 43 | Ceiling and Constructive Schools | BISH + LPO unifies Bishop, Brouwer, Markov |
| 44 | Measurement Problem Dissolved | Copenhagen (WLPO), Many-Worlds (DC), Bohm (LPO) |

### Arithmetic Papers

#### Five Conjectures (Papers 45–49)

| # | Title | Bottom line |
|---|-------|------------|
| 45 | Weight-Monodromy and LPO | De-omniscientising descent: geometric origin replaces LPO with BISH |
| 46 | Tate Conjecture and LPO | Galois-invariance ≡ LPO; Conjecture D is the decidability axiom |
| 47 | Fontaine–Mazur and LPO | De Rham ≡ LPO; Faltings comparison descends to BISH |
| 48 | BSD and LPO | L(E,1)=0 ≡ LPO; Néron–Tate gives Archimedean polarisation |
| 49 | Hodge Conjecture | Hodge type ≡ LPO; polarisation available but insufficient |

#### DPT Framework and Tests (Papers 50–59)

| # | Title | Bottom line |
|---|-------|------------|
| **50** | **Three Axioms for the Motive** | **DPT: decidable morphisms + algebraic spectrum + polarisation** |
| 51 | Archimedean Rescue in BSD | Positive-definite metric converts rank-1 from MP to BISH |
| 52 | Decidability Transfer | Conjecture D for abelian 3-folds via char-p transfer |
| 53 | CM Decidability Oracle | Decision procedure for all 13 CM elliptic curves over ℚ |
| 54 | Bloch–Kato Calibration | First out-of-sample DPT test; Axiom 1 fails for mixed motives |
| 55 | K3 Surfaces and Kuga–Satake | Second out-of-sample test; full DPT success |
| 56 | Exotic Weil Self-Intersection | deg(w·w) = √disc(F) on CM abelian fourfolds |
| 57 | All Nine Heegner Fields | Extension to all nine class-number-1 imaginary quadratic fields |
| 58 | Class Number Correction | h·Nm(𝔄) = f for h > 1 |
| 59 | De Rham Decidability + DPT Completeness | DPT complete: three axioms suffice |

#### Three-Invariant Hierarchy and Self-Intersection (Papers 61–66)

| # | Title | Bottom line |
|---|-------|------------|
| 61 | Lang's Conjecture as MP→BISH Gate | Effective Lang bound converts rank ≥ 2 from MP to BISH |
| 63 | Intermediate Jacobian Obstruction | Algebraic J^p ↔ low Hodge ↔ Northcott ↔ MP |
| 64 | Uniform p-Adic Decidability | p-adic side uniformly BISH; 23,454 pairs verified |
| 65 | Self-Intersection Beyond Cyclic Cubics | h·Nm(𝔄) = f on 1,220 pairs; zero exceptions |
| 66 | Form-Class Resolution | Trace-zero form classifies non-cyclic totally real cubics |

#### Synthesis and Trilogy (Papers 67–71)

| # | Title | Bottom line |
|---|-------|------------|
| **67** | **The Motive Is a Decidability Certificate** | **Monograph: (r, ℓ, c) classify all motives (Papers 45–75)** |
| 68 | Fermat's Last Theorem Is BISH | Wiles WLPO; Kisin bypass → BISH |
| 69 | Function Field Langlands Is BISH | Algebraic-vs-transcendental boundary, not discrete-vs-continuous |
| **70** | **The Archimedean Principle** | **Capstone: the only expensive thing is ℝ** |
| 71 | Archimedean Principle in Cryptography | Lattice crypto Archimedean-hard; SVP at projection/search boundary |

#### DPT Biconditional Trilogy and Conservation Test (Papers 72–75)

| # | Title | Bottom line |
|---|-------|------------|
| **72** | **The DPT Characterisation Theorem** | **Axiom 3 (Archimedean polarisation) ↔ BISH cycle-search; failure costs LPO** |
| 73 | Standard Conjecture D Is Necessary | Axiom 1 (Conjecture D) ↔ BISH morphism decidability; failure costs LPO |
| 74 | Algebraic Spectrum Is Necessary | Axiom 2 (algebraic spectrum) ↔ BISH eigenvalue decidability; failure costs WLPO |
| **75** | **Conservation Test: GL LLC Calibration** | **Statement WLPO, proof CLASS — conservation gap validates DPT externally** |

---

## Repository

```
Papers/                     Lean 4 formalization bundles (self-contained)
  P2_BidualGap/
  P5_GeneralRelativity/
  P6_Heisenberg_v2/
  P7_ReflexiveWLPO/
  P8_LPO_IsingBound/
  P23_FanTheorem/
  P28_NewtonLagrange/
  P33_QCDConfinement/
  P51_BSD/
  P68_WilesFLT/
  P69_FuncField/
  P70_Archimedean/
  P72_DPTCharacterisation/
  P73_Axiom1Reverse/
  P74_Axiom2Reverse/
  P75_ConservationTest/
paper N/                    LaTeX sources and PDFs for each paper
scripts/                    CI audit scripts
```

Each `Papers/P{N}_*/` bundle builds independently: `cd Papers/P72_DPTCharacterisation && lake build`. Lean 4 toolchain v4.28.0-rc1 (Papers 72–75: v4.29.0-rc2). Zero `sorry` across all published bundles. `Classical.choice` in every ℝ theorem is Mathlib infrastructure, not classical content — constructive stratification is by proof content, not `#print axioms` output.

73 active papers (Papers 1 and 3 withdrawn; Papers 60 and 62 retired into 59 and 63).

## Citation

```bibtex
@software{lee2026crm,
  author = {Lee, Paul Chun-Kit},
  title = {Constructive Reverse Mathematics Series: Lean 4 Formalizations},
  year = {2026},
  doi = {10.5281/zenodo.17054050},
  url = {https://doi.org/10.5281/zenodo.17054050}
}
```

Individual paper DOIs: [series concept record](https://doi.org/10.5281/zenodo.17054050).

## License

Apache 2.0. See [LICENSE](LICENSE).

## Acknowledgments

- Lean 4 development team and mathlib4 contributors
- The constructive mathematics community (Bishop, Bridges, Richman)
- Lean 4 formalization: primarily Claude (Anthropic, Opus 4.6), with Gemini 3.0 DeepThink for difficult mathematical proofs in the later series
- LaTeX and editorial assistance: Claude, Gemini, GPT
