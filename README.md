# Constructive Reverse Mathematics Series

> **Disclaimer**: This Lean 4 formalization was produced by multi-AI agents under human direction. All proofs are verified by Lean's kernel. The mathematical content — theorems, calibrations, and the programme's conclusions — is the work of Paul Chun-Kit Lee.

[![CI](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml)
[![Series DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17054050.svg)](https://doi.org/10.5281/zenodo.17054050)

**Author:** Paul Chun-Kit Lee (New York University)

**70 papers. ~88,000 lines Lean 4. One finding:**

---

## The Central Claim

**The logical cost of mathematics is the logical cost of the real numbers.**

Every non-constructive principle required by any physical theory or arithmetic theorem enters through one place: the Archimedean completion of the rationals — the real number line. Remove ℝ and everything collapses to Bishop-style constructive mathematics (BISH), where every object is computable and every proof carries an algorithm.

The intuition that the continuum is the source of difficulty is old. Brouwer said as much in 1907. Bishop built a programme around it. What is new here is:

1. **Uniform calibration.** A single framework classifies the logical cost of theorems across both mathematical physics (44 papers) and arithmetic geometry (22 papers). No prior work attempted this.

2. **The specific mechanism: u(ℝ) = ∞.** The u-invariant of the reals — the fact that positive-definite quadratic forms exist in every dimension — is the engine. This forces three apparently unrelated fields to develop the same inner-product architecture: the Hilbert space inner product in physics, the Rosati involution on abelian varieties, and the Petersson inner product on automorphic forms. They are the same construction, seen through the same logical lens.

3. **Projection vs. search.** Physics extracts information from ℝ by *projecting* (measurement collapses a state to an eigenvalue). Arithmetic extracts information from ℝ by *searching* (find a rational point, decide whether a series converges). Projection needs only LPO. Search needs MP. That asymmetry is why number theory is harder than physics — not because its objects are more complicated, but because its access to the continuum is less direct.

4. **Physics encodes Langlands.** Multiple physical theories (gauge theory, string dualities, conformal field theory) independently rediscover the Langlands correspondence. This programme explains why: they share the same logical constraint. Both are controlled by the spectral theory of ℝ.

---

## The Logical Hierarchy

Constructive reverse mathematics classifies theorems by which non-constructive principles they require. The hierarchy, from weakest to strongest:

```
BISH  ⊂  BISH + MP  ⊂  BISH + LLPO  ⊂  BISH + WLPO  ⊂  BISH + LPO  ⊂  CLASS
```

| Principle | What it decides | Logical cost |
|-----------|----------------|--------------|
| **BISH** | Nothing — all searches bounded, all witnesses explicit | Free |
| **MP** (Markov) | An unbounded search that cannot fail to terminate, terminates | Cheap |
| **LLPO** | The sign of a real number | Moderate |
| **WLPO** | Whether a real number equals zero | Moderate |
| **LPO** | Whether a binary sequence contains a 1 | Expensive |
| **CLASS** | Everything — law of excluded middle | Maximum |

Two independent principles — the **Fan Theorem** (FT) and **Dependent Choice** (DC) — are physically dispensable and sit outside this chain.

**The programme's calibration:** all of empirical physics lives at BISH + LPO. All of arithmetic geometry lives between BISH and BISH + LPO, with an MP residual. Classical logic (CLASS) is never needed.

---

## The Programme in Four Phases

### Phase 1 — Physics (Papers 2–44)

Forty-three papers audit the logical content of physical theories: quantum mechanics, general relativity, quantum field theory, statistical mechanics, the Standard Model. The conclusion (Paper 40): **BISH + LPO is the complete logical constitution of empirically accessible physics.** LPO enters through exactly one door — the spectral theorem for unbounded self-adjoint operators on L²(ℝⁿ). Every other ingredient is BISH.

### Phase 2 — Arithmetic Geometry (Papers 45–66)

Twenty-two papers build the DPT (de-omniscientising, projecting, testing) framework for motives. Three axioms. Five conjectures exhibit LPO → BISH descent with an MP residual. Key results:

- **Three-invariant hierarchy** (Papers 59–62): rank *r*, Hodge level *ℓ*, and Lang constant *c* classify the full decidability landscape of arithmetic objects.
- **h = f discovery** (Papers 56–58, 65–66): the Faltings height times the norm of the different equals the conductor on CM abelian fourfolds. Verified on 1,220 pairs. This is a new identity, not a CRM classification.

### Phase 3 — The Trilogy (Papers 68–70)

The trilogy asks: how cheap can the hardest theorems be?

**Paper 68: Fermat's Last Theorem is BISH.** The Wiles–Taylor proof costs BISH + WLPO — the non-constructive content lives entirely in the weight-1 Artin representation obstruction. But Kisin's 2009 proof (p = 2 dihedral bypass) avoids this obstruction. The net cost: BISH. The most famous theorem in number theory requires no non-constructive principles at all. The heavy machinery (Galois representations, modularity lifting, Hecke algebras) is scaffolding, not structure.

**Paper 69: Function Field Langlands is BISH.** Both proofs of the function field Langlands correspondence (L. Lafforgue 2002, V. Lafforgue 2018) are audited. Both are BISH. The key discovery is that the boundary between constructive and non-constructive is *not* discrete-vs-continuous spectrum (the naive expectation) but **algebraic-vs-transcendental spectral parameters**. Over function fields, even the continuous spectrum has algebraic parameters (z = q⁻ˢ lives on a compact algebraic torus), so the entire trace formula is BISH. Over number fields, the analogous parameters involve Γ(s) for s ∈ iℝ — transcendental — which forces WLPO. The correspondence itself is cheap. The base field is expensive.

**Paper 70: The Archimedean Principle.** Four theorems formalise the central claim:
- **(A)** The CRM level of any theorem is determined by one parameter: its distance from the Archimedean place.
- **(B)** The MP Gap: physics descends by projection (→ BISH). Arithmetic descends by search (→ BISH + MP). The gap is exactly Markov's Principle.
- **(C)** Automorphic CRM Incompleteness: the witness triple (5, 5, 2) shows there exist automorphic objects whose constructive status cannot be resolved within the current framework.
- **(D)** Three Spectral Gaps are Σ⁰₂ — the classification boundaries are arithmetically definable.

Paper 70 also explains why physics and Langlands are connected (§5.5) and why function fields serve as a lattice regularisation of number fields (§5.6): both are consequences of removing the Archimedean place.

### Phase 4 — Applications (Paper 71)

The Archimedean Principle applied to cryptography and computation.

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

## Key Discoveries

1. **BISH + LPO = physics** — the logical constitution is uniform across QM, GR, QFT, stat mech (Paper 40)
2. **Three-invariant hierarchy** — rank, Hodge level, Lang constant classify all motives (Papers 59–62)
3. **h · Nm(𝔄) = f** — Faltings height times norm of different equals conductor on CM abelian fourfolds; 1,220 pairs verified (Papers 56–58, 65–66)
4. **FLT is BISH** — the most famous theorem in number theory needs no non-constructive principles (Paper 68)
5. **Weight-1 obstruction: irreducible but bypassable** — five failure modes of the Wiles path, all bypassed by Kisin (Paper 68)
6. **Algebraic-vs-transcendental boundary** — the CRM boundary in automorphic theory is about the nature of spectral *parameters*, not the topology of the *spectrum* (Paper 69)
7. **Function field = lattice regularisation** — removing the Archimedean place does for Langlands what putting QFT on a lattice does for physics (Paper 70)
8. **Projection vs. search** — the precise reason number theory is harder than physics (Paper 70)
9. **The Archimedean Principle** — the logical cost of mathematics is the logical cost of ℝ (Paper 70)

---

## CRM as Diagnostic Tool

CRM does not compute new numbers or prove new theorems about specific mathematical objects. It is a *diagnostic*: it tells you where logical difficulty lives and why. The value is knowing where computational approximations fail and understanding the structural reason.

When a physicist discretises a PDE and the scheme blows up, or a number theorist's algorithm fails to converge, or an optimisation landscape has a non-computable minimum — CRM says these are not accidents. They are manifestations of the same boundary: the point where the Archimedean structure of ℝ forces a non-constructive step.

---

## Open Questions

These are signposts, not planned work. The programme stops at Paper 70.

1. Is the MP gap refinable? Does a natural domain sit at BISH + LLPO?
2. Can the Langlands correspondence serve as a CRM axiom?
3. Are the three spectral gaps exactly Σ⁰₂-complete?
4. Does condensed mathematics (Clausen–Scholze) provide an alternative descent mechanism?
5. Is the Fargues–Scholze geometrisation BISH? (The Archimedean Principle predicts yes.)
6. Where do CRM boundaries create engineering failures — in numerical stability, quantum complexity, and optimisation?

---

## Start Here: The Six Synthesis Papers

These six papers are the programme's best entry points. Each synthesises a phase; together they tell the whole story.

| Paper | Title | What it does |
|-------|-------|-------------|
| **10** | Logical Geography of Mathematical Physics | First atlas — 50 calibration entries across 11 physics domains in one table |
| **12** | Constructive History of Mathematical Physics | Narrative history — 150 years of mathematical physics told through the CRM lens |
| **40** | Logical Constitution of Physical Reality | Physics monograph — proves BISH + LPO is the complete logical constitution of empirical physics (~35k lines Lean 4) |
| **50** | Three Axioms for the Motive | Arithmetic axioms — the DPT framework distilling five conjectures into three axioms for Grothendieck's category of motives |
| **67** | The Motive Is a Decidability Certificate | Arithmetic monograph — synthesises Papers 45–66; three invariants (rank, Hodge level, Lang constant) classify all motives |
| **70** | The Archimedean Principle | Capstone — the logical cost of mathematics is the logical cost of ℝ; unifies physics and arithmetic via u(ℝ) = ∞ |

---

## Complete Paper List

Every paper with its bottom line. Papers 1 and 3 withdrawn; Papers 60 and 62 retired (merged into 59 and 63).

### Part I — Foundations (Papers 2–6)

| # | Title | Bottom line |
|---|-------|------------|
| 2 | The Bidual Gap and WLPO | Banach space non-reflexivity detection ≡ WLPO |
| 4 | Axiom Calibration for Quantum Spectra | Five spectral properties stratified BISH → WLPO+MP |
| 5 | Schwarzschild Curvature Verification | GR curvature verification calibrated across five loci, BISH → LPO |
| 6 | Heisenberg Uncertainty (v2) | Preparation uncertainty is BISH; measurement uncertainty needs DC |

### Part II — Physical Calibrations (Papers 7–28)

| # | Title | Bottom line |
|---|-------|------------|
| 7 | Physical Bidual Gap | Trace-class non-reflexivity ≡ WLPO; quantum state space gap is constructively inaccessible |
| 8 | 1D Ising Model and LPO | Finite-size bounds BISH; thermodynamic limit ≡ LPO |
| 9 | Ising Formulation-Invariance | Same LPO cost from combinatorial and transfer-matrix derivations |
| **10** | **Logical Geography of Mathematical Physics** | **Synthesis: 50 calibration entries across 11 physics domains** |
| 11 | Entanglement, CHSH, Tsirelson Bound | Tsirelson bound and entanglement entropy are BISH |
| **12** | **Constructive History of Mathematical Physics** | **Synthesis: 150-year narrative of physics through the CRM lens** |
| 13 | Event Horizon as Logical Boundary | Interior geometry BISH; singularity assertion LPO |
| 14 | Quantum Decoherence | Finite-step decoherence BISH; completed limit LPO |
| 15 | Noether's Theorem | Local conservation BISH; global energy LPO |
| 16 | Born Rule | Single-trial probability BISH; frequentist convergence DC |
| 17 | Bekenstein–Hawking Formula | Finite entropy BISH; density convergence LPO |
| 18 | Yukawa RG Stratification | RG step BISH; threshold crossings WLPO; global coupling LPO |
| 19 | WKB Tunneling and LLPO | Amplitude BISH; turning points LLPO; semiclassical limit LPO |
| 20 | Observable-Dependent Logical Cost | Same system, different questions → different logical costs |
| 21 | Bell Nonlocality and LLPO | CHSH violation BISH; disjunctive conclusion LLPO |
| 22 | Markov's Principle and Radioactive Decay | "Nonzero decay rate → eventual detection" ≡ MP |
| 23 | Fan Theorem and Optimisation | Extreme Value Theorem ≡ FT; physically dispensable |
| 24 | Kochen–Specker and LLPO | KS uncolourability BISH; sign decision LLPO (≡ Bell) |
| 25 | Choice Axis: Ergodic Theorems | Mean ergodic ≡ CC; Birkhoff pointwise ≡ DC |
| 26 | Bidual Gap Arithmetic Route | Second proof of WLPO-completeness via Gödel sequences |
| 27 | Bell Angle Optimisation | LLPO ≡ exact IVT; Bell angle-finding strictly below WLPO |
| 28 | Newton vs. Lagrange vs. Hamilton | Equations of motion BISH; action minimisation FT (dispensable) |

### Part III — Ceiling and Dispensability (Papers 29–35)

| # | Title | Bottom line |
|---|-------|------------|
| 29 | Fekete's Subadditive Lemma and LPO | Fekete ≡ LPO; the LPO cost is genuine and ineliminable |
| 30 | Dispensability of the Fan Theorem | Every FT prediction is recoverable in BISH + LPO |
| 31 | Dispensability of Dependent Choice | Every DC prediction is recoverable in BISH + LPO |
| 32 | QED Renormalisation: Landau Pole | Landau pole is BISH (!); threshold crossings WLPO |
| 33 | QCD Renormalisation and Confinement | Confinement is free — LPO for the continuum limit subsidises the mass gap |
| 34 | Scattering Amplitudes | Fixed-order cross sections (Bhabha) pure BISH |
| 35 | Logical Constitution: Metatheorem | BISH + LPO ceiling established; three mechanisms mutually equivalent |

### Part IV — Undecidability and Beyond (Papers 36–44)

| # | Title | Bottom line |
|---|-------|------------|
| 36 | Spectral Gap Undecidability = LPO | Cubitt's undecidability is Turing–Weihrauch ≡ LPO |
| 37 | Undecidability Landscape = LPO | Three further undecidability results, all LPO |
| 38 | Wang Tiling | All quantum undecidability descends from Wang tiling (LPO) |
| 39 | Beyond LPO: Thermodynamic Stratification | Generic spectral gap is Σ⁰₂; extensive observables cap at LPO |
| **40** | **Logical Constitution of Physical Reality** | **Physics monograph: BISH + LPO is the complete constitution** |
| 41 | AdS/CFT Diagnostic | Holographic dictionary is axiom-preserving; bulk ≡ boundary cost |
| 42 | Cosmological Constant Problem | The 10¹²⁰ discrepancy introduces no new logical resources |
| 43 | Ceiling and Constructive Schools | BISH + LPO unifies Bishop, Brouwer, Markov; disagreement localises to MP |
| 44 | Measurement Problem Dissolved | Copenhagen (WLPO), Many-Worlds (DC), Bohm (LPO) — three distinct positions |

### Part V — Arithmetic Geometry (Papers 45–59)

| # | Title | Bottom line |
|---|-------|------------|
| 45 | Weight-Monodromy and LPO | De-omniscientising descent: geometric origin replaces LPO with BISH |
| 46 | Tate Conjecture and LPO | Galois-invariance decidability ≡ LPO; Standard Conjecture D is the decidability axiom |
| 47 | Fontaine–Mazur and LPO | De Rham condition ≡ LPO; Faltings comparison descends to BISH |
| 48 | BSD and LPO | L(E,1)=0 decision ≡ LPO; Néron–Tate height gives Archimedean polarisation |
| 49 | Hodge Conjecture | Hodge type decidability ≡ LPO; polarisation available but insufficient |
| **50** | **Three Axioms for the Motive** | **DPT framework: decidable morphisms + algebraic spectrum + Archimedean polarisation** |
| 51 | Archimedean Rescue in BSD | Positive-definite metric converts rank-1 search from MP to BISH |
| 52 | Decidability Transfer | Standard Conjecture D for abelian 3-folds via characteristic-p transfer |
| 53 | CM Decidability Oracle | Verified decision procedure for all 13 CM elliptic curves over ℚ |
| 54 | Bloch–Kato Calibration | First out-of-sample DPT test; Axiom 1 fails for mixed motives |
| 55 | K3 Surfaces and Kuga–Satake | Second out-of-sample test; full DPT success |
| 56 | Exotic Weil Self-Intersection | deg(w·w) = √disc(F) on three CM abelian fourfolds |
| 57 | All Nine Heegner Fields | Extension of Paper 56 to all nine class-number-1 imaginary quadratic fields |
| 58 | Class Number Correction | h·Nm(𝔄) = f for h > 1; verified for ℚ(√-5) |
| 59 | De Rham Decidability + DPT Completeness | DPT is complete: three axioms + automatic de Rham decidability suffice |

### Part VI — Three-Invariant Hierarchy and Self-Intersection (Papers 61–66)

| # | Title | Bottom line |
|---|-------|------------|
| 61 | Lang's Conjecture as MP→BISH Gate | Effective Lang height bound converts rank ≥ 2 from MP to BISH |
| 63 | Intermediate Jacobian Obstruction | Algebraic J^p ↔ low Hodge ↔ Northcott ↔ MP; four-way equivalence |
| 64 | Uniform p-Adic Decidability | p-adic side uniformly BISH-decidable; 23,454 (E,p) pairs verified |
| 65 | Self-Intersection Beyond Cyclic Cubics | h·Nm(𝔄) = f verified on 1,220 pairs; zero exceptions |
| 66 | Form-Class Resolution | Trace-zero binary quadratic form classifies non-cyclic totally real cubics |

### Part VII — Synthesis (Papers 67–71)

| # | Title | Bottom line |
|---|-------|------------|
| **67** | **The Motive Is a Decidability Certificate** | **Arithmetic monograph: (r, ℓ, c) classify all motives** |
| 68 | Fermat's Last Theorem Is BISH | Wiles costs WLPO; Kisin bypass gives BISH; FLT needs no non-constructive principles |
| 69 | Function Field Langlands Is BISH | Both Lafforgue proofs BISH; boundary is algebraic-vs-transcendental, not discrete-vs-continuous |
| **70** | **The Archimedean Principle** | **Capstone: the only expensive thing is ℝ; u(ℝ) = ∞ unifies all 70 papers** |
| 71 | Archimedean Principle in Cryptography | Lattice crypto is Archimedean-hard; SVP phase transition at projection/search boundary |

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
  P69_FuncField/
  P70_Archimedean/
paper N/                    LaTeX sources and PDFs for each paper
scripts/                    CI audit scripts
```

Each `Papers/P{N}_*/` bundle builds independently: `cd Papers/P70_Archimedean && lake build`. Lean 4 toolchain v4.28.0-rc1. Zero `sorry` across all published bundles. `Classical.choice` in every ℝ theorem is Mathlib infrastructure, not classical content — constructive stratification is by proof content, not `#print axioms` output.

69 active papers (Papers 1 and 3 withdrawn; Papers 60 and 62 retired into 59 and 63).

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
