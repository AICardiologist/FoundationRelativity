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
- AI development assistance: Claude, Gemini, GPT
