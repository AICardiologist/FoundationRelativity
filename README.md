# Constructive Reverse Mathematics Series

> **Disclaimer**: This Lean 4 formalization was produced by multi-AI agents under human direction. All proofs are verified by Lean's kernel. The mathematical content — theorems, calibrations, and the programme's conclusions — is the work of Paul Chun-Kit Lee.

[![CI](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml/badge.svg)](https://github.com/AICardiologist/FoundationRelativity/actions/workflows/ci.yml)
[![Series DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17054050.svg)](https://doi.org/10.5281/zenodo.17054050)

**Author:** Paul Chun-Kit Lee (New York University)

**70 papers. ~88,000 lines Lean 4. One finding:**

> The logical cost of mathematics is the logical cost of the real numbers.

The real numbers are the sole source of logical difficulty in both mathematical physics and arithmetic geometry. Every non-constructive principle required by any physical theory or arithmetic theorem enters through the Archimedean place — the completion of Q at infinity. The mechanism is u(R) = infinity, which forces three fields (physics, motivic arithmetic, automorphic theory) into the same positive-definite architecture.

## Logical Hierarchy

```
BISH  ⊂  BISH + MP  ⊂  BISH + LLPO  ⊂  BISH + WLPO  ⊂  BISH + LPO  ⊂  CLASS
```

- **BISH**: all searches bounded, all witnesses explicit
- **MP** (Markov's Principle): unbounded search that cannot fail to terminate, terminates
- **LLPO**: decide the sign of a real number
- **WLPO**: decide whether a real number equals zero
- **LPO**: decide whether a binary sequence contains a 1
- **FT** (Fan Theorem): independent, physically dispensable
- **DC** (Dependent Choice): independent, physically dispensable

**Physics ceiling**: BISH + LPO. **Arithmetic residual**: BISH + MP.

## Programme Structure

| Phase | Papers | Result |
|-------|--------|--------|
| **Physics** | 2-44 | BISH + LPO is the complete logical constitution of empirical physics |
| **Arithmetic geometry** | 45-66 | DPT framework, three-invariant hierarchy, h = f discovery |
| **FLT** | 68 | Fermat's Last Theorem is BISH |
| **Function field Langlands** | 69 | The correspondence is BISH; the base field is expensive |
| **Synthesis** | 70 | The Archimedean Principle: the only expensive thing is R |
| **Applications** | 71 | Archimedean Principle in cryptography and computation |

69 active papers (Papers 1 and 3 withdrawn; Papers 60 and 62 retired into 59 and 63).

## Key Discoveries

1. BISH + LPO = physics (Paper 40)
2. Three-invariant hierarchy for motives: rank, Hodge level, Lang constant (Papers 59-62)
3. Self-intersection equals conductor on CM abelian fourfolds (Papers 56-58, 65-66)
4. Fermat's Last Theorem is BISH (Paper 68)
5. Algebraic-vs-transcendental boundary, not discrete-vs-continuous (Paper 69)
6. Function field as lattice regularisation of number field (Paper 70)
7. Projection vs. search explains why number theory is harder than physics (Paper 70)

## Repository Layout

```
Papers/                     Lean 4 formalization bundles (self-contained, lake build)
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
paper N/                    LaTeX sources, PDFs, and per-paper Lean for each paper
scripts/                    CI audit scripts
```

Each `Papers/P{N}_*/` bundle is self-contained with its own `lakefile.lean`, `lean-toolchain` (v4.28.0-rc1), and `lake build`.

## Build

```bash
git clone https://github.com/AICardiologist/FoundationRelativity.git
cd FoundationRelativity

# Build a specific paper bundle
cd Papers/P69_FuncField && lake build

# Or from root (builds the root project's Papers)
lake build
```

## Lean Conventions

- Zero `sorry` policy across all published bundles
- `Classical.choice` appears in every theorem over R — this is Mathlib infrastructure, not classical content
- Constructive stratification is established by proof content (explicit witnesses vs. principle-as-hypothesis), not by `#print axioms` output

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

Individual paper DOIs are listed in the [series concept record](https://doi.org/10.5281/zenodo.17054050).

## License

Apache 2.0. See [LICENSE](LICENSE).

## Acknowledgments

- Lean 4 development team and mathlib4 contributors
- The constructive mathematics community (Bishop, Bridges, Richman)
- AI development assistance: Claude, Gemini, GPT
