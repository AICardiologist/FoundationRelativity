# Paper 11 v1.1: The Constructive Cost of Quantum Entanglement

**Tsirelson Bound and Bell State Entropy in Lean 4**

Paul Chun-Kit Lee, New York University

DOI: [10.5281/zenodo.18527676](https://doi.org/10.5281/zenodo.18527676)

---

## What's New in v1.1

- **Revised §6 "The Classical Metatheory"**: honest disclosure of the certification
  methodology with §6.1-6.4 structure (axiom profile, what the formalization certifies,
  what it does not certify, comparison table with certification levels).
- **Abstract qualification**: one sentence on Classical.choice provenance.
- **§5.2 methodological paragraph**: clarifies that the artifact is primarily a
  verification of correctness; the BISH calibration follows from proof content.
- **Corrected `#print axioms` comments** in code listings.
- **Paper 10 forward reference** for systematic certification methodology.
- **Affiliation updated** to New York University.

The Lean code is unchanged (639 lines, 8 modules, zero sorry, zero errors).

---

## Quick Start

### Prerequisites

- **elan** (Lean version manager): https://github.com/leanprover/elan
- **Git** (required by Lake to fetch Mathlib)
- ~8 GB disk space (for Mathlib cache)

### Build and Verify

```bash
cd paper11_v1_1
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 11 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, 0 sorry.

### Compile the Paper

```bash
pdflatex paper11_writeup.tex    # pass 1
pdflatex paper11_writeup.tex    # pass 2
pdflatex paper11_writeup.tex    # pass 3
```

The precompiled `paper11_writeup.pdf` (21 pages) is included.

---

## File Organization

```
paper11_v1_1/
├── README.md                              this file
├── lakefile.lean                          Lake build configuration
├── lean-toolchain                         Lean version pin (v4.28.0-rc1)
├── lake-manifest.json                     pinned dependency versions
├── Papers.lean                            root import module
├── Papers/P11_Entanglement/
│   ├── Defs.lean                          involutions, CHSH, Pauli, Bell state (85 lines)
│   ├── BinaryEntropy.lean                 h(p), h(1/2) = log 2 (57 lines)
│   ├── PartialTrace.lean                  trace preservation (36 lines)
│   ├── BellState.lean                     partial trace = ½I, entropy = log 2 (61 lines)
│   ├── KroneckerLemmas.lean               Kronecker algebra, CHSH decomp (116 lines)
│   ├── InvolutionNorm.lean                dot-product preservation (65 lines)
│   ├── TsirelsonBound.lean                ‖𝒞ψ‖² ≤ 8 (167 lines)
│   └── Main.lean                          assembly + #print axioms (52 lines)
├── paper11_writeup.tex                    LaTeX source (v1.1)
└── paper11_writeup.pdf                    compiled paper (21 pages)
```

**Total formalization:** 639 lines, 8 modules, zero sorry, zero errors.

---

## Main Results

**Part A — Tsirelson Bound (BISH):**
For any self-adjoint involutions A, A', B, B' on ℂ² and unit vector ψ ∈ ℂ⁴:
‖𝒞ψ‖² ≤ 8 (equivalently |⟨ψ, 𝒞ψ⟩| ≤ 2√2).

**Part B — Bell State Entropy (BISH):**
The partial trace of the Bell singlet density matrix yields ρ_A = ½I
with von Neumann entropy S(ρ_A) = log 2 (maximal qubit entanglement).

---

## Axiom Profile

```
#print axioms tsirelson_bound
-- [propext, Classical.choice, Quot.sound]

#print axioms bell_maximal_entanglement
-- [propext, Classical.choice, Quot.sound]
```

No custom axioms. The `Classical.choice` dependency enters through Mathlib's
typeclass infrastructure (Decidable instances on ℝ/ℂ), not from the
mathematical content. The BISH calibration is established by proof-content
analysis: all proof steps are finite-dimensional matrix algebra.

Paper 11 is classified as "structurally verified" in the series certification
framework (Paper 10, forthcoming).

---

## Toolchain

| Component | Version / Commit |
|-----------|-----------------|
| Lean 4 | v4.28.0-rc1 |
| Mathlib4 | `2d9b14086f3a61c13a5546ab27cb8b91c0d76734` |

---

## Citation

```bibtex
@unpublished{Lee2026Paper11,
  author = {Lee, Paul Chun-Kit},
  title  = {The Constructive Cost of Quantum Entanglement:
            {Tsirelson} Bound and {Bell} State Entropy in {Lean}~4},
  year   = {2026},
  note   = {Preprint, v1.1},
  doi    = {10.5281/zenodo.18527676},
  url    = {https://github.com/quantmann/FoundationRelativity}
}
```

---

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
