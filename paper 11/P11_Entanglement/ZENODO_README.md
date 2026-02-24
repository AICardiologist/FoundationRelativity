# Paper 11: The Constructive Cost of Quantum Entanglement

**Tsirelson Bound and Bell State Entropy in Lean 4**

**A Lean 4 Formalization**

Paul Chun-Kit Lee, Independent Researcher, New York

DOI: [10.5281/zenodo.18521274](https://doi.org/10.5281/zenodo.18521274)

---

## Quick Start

### Prerequisites

- **elan** (Lean version manager): https://github.com/leanprover/elan
- **Git** (required by Lake to fetch Mathlib)
- ~8 GB disk space (for Mathlib cache)

### Build and Verify

```bash
tar xzf paper11_entanglement.tar.gz
cd paper11_entanglement
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 11 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

### Verify Axiom Profile

After building, the axiom audits in `Main.lean` produce the following output:

```lean
-- Part A: Tsirelson bound
#print axioms tsirelson_bound
-- [propext, Classical.choice, Quot.sound]

-- Part B: Bell state
#print axioms bell_partialTrace
-- [propext, Classical.choice, Quot.sound]

#print axioms bell_entropy
-- [propext, Classical.choice, Quot.sound]

#print axioms bell_maximal_entanglement
-- [propext, Classical.choice, Quot.sound]
```

### Compile the Paper

```bash
pdflatex paper11_writeup.tex    # first pass
pdflatex paper11_writeup.tex    # second pass (resolves references)
```

The precompiled `paper11_writeup.pdf` (20 pages) is included in this archive.

---

## File Organization

```
paper11_entanglement/
|-- ZENODO_README.md                 this file
|-- lakefile.lean                    Lake build configuration
|-- lean-toolchain                   Lean version pin (v4.28.0-rc1)
|-- lake-manifest.json               pinned dependency versions
|-- Papers.lean                      root import module
|-- Papers/P11_Entanglement/
|   |-- Defs.lean                    Core definitions: Involution, CHSH operator,
|   |                                Pauli matrices, partial trace, Bell state (85 lines)
|   |-- BinaryEntropy.lean           Binary entropy h(p), h(1/2) = log 2 (57 lines)
|   |-- PartialTrace.lean            Trace preservation lemmas (36 lines)
|   |-- BellState.lean               Bell density matrix, partial trace = (1/2)I,
|   |                                entropy = log 2 (61 lines)
|   |-- KroneckerLemmas.lean         Kronecker negation/subtraction, CHSH decomposition,
|   |                                sum-of-squares identity (116 lines)
|   |-- InvolutionNorm.lean          Dot-product preservation under involution
|   |                                Kronecker action (65 lines)
|   |-- TsirelsonBound.lean          Main bound: ||C*psi||^2 <= 8 (167 lines)
|   |-- Main.lean                    Assembly + axiom audit (52 lines)
|-- paper11_writeup.tex              LaTeX source
|-- paper11_writeup.pdf              compiled paper (20 pages)
```

**Total formalization:** 639 lines of Lean 4 across 8 source files.

---

## Main Theorems

### Part A: Tsirelson Bound

```lean
theorem tsirelson_bound (A A' B B' : Involution 2)
    (v : Fin 2 × Fin 2 → ℂ) (hv : star v ⬝ᵥ v = 1) :
    (star ((chshOperator A A' B B').mulVec v) ⬝ᵥ
     ((chshOperator A A' B B').mulVec v)).re ≤ 8
```

For any self-adjoint involutions A, A' (Alice) and B, B' (Bob) on ℂ²,
and any unit vector ψ ∈ ℂ² ⊗ ℂ² (i.e., star ψ ⬝ᵥ ψ = 1):
the squared dot-product norm of the CHSH operator applied to ψ
satisfies re(⟨Cψ, Cψ⟩) ≤ 8, equivalently ‖Cψ‖² ≤ 8,
which implies |⟨ψ, Cψ⟩| ≤ 2√2 via Cauchy-Schwarz.

The proof is entirely BISH-valid — no omniscience principle is required.

### Part B: Bell State Entanglement

```lean
theorem bell_partialTrace :
    partialTraceB bellDensityMatrix =
    (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
```

The partial trace of the Bell singlet density matrix |Ψ⁻⟩⟨Ψ⁻|
over subsystem B yields the maximally mixed qubit state (1/2)I.

```lean
theorem bell_entropy :
    binaryEntropy (1/2 : ℝ) = Real.log 2
```

The von Neumann entropy of the reduced Bell state equals log 2,
confirming maximal qubit entanglement.

```lean
theorem bell_maximal_entanglement :
    partialTraceB bellDensityMatrix =
      (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    binaryEntropy (1/2 : ℝ) = Real.log 2
```

Combined statement: the Bell singlet has maximal qubit entanglement.

---

## Axiom Profile

All theorems depend only on Lean's three standard infrastructure axioms:
`[propext, Classical.choice, Quot.sound]`. No custom axioms.

The `Classical.choice` dependency enters through Mathlib's typeclass
infrastructure (specifically `Decidable` instances for real number
comparisons), not from the mathematical content of the proofs. The
mathematical content is entirely BISH-valid.

---

## Toolchain and Dependencies

| Component | Version / Commit |
|-----------|-----------------|
| Lean 4 | v4.28.0-rc1 |
| Mathlib4 | `2d9b14086f3a61c13a5546ab27cb8b91c0d76734` |

All dependency versions are pinned in `lake-manifest.json` for
exact reproducibility.

---

## Citation

### Paper 11 (this work)

```bibtex
@unpublished{Lee2026Paper11,
  author = {Lee, Paul Chun-Kit},
  title  = {The Constructive Cost of Quantum Entanglement:
            {Tsirelson} Bound and {Bell} State Entropy
            in {Lean}~4},
  year   = {2026},
  note   = {Preprint. Lean~4 formalization},
  doi    = {10.5281/zenodo.18521274},
  url    = {https://github.com/quantmann/FoundationRelativity}
}
```

### Companion papers

```bibtex
@unpublished{Lee2026Paper2,
  author = {Lee, Paul Chun-Kit},
  title  = {{WLPO} Equivalence of the Bidual Gap in $\ell^1$:
            A {Lean}~4 Formalization},
  year   = {2026},
  note   = {Paper 2 in the constructive reverse mathematics series}
}

@unpublished{Lee2026Paper7,
  author = {Lee, Paul Chun-Kit},
  title  = {Non-Reflexivity of $S_1(H)$ Implies {WLPO}:
            A {Lean}~4 Formalization},
  year   = {2026},
  note   = {Paper 7 in the constructive reverse mathematics series}
}

@unpublished{Lee2026Paper8,
  author = {Lee, Paul Chun-Kit},
  title  = {The Logical Cost of the Thermodynamic Limit:
            {LPO}-Equivalence and {BISH}-Dispensability
            for the {1D} {Ising} Free Energy},
  year   = {2026},
  note   = {Paper 8 in the constructive reverse mathematics series},
  doi    = {10.5281/zenodo.18516813}
}
```

---

## Links

- **GitHub repository:** https://github.com/quantmann/FoundationRelativity
- **Paper 8 (companion):** same repository
- **Mathlib4 documentation:** https://leanprover-community.github.io/mathlib4_docs/

---

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
