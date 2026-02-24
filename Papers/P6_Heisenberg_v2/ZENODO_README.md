# Paper 6 v2: Constructive Reverse Mathematics for the Heisenberg Uncertainty Principle

**Robertson--Schrodinger and Schrodinger Inequalities over Mathlib**

**A Lean 4 Formalization (2nd Edition)**

Paul Chun-Kit Lee, New York University

DOI: [10.5281/zenodo.18519836](https://doi.org/10.5281/zenodo.18519836)

---

## Quick Start

### Prerequisites

- **elan** (Lean version manager): https://github.com/leanprover/elan
- **Git** (required by Lake to fetch Mathlib)
- ~8 GB disk space (for Mathlib cache)

### Build and Verify

```bash
tar xzf paper6_heisenberg_v2.tar.gz
cd P6_Heisenberg_v2
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 6 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

### Verify Axiom Profile

After building, the axiom audits in `Main.lean` produce the following output:

```lean
#print axioms Papers.P6_Heisenberg.robertson_schrodinger
-- [propext, Classical.choice, Quot.sound]

#print axioms Papers.P6_Heisenberg.schrodinger
-- [propext, Classical.choice, Quot.sound]

#print axioms Papers.P6_Heisenberg.measurement_uncertainty_requires_dcω
-- 'Papers.P6_Heisenberg.measurement_uncertainty_requires_dcω' does not depend on any axioms
```

### Compile the Paper

```bash
pdflatex paper6_heisenberg_v2.tex    # first pass
pdflatex paper6_heisenberg_v2.tex    # second pass (resolves references)
```

The precompiled `paper6_heisenberg_v2.pdf` is included in this archive.

---

## File Organization

```
P6_Heisenberg_v2/
|-- ZENODO_README.md                 this file
|-- lakefile.lean                    Lake build configuration
|-- lean-toolchain                   Lean version pin (v4.28.0-rc1)
|-- lake-manifest.json               pinned dependency versions
|-- Papers.lean                      root import module
|-- Papers/P6_Heisenberg/
|   |-- Basic.lean                   operator defs, bridge lemmas (193 lines)
|   |-- RobertsonSchrodinger.lean    main theorems (133 lines)
|   |-- MeasurementUncertainty.lean  DCw definition + measurement (46 lines)
|   |-- Main.lean                    aggregator + axiom audit (35 lines)
|-- paper6_heisenberg_v2.tex         LaTeX source
|-- paper6_heisenberg_v2.pdf         compiled paper
```

**Total formalization:** ~420 lines of Lean 4 across 4 source files.

---

## Main Theorems

### Robertson--Schrodinger Inequality (Height 0)

```lean
theorem robertson_schrodinger (A B : Op E) (ψ : E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hψ : ‖ψ‖ = 1) :
    ‖expect (comm A B) ψ‖ ^ 2 ≤ 4 * (var A ψ * var B ψ)
```

For self-adjoint operators A, B and unit vector psi:
|<[A,B]>|^2 <= 4 * Var(A) * Var(B).

### Schrodinger Inequality (Height 0)

```lean
theorem schrodinger (A B : Op E) (ψ : E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hψ : ‖ψ‖ = 1) :
    ‖expect (comm A B) ψ‖ ^ 2 +
    ‖expect (acomm A B) ψ - 2 * expect A ψ * expect B ψ‖ ^ 2
      ≤ 4 * (var A ψ * var B ψ)
```

Strengthening of Robertson--Schrodinger with the anticommutator term.

### Measurement Uncertainty (Height <= DCw)

```lean
theorem measurement_uncertainty_requires_dcω
    (Outcome : Type) (prepare : Unit → Outcome) :
    DCω → ∃ h : MeasHistory Outcome, ∀ n, h.outcomes n = prepare ()
```

Construction of infinite measurement histories requires Dependent Choice.

---

## Axiom Profile

The formalization has **zero custom axioms**. All mathematical
prerequisites come from Mathlib.

- **robertson_schrodinger**: `[propext, Classical.choice, Quot.sound]`
- **schrodinger**: `[propext, Classical.choice, Quot.sound]`
- **measurement_uncertainty_requires_dcw**: does not depend on any axioms

The `Classical.choice` appearance is a Mathlib infrastructure artifact:
`InnerProductSpace` and `ContinuousLinearMap.adjoint` use it transitively
through the Riesz representation theorem and norm completions. The
mathematical content of the proofs is constructive (Cauchy--Schwarz +
algebraic identities).

---

## What Changed from v1

| Aspect | v1 (AxCal, 2025) | v2 (CRM, 2026) |
|--------|------------------|-----------------|
| Framework | AxCal (mathlib-free) | CRM over Mathlib |
| Custom axioms | 71 | 0 |
| Lines of code | ~960 | ~420 |
| Dependencies | None (self-contained) | Mathlib4 |
| Sorry count | 0 | 0 |

Version 1 used the Axiom Calibration framework where all mathematical
prerequisites were axiomatized as Prop-level signatures. Version 2
replaces every custom axiom with a Mathlib proof.

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

### Paper 6 v2 (this work)

```bibtex
@unpublished{Lee2026Paper6v2,
  author = {Lee, Paul Chun-Kit},
  title  = {Constructive Reverse Mathematics for the {Heisenberg}
            Uncertainty Principle: {Robertson}--{Schr\"odinger}
            and {Schr\"odinger} Inequalities over {Mathlib}},
  year   = {2026},
  note   = {Paper~6, v2. Lean~4 formalization over Mathlib},
  doi    = {10.5281/zenodo.18519836},
  url    = {https://github.com/quantmann/FoundationRelativity}
}
```

### Paper 6 v1 (predecessor)

```bibtex
@unpublished{Lee2025Paper6v1,
  author = {Lee, Paul Chun-Kit},
  title  = {Axiom Calibration for the {Heisenberg} Uncertainty
            Principle: Preparation vs.\ Measurement},
  year   = {2025},
  note   = {Paper~6, v1. Lean~4 formalization (AxCal)},
  doi    = {10.5281/zenodo.17068179}
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
  doi    = {10.5281/zenodo.18509795}
}

@unpublished{Lee2026Paper8,
  author = {Lee, Paul Chun-Kit},
  title  = {The Logical Cost of the Thermodynamic Limit:
            {LPO}-Equivalence and {BISH}-Dispensability
            for the {1D} {Ising} Free Energy},
  year   = {2026},
  doi    = {10.5281/zenodo.18516813}
}
```

---

## Links

- **GitHub repository:** https://github.com/quantmann/FoundationRelativity
- **Paper 6 v1 (predecessor):** https://zenodo.org/records/17068179
- **Paper 7 (companion):** same repository, `paper_7_bundle/`
- **Paper 8 (companion):** same repository, `paper 8/P8_LPO_IsingBound/`
- **Mathlib4 documentation:** https://leanprover-community.github.io/mathlib4_docs/

---

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
