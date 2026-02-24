# Paper 29: Fekete's Subadditive Lemma is Equivalent to LPO

**A Lean 4 Formalization**

Paul Chun-Kit Lee, New York University

DOI: [10.5281/zenodo.18632776](https://doi.org/10.5281/zenodo.18632776)

---

## Quick Start

### Prerequisites

- **elan** (Lean version manager): https://github.com/leanprover/elan
- **Git** (required by Lake to fetch Mathlib)
- ~8 GB disk space (for Mathlib cache)

### Build and Verify

```bash
tar xzf P29_FeketeLPO.tar.gz
cd P29_FeketeLPO
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 29 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

### Verify Axiom Profile

After building, the axiom audits in `Main.lean` produce the following output:

```lean
-- Backward direction (no custom axioms):
#print axioms Papers.P29.lpo_of_fekete
-- [propext, Classical.choice, Quot.sound]

-- Full equivalence (two cited axioms):
#print axioms Papers.P29.fekete_iff_lpo
-- [propext, Classical.choice, Quot.sound, Papers.P29.bmc_of_lpo, Papers.P29.fekete_of_bmc]
```

### Compile the Paper

```bash
pdflatex paper29_fekete_lpo.tex    # first pass
pdflatex paper29_fekete_lpo.tex    # second pass (resolves references)
```

The precompiled `paper29_fekete_lpo.pdf` is included in this archive.

---

## File Organization

```
P29_FeketeLPO/
|-- ZENODO_README.md                 this file
|-- lakefile.lean                    Lake build configuration
|-- lean-toolchain                   Lean version pin (v4.28.0-rc1)
|-- lake-manifest.json               pinned dependency versions
|-- Papers.lean                      root import module
|-- Papers/P29_FeketeLPO/
|   |-- Defs.lean                   Core definitions: LPO, BMC, FeketeConvergence, encoding (87 lines)
|   |-- Indicator.lean              hasTrue/indicator properties: monotonicity, witnesses (118 lines)
|   |-- Subadditive.lean            Subadditivity + lower bound proofs (103 lines)
|   |-- Decision.lean               Main theorem: FeketeConvergence -> LPO (117 lines)
|   |-- Forward.lean                Axiomatized: LPO -> BMC -> FeketeConvergence (43 lines)
|   |-- Main.lean                   Assembly: FeketeConvergence <-> LPO + axiom audit (81 lines)
|-- paper29_fekete_lpo.tex           LaTeX source
|-- paper29_fekete_lpo.pdf           compiled paper
```

**Total formalization:** 549 lines of Lean 4 across 6 source files.

---

## Main Theorems

### The Equivalence

```lean
theorem fekete_iff_lpo : FeketeConvergence <-> LPO
```

Over BISH, Fekete's Subadditive Lemma (every subadditive sequence with
u(n)/n bounded below converges) is equivalent to the Limited Principle
of Omniscience.

### Backward Direction (fully proved)

```lean
theorem lpo_of_fekete (hFek : FeketeConvergence) : LPO
```

Given any binary sequence alpha, encode it into a mock free energy
F_n = -n * x_n where x_n = 1 iff exists k < n, alpha(k) = true.
F is subadditive with F_n/n >= -1. Apply Fekete to get limit L.
Evaluate at M = max(N_0, 2) and case-split on the Bool hasTrue(alpha, M):
- true: extract witness (exists n, alpha(n) = true)
- false: contradiction from disjoint epsilon-intervals (forall n, alpha(n) = false)

### Forward Direction (axiomatized)

```lean
axiom bmc_of_lpo : LPO -> BMC           -- Bridges-Vita 2006
axiom fekete_of_bmc : BMC -> FeketeConvergence  -- classical Fekete proof

theorem fekete_of_lpo : LPO -> FeketeConvergence :=
  fun h => fekete_of_bmc (bmc_of_lpo h)
```

---

## Axiom Profile

### Backward direction: Clean

`lpo_of_fekete` depends only on Lean's three foundational axioms:
`[propext, Classical.choice, Quot.sound]`. No LPO, WLPO, LLPO, or
custom axioms. The `Classical.choice` is an infrastructure artifact
of Mathlib's real number construction.

### Full equivalence: Two cited axioms

`fekete_iff_lpo` depends on `[propext, Classical.choice, Quot.sound,
Papers.P29.bmc_of_lpo, Papers.P29.fekete_of_bmc]`.

| Axiom | Citation |
|-------|----------|
| `bmc_of_lpo` | Bridges and Vita, *Techniques of Constructive Analysis* (2006), Theorem 2.1.5 |
| `fekete_of_bmc` | Classical Fekete proof; available in Mathlib as `Subadditive.tendsto_lim` |

---

## Physical Significance

This result establishes a three-tier hierarchy for thermodynamic-limit convergence:

| Route | Logical cost | Example |
|-------|-------------|---------|
| Exact solution (closed-form modulus) | BISH | 1D Ising (Papers 8, 9) |
| Cluster expansion (exponential decay) | BISH | High-temperature lattice gases |
| Generic subadditivity (Fekete) | LPO | This paper |

The LPO cost becomes ineliminable when explicit finite-size bounds are
unavailable—typically near phase transitions where correlation lengths diverge.

---

## Toolchain and Dependencies

| Component | Version / Commit |
|-----------|-----------------|
| Lean 4 | v4.28.0-rc1 |
| Mathlib4 | `2598404fe9e0a5aee87ffca4ff83e2d01b23b024` |

All dependency versions are pinned in `lake-manifest.json` for
exact reproducibility.

---

## Citation

### Paper 29 (this work)

```bibtex
@unpublished{Lee2026Paper29,
  author = {Lee, Paul Chun-Kit},
  title  = {Fekete's Subadditive Lemma is Equivalent to {LPO}:
            A {Lean}~4 Formalization},
  year   = {2026},
  note   = {Preprint. Lean~4 formalization},
  doi    = {10.5281/zenodo.18632776},
  url    = {https://github.com/quantmann/FoundationRelativity}
}
```

### Companion papers

```bibtex
@unpublished{Lee2026Paper8,
  author = {Lee, Paul Chun-Kit},
  title  = {The Logical Cost of the Thermodynamic Limit:
            {LPO}-Equivalence and {BISH}-Dispensability
            for the {1D} {Ising} Free Energy},
  year   = {2026},
  note   = {Paper 8 in the constructive reverse mathematics series},
  doi    = {10.5281/zenodo.18516813}
}

@unpublished{Lee2026Paper10,
  author = {Lee, Paul Chun-Kit},
  title  = {Logical Geography of Mathematical Physics:
            A Constructive Calibration Programme},
  year   = {2026},
  note   = {Paper 10 (synthesis)}
}
```

---

## Links

- **GitHub repository:** https://github.com/quantmann/FoundationRelativity
- **Paper 8 (companion):** DOI 10.5281/zenodo.18516813
- **Paper 10 (synthesis):** same repository
- **Mathlib4 documentation:** https://leanprover-community.github.io/mathlib4_docs/

---

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
