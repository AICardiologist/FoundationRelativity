# Paper 9: Formulation-Invariance of the Logical Cost of the Thermodynamic Limit

**A Combinatorial Proof for the 1D Ising Model**

**A Lean 4 Formalization**

Paul Chun-Kit Lee, New York University

DOI: [10.5281/zenodo.18517570](https://doi.org/10.5281/zenodo.18517570)

---

## Quick Start

### Prerequisites

- **elan** (Lean version manager): https://github.com/leanprover/elan
- **Git** (required by Lake to fetch Mathlib)
- ~8 GB disk space (for Mathlib cache)

### Build and Verify

```bash
tar xzf paper9_combinatorial_ising.tar.gz
cd paper9_combinatorial_ising
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 9 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

### Verify Axiom Profile

After building, the axiom audits in `Main.lean` and `PartB_Main.lean`
produce the following output:

```lean
-- Part A:
#print axioms Papers.P9.ising_1d_dispensability_combinatorial
-- [propext, Classical.choice, Quot.sound]

-- Part B backward direction:
#print axioms Papers.P9.lpo_of_bmc
-- [propext, Classical.choice, Quot.sound]

-- Part B equivalence:
#print axioms Papers.P9.lpo_iff_bmc
-- [propext, Classical.choice, Quot.sound, Papers.P9.bmc_of_lpo]
```

### Compile the Paper

```bash
pdflatex paper9_writeup.tex    # first pass
pdflatex paper9_writeup.tex    # second pass (resolves references)
```

The precompiled `paper9_writeup.pdf` (16 pages) is included in this archive.

---

## File Organization

```
paper9_combinatorial_ising/
|-- ZENODO_README.md                      this file
|-- lakefile.lean                         Lake build configuration
|-- lean-toolchain                        Lean version pin (v4.28.0-rc1)
|-- lake-manifest.json                    pinned dependency versions
|-- Papers.lean                           root import module
|-- Papers/P9_Combinatorial_Ising/
|   |-- Basic.lean                        Core defs: LPO, twoCosh, twoSinh, partitionFn (73 lines)
|   |-- CoshSinhProps.lean                2cosh > 2sinh > 0, tanh properties (118 lines)
|   |-- ParitySieve.lean                  Parity sieve identity (axiomatized; standard) (47 lines)
|   |-- PartitionIdentity.lean            Bond derivation: Z_N = (2cosh)^N + (2sinh)^N (57 lines)
|   |-- LogBounds.lean                    log(1+x) <= x, geometric decay (70 lines)
|   |-- FreeEnergyDecomp.lean             f_N decomposition (79 lines)
|   |-- ErrorBound.lean                   |f_N - f_inf| <= (1/N) r^N (70 lines)
|   |-- ComputeN0.lean                    constructive N_0 from beta, epsilon (54 lines)
|   |-- Main.lean                         Part A assembly + axiom audit (75 lines)
|   |-- SmokeTest.lean                    minimal import validation (10 lines)
|   |-- PartB_Defs.lean                   BMC, runMax, coupling, encoded seq (77 lines)
|   |-- PartB_RunMax.lean                 running maximum properties (103 lines)
|   |-- PartB_FreeEnergyAnti.lean         g(J) strictly anti-monotone (77 lines)
|   |-- PartB_CouplingSeq.lean            coupling monotonicity, bounds (76 lines)
|   |-- PartB_EncodedSeq.lean             -F non-decreasing, bounded (83 lines)
|   |-- PartB_Forward.lean                axiom: LPO -> BMC [BV06] (21 lines)
|   |-- PartB_Backward.lean               main theorem: BMC -> LPO (162 lines)
|   |-- PartB_Main.lean                   Part B assembly + axiom audit (67 lines)
|-- paper9_writeup.tex                    LaTeX source
|-- paper9_writeup.pdf                    compiled paper (16 pages)
```

**Total formalization:** 1319 lines of Lean 4 across 18 source files.

---

## Main Theorems

### Part A: Dispensability (Combinatorial Formulation)

```lean
theorem ising_1d_dispensability_combinatorial
    (beta : Real) (hbeta : 0 < beta) (eps : Real) (heps : 0 < eps) :
    exists N0 : Nat, 0 < N0 /\ forall N : Nat, N0 <= N -> (hN : 0 < N) ->
      |freeEnergyDensity beta N hN - freeEnergyInfVol beta| < eps
```

For every inverse temperature beta > 0 and tolerance epsilon > 0,
there exists a constructively computable N_0 such that for all N >= N_0,
the finite-volume free energy density f_N(beta) approximates the
infinite-volume value f_inf(beta) = -log(2 cosh beta) within epsilon.

The partition function Z_N = (2 cosh beta)^N + (2 sinh beta)^N is derived
combinatorially via bond variables and the parity sieve identity — NO
transfer matrices, eigenvalues, or linear algebra.

### Part B: LPO <-> BMC Equivalence

```lean
theorem lpo_iff_bmc : LPO <-> BMC
```

Over BISH, the Limited Principle of Omniscience is equivalent to
Bounded Monotone Convergence. The backward direction (BMC -> LPO)
is proved by encoding binary sequences into 1D Ising free energy
sequences and extracting decisions from convergence behavior.

---

## Axiom Profile

### Part A: Clean

`ising_1d_dispensability_combinatorial` depends only on Lean's three
foundational axioms: `[propext, Classical.choice, Quot.sound]`. No LPO,
WLPO, LLPO, or custom axioms.

### Part B backward direction: Clean

`lpo_of_bmc` depends only on `[propext, Classical.choice, Quot.sound]`.
BMC appears as a hypothesis, not an axiom.

### Part B full equivalence: One cited axiom

`lpo_iff_bmc` depends on `[propext, Classical.choice, Quot.sound,
Papers.P9.bmc_of_lpo]`. The axiomatized `bmc_of_lpo` (LPO -> BMC)
cites Bridges and Vita, *Techniques of Constructive Analysis* (2006),
Theorem 2.1.5.

---

## Formulation-Invariance Note

This formalization is a companion to Paper 8, which proved the same two
results using the transfer matrix formulation. The key differences:

| Aspect | Paper 8 (Transfer Matrix) | Paper 9 (Combinatorial) |
|--------|--------------------------|------------------------|
| Z_N derived via | Tr(T^N) = lambda_+^N + lambda_-^N | Bond sums + parity sieve |
| Key identity | Spectral decomposition | Binomial parity extraction |
| Linear algebra | Matrix, trace, eigenvectors | **None** |
| Mathlib imports | `LinearAlgebra.Matrix.*` | **None from LinearAlgebra** |
| Naming | `transferEigenPlus`, `eigenRatio` | `twoCosh`, `tanhRatio` |
| Axiom profile | Identical | Identical |

The formulation-invariance constraint is enforced at the import level: no
file imports any module from `LinearAlgebra.Matrix.*`,
`LinearAlgebra.Eigenspace.*`, `Analysis.NormedSpace.*`, or
`Analysis.InnerProductSpace.*`.

---

## Toolchain and Dependencies

| Component | Version / Commit |
|-----------|-----------------|
| Lean 4 | v4.28.0-rc1 |
| Mathlib4 | `7091f0f601d5aaea565d2304c1a290cc8af03e18` |

All dependency versions are pinned in `lake-manifest.json` for
exact reproducibility.

---

## Citation

### Paper 9 (this work)

```bibtex
@unpublished{Lee2026Paper9,
  author = {Lee, Paul Chun-Kit},
  title  = {Formulation-Invariance of the Logical Cost of the
            Thermodynamic Limit: A Combinatorial Proof for the
            {1D} {Ising} Model},
  year   = {2026},
  note   = {Preprint. Lean~4 formalization},
  doi    = {10.5281/zenodo.18517570},
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
```

---

## Links

- **GitHub repository:** https://github.com/quantmann/FoundationRelativity
- **Paper 8 (companion):** same repository, `paper 8/`
- **Paper 2 (companion):** same repository, `paper_2_bundle/`
- **Paper 7 (companion):** same repository, `paper_7_bundle/`
- **Mathlib4 documentation:** https://leanprover-community.github.io/mathlib4_docs/

---

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
