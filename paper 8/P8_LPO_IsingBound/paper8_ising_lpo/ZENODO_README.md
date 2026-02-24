# Paper 8: The Logical Cost of the Thermodynamic Limit

**LPO-Equivalence and BISH-Dispensability for the 1D Ising Free Energy**

**A Lean 4 Formalization**

Paul Chun-Kit Lee, New York University

DOI: [10.5281/zenodo.18516813](https://doi.org/10.5281/zenodo.18516813)

---

## Quick Start

### Prerequisites

- **elan** (Lean version manager): https://github.com/leanprover/elan
- **Git** (required by Lake to fetch Mathlib)
- ~8 GB disk space (for Mathlib cache)

### Build and Verify

```bash
tar xzf paper8_ising_lpo.tar.gz
cd paper8_ising_lpo
lake exe cache get       # downloads prebuilt Mathlib (~5 min)
lake build               # compiles Paper 8 source files (~2-5 min)
```

A successful build produces 0 errors, 0 warnings, and 0 sorries.

### Verify Axiom Profile

After building, the axiom audits in `Main.lean` and `PartB_Main.lean`
produce the following output:

```lean
-- Part A:
#print axioms Papers.P8.ising_1d_dispensability
-- [propext, Classical.choice, Quot.sound]

-- Part B backward direction:
#print axioms Papers.P8.lpo_of_bmc
-- [propext, Classical.choice, Quot.sound]

-- Part B equivalence:
#print axioms Papers.P8.lpo_iff_bmc
-- [propext, Classical.choice, Quot.sound, Papers.P8.bmc_of_lpo]
```

### Compile the Paper

```bash
pdflatex paper8_writeup.tex    # first pass
pdflatex paper8_writeup.tex    # second pass (resolves references)
```

The precompiled `paper8_writeup.pdf` (17 pages) is included in this archive.

---

## File Organization

```
paper8_ising_lpo/
|-- ZENODO_README.md                 this file
|-- lakefile.lean                    Lake build configuration
|-- lean-toolchain                   Lean version pin (v4.28.0-rc1)
|-- lake-manifest.json               pinned dependency versions
|-- Papers.lean                      root import module
|-- Papers/P8_LPO_IsingBound/
|   |-- Basic.lean                   Core definitions: LPO, eigenvalues, free energy (67 lines)
|   |-- EigenvalueProps.lean         eigenvalue properties, tanh bounds (119 lines)
|   |-- LogBounds.lean               log(1+x) <= x, geometric decay (70 lines)
|   |-- TransferMatrix.lean          2x2 transfer matrix, projectors (117 lines)
|   |-- PartitionTrace.lean          Bonus: Tr(T^N) = lambda_+^N + lambda_-^N (64 lines)
|   |-- FreeEnergyDecomp.lean        f_N decomposition (87 lines)
|   |-- ErrorBound.lean              |f_N - f_inf| <= (1/N) r^N (72 lines)
|   |-- ComputeN0.lean              constructive N_0 from beta, epsilon (54 lines)
|   |-- Main.lean                    Part A assembly + axiom audit (72 lines)
|   |-- SmokeTest.lean              minimal import validation (7 lines)
|   |-- PartB_Defs.lean             BMC, runMax, coupling, encoded seq (76 lines)
|   |-- PartB_RunMax.lean           running maximum properties (103 lines)
|   |-- PartB_FreeEnergyAnti.lean   g(J) strictly anti-monotone (73 lines)
|   |-- PartB_CouplingSeq.lean      coupling monotonicity, bounds (76 lines)
|   |-- PartB_EncodedSeq.lean       -F non-decreasing, bounded (83 lines)
|   |-- PartB_Forward.lean          axiom: LPO -> BMC [BV06] (21 lines)
|   |-- PartB_Backward.lean         main theorem: BMC -> LPO (154 lines)
|   |-- PartB_Main.lean             Part B assembly + axiom audit (58 lines)
|-- paper8_writeup.tex               LaTeX source
|-- paper8_writeup.pdf               compiled paper (17 pages)
```

**Total formalization:** 1374 lines of Lean 4 across 18 source files.

---

## Main Theorems

### Part A: Dispensability

```lean
theorem ising_1d_dispensability
    (beta : Real) (hbeta : 0 < beta) (eps : Real) (heps : 0 < eps) :
    exists N0 : Nat, 0 < N0 /\ forall N : Nat, N0 <= N -> (hN : 0 < N) ->
      |freeEnergyDensity beta N hN - freeEnergyInfVol beta| < eps
```

For every inverse temperature beta > 0 and tolerance epsilon > 0,
there exists a constructively computable N_0 such that for all N >= N_0,
the finite-volume free energy density f_N(beta) approximates the
infinite-volume value f_inf(beta) = -log(2 cosh beta) within epsilon.
The proof is entirely BISH-valid — no omniscience principle is required.

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

`ising_1d_dispensability` depends only on Lean's three foundational axioms:
`[propext, Classical.choice, Quot.sound]`. No LPO, WLPO, LLPO, or
custom axioms.

### Part B backward direction: Clean

`lpo_of_bmc` depends only on `[propext, Classical.choice, Quot.sound]`.
BMC appears as a hypothesis, not an axiom.

### Part B full equivalence: One cited axiom

`lpo_iff_bmc` depends on `[propext, Classical.choice, Quot.sound,
Papers.P8.bmc_of_lpo]`. The axiomatized `bmc_of_lpo` (LPO -> BMC)
cites Bridges and Vita, *Techniques of Constructive Analysis* (2006),
Theorem 2.1.5.

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

### Paper 8 (this work)

```bibtex
@unpublished{Lee2026Paper8,
  author = {Lee, Paul Chun-Kit},
  title  = {The Logical Cost of the Thermodynamic Limit:
            {LPO}-Equivalence and {BISH}-Dispensability
            for the {1D} {Ising} Free Energy},
  year   = {2026},
  note   = {Preprint. Lean~4 formalization},
  doi    = {10.5281/zenodo.18516813},
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
```

---

## Links

- **GitHub repository:** https://github.com/quantmann/FoundationRelativity
- **Paper 2 (companion):** same repository, `paper_2_bundle/`
- **Paper 7 (companion):** same repository, `paper_7_bundle/`
- **Mathlib4 documentation:** https://leanprover-community.github.io/mathlib4_docs/

---

## License

Apache 2.0 (code) / CC-BY 4.0 (paper).
