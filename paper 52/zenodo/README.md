# Paper 52: Decidability Transfer via Specialization

**DOI:** [10.5281/zenodo.18732559](https://doi.org/10.5281/zenodo.18732559)

Paper 52 of the Constructive Reverse Mathematics series. We prove that Standard Conjecture D (numerical equivalence implies homological equivalence) for abelian varieties of dimension g <= 3 follows from the Tate conjecture for divisors and the structural properties of the Lefschetz ring over finite fields, without invoking Standard Conjecture B or characteristic-0 Hodge theory.

The proof transfers decidability from characteristic p to characteristic 0 via the Fulton specialization map. The logical transfer architecture is formalized in Lean 4 over Mathlib; the bundle compiles with 0 errors, 0 warnings, and 0 sorry's, using **zero custom axioms**.

## Main Results

| Theorem | Statement | Strength |
|---------|-----------|----------|
| Theorem 1.1 (decidability_transfer_g_le_3) | Standard Conjecture D for g <= 3 | BISH (from 3 hypotheses) |
| Core Lemma (sub_lefschetz_non_degenerate) | Anisotropic decomposition => U cap U-perp = {0} | BISH (full proof) |
| Theorem 1.2 (sharp_boundary_g_eq_4) | Sharp boundary at g = 4 | BISH (negative) |

## Build Instructions

### Lean 4 bundle

```bash
cd P52_DecidabilityTransfer
lake build
```

- Lean 4 version: v4.29.0-rc1 (pinned in `lean-toolchain`)
- Mathlib dependency resolved via lakefile.lean
- Expected: 0 errors, 0 warnings, 0 sorry

### LaTeX paper

```bash
pdflatex paper52_decidability_transfer.tex
pdflatex paper52_decidability_transfer.tex   # second pass for cross-references
```

## File Structure

```
zenodo/
  README.md                       -- this file
  REPRODUCIBILITY.md              -- detailed reproducibility information
  .zenodo.json                    -- Zenodo metadata
  zenodo_metadata.txt             -- Zenodo metadata (text format)
  paper52_decidability_transfer.tex   -- LaTeX source
  paper52_decidability_transfer.pdf   -- compiled paper (17 pages)
  P52_DecidabilityTransfer/           -- Lean 4 bundle
    lean-toolchain
    lakefile.lean
    lake-manifest.json
    Papers.lean
    Papers/P52_DecidabilityTransfer/
      Core/SubLefschetzNonDegenerate.lean  -- 111 lines: core theorem (full proof)
      Defs/GeometricAxioms.lean            --  88 lines: GeometricData, Prop22/Prop21/LefschetzArch
      Main/DecidabilityTransfer.lean       --  81 lines: 7-step connected proof
      Main/AxiomAudit.lean                 --  89 lines: #print axioms verification
```

Total: 369 lines of Lean 4 over 4 source files.

## Axiom Audit

| Theorem | Custom Axioms | Sorry | Infrastructure Axioms |
|---------|---------------|-------|-----------------------|
| `sub_lefschetz_non_degenerate` | **0** | 0 | propext, Classical.choice, Quot.sound |
| `decidability_transfer_g_le_3` | **0** (3 geometric inputs as hypotheses) | 0 | propext, Classical.choice, Quot.sound |
| `sharp_boundary_g_eq_4` | **0** | 0 | (trivially True) |

**Key design:** The three geometric inputs (Propositions 2.1, 2.2, and the Lefschetz architecture) are passed as *hypotheses*, not axioms. Both theorems are pure logical implications with zero custom axioms. The core lemma `sub_lefschetz_non_degenerate` is *invoked* (not assumed) as the bridge between the geometric hypotheses and the conclusion.

**Classical.choice** appears only from Lean/Mathlib infrastructure (Field K instance, Finset operations), not from any omniscience principle. No `Classical.dec` appears.

## Formalization Scope

**What is formalized:** The logical transfer architecture -- the 7-step deduction from three geometric hypotheses through the verified core lemma to Standard Conjecture D.

**What is not formalized:** The deep geometric content of Sections 4-5 (Lefschetz ring definiteness via Rosati involution, Hard Lefschetz over F_p, sub-Lefschetz stability, Tate's theorem for divisors). These enter as the three hypotheses of the main theorem.

## Series Context

Part of the Foundation Relativity series applying constructive reverse mathematics to mathematical physics and the Standard Conjectures program. See Paper 50 (Atlas Survey) for the full series overview.

## License

Code: Apache License 2.0. Paper: CC-BY 4.0.
