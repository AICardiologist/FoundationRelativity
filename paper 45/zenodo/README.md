# Paper 45: Weight-Monodromy Conjecture and LPO

**DOI:** [10.5281/zenodo.18676170](https://doi.org/10.5281/zenodo.18676170)

Paper 45 of the Constructive Reverse Mathematics series. We apply CRM to calibrate the logical strength of spectral sequence degeneration in the context of the Weight-Monodromy Conjecture (WMC) for smooth projective varieties over p-adic fields.

## Main Results

| Theorem | Statement | Strength |
|---------|-----------|----------|
| C1 | Polarization forces degeneration | BISH (full proof) |
| C2 | DecidesDegeneration(K) <-> LPO(K) | BISH (full proof) |
| C3 | No positive-definite Hermitian form over Q_p in dim >= 3 | BISH (from axioms) |
| C4 | Geometric degeneration decidable in BISH | BISH (from axioms) |

The gap between C2 and C4 is the *de-omniscientizing descent*: geometric origin descends the coefficient field from undecidable Q_l to decidable Q-bar.

## Build Instructions

### Lean 4 bundle

```bash
cd P45_WMC
lake build
```

- Lean 4 version: v4.28.0
- Mathlib dependency resolved via lakefile.lean
- Expected: 0 errors, 0 warnings, 0 sorry

### LaTeX paper

```bash
pdflatex paper45.tex
pdflatex paper45.tex   # second pass for cross-references
```

## File Structure

```
zenodo/
  README.md                 -- this file
  REPRODUCIBILITY.md        -- detailed reproducibility information
  LICENSE                   -- Apache 2.0
  .zenodo.json              -- Zenodo metadata
  CITATION.cff              -- citation metadata
  paper45.tex               -- LaTeX source
  paper45.pdf               -- compiled paper
  P45_WMC/                  -- Lean 4 bundle
    lean-toolchain
    lakefile.lean
    lake-manifest.json
    Papers.lean
    Papers/P45_WMC/
      Defs.lean             -- 236 lines: definitions, infrastructure
      Sublemmas.lean        -- 156 lines: sub-lemmas 1-4 + bridge axioms
      Reduction.lean        --  97 lines: strong induction proof
      C1_Polarization.lean  --  78 lines: Theorem C1 (full proof)
      C2_LPO.lean           -- 121 lines: Theorem C2 (full proof)
      C3_Obstruction.lean   -- 140 lines: Theorem C3 (from axioms)
      C4_Descent.lean       -- 205 lines: Theorem C4 + descent
      Calibration.lean      --  84 lines: C1+C2+C3+C4 assembly
      Main.lean             -- 130 lines: root + axiom audit
```

Total: 1,247 lines of Lean 4 over 9 files.

## Axiom Audit

- 22 custom axioms (16 load-bearing, 6 documentary)
- Sub-lemma 5 (Arithmetic Kashiwara Conjecture) is NOT axiomatized; it appears as a hypothesis parameter, preserving conditionality
- 0 sorry
- Classical.choice appears only from Lean/Mathlib infrastructure (R and C as Cauchy completions), not from any omniscience principle

## Series Context

Part of the Foundation Relativity series applying constructive reverse mathematics to mathematical physics and the "five great conjectures" program. See Paper 50 (Atlas Survey) for the full series overview.

## License

Code: Apache License 2.0. Paper: CC-BY 4.0.
