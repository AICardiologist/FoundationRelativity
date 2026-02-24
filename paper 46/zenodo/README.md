# Paper 46: The Tate Conjecture and LPO

**DOI:** [10.5281/zenodo.18682285](https://doi.org/10.5281/zenodo.18682285)

Paper 46 of the Constructive Reverse Mathematics series. We apply CRM to calibrate the logical strength of the Tate Conjecture for smooth projective varieties over finite fields, establishing four theorems (T1--T4) that classify which components require LPO and which are BISH-compatible.

## Main Results

| Theorem | Statement | Strength |
|---------|-----------|----------|
| T1 | Galois-invariance (membership in ker(Frob - I)) iff LPO(Q_l) | BISH <-> BISH+LPO |
| T2 | Numerical equivalence decidable via integer arithmetic | BISH (full proof) |
| T3 | Poincare pairing not anisotropic in dim >= 5 | BISH (from axioms) |
| T4a | Homological equivalence decidability requires LPO(Q_l) | BISH (full proof) |
| T4b | Standard Conjecture D converts hom_equiv to BISH-decidable num_equiv | BISH + SCD (from axioms) |

The key new result is T4: Standard Conjecture D is precisely the axiom that *de-omniscientizes* the morphism spaces of the motivic category, converting LPO-dependent homological equivalence testing to BISH-decidable numerical equivalence via integer arithmetic.

## Build Instructions

### Lean 4 bundle

```bash
cd P46_Tate
lake build
```

- Lean 4 version: v4.29.0-rc1
- Mathlib dependency resolved via lakefile.lean
- Expected: 0 errors, 0 warnings, 0 sorry

### LaTeX paper

```bash
pdflatex paper46.tex
pdflatex paper46.tex   # second pass for cross-references
```

## File Structure

```
zenodo/
  README.md                 -- this file
  REPRODUCIBILITY.md        -- detailed reproducibility information
  LICENSE                   -- Apache 2.0
  .zenodo.json              -- Zenodo metadata
  CITATION.cff              -- citation metadata
  paper46.tex               -- LaTeX source
  paper46.pdf               -- compiled paper
  P46_Tate/                 -- Lean 4 bundle
    lean-toolchain
    lakefile.lean
    lake-manifest.json
    Papers.lean
    Papers/P46_Tate/
      Defs.lean             -- 250 lines: definitions, axioms, infrastructure
      T1_GaloisLPO.lean     --  85 lines: Theorem T1 (full proof)
      T2_CycleVerify.lean   -- 100 lines: Theorem T2 (full proof)
      T3_Obstruction.lean   --  76 lines: Theorem T3 (from axioms)
      T4_ConjD.lean         -- 106 lines: Theorem T4 (full proof from axioms)
      Main.lean             -- 154 lines: root + axiom audit
```

Total: 771 lines of Lean 4 over 6 files.

## Axiom Audit

- 21 custom axioms (20 in Defs.lean, 1 in T4_ConjD.lean)
- Categories: infrastructure (types/instances), cycle class, Poincare pairing, calibration (encoding/bridge/isotropy), Standard Conjecture D
- Standard Conjecture D is an explicit axiom (an open conjecture); T4b's decidability result is conditional on it
- 0 sorry
- Classical.choice appears only from Lean/Mathlib infrastructure, not from any omniscience principle
- Classical.dec does NOT appear; decidability in T2 and T4b derives from Int.decEq and SCD

## Series Context

Part of the Foundation Relativity series applying constructive reverse mathematics to mathematical physics and the "five great conjectures" program. See Paper 50 (Atlas Survey) for the full series overview.

## License

Code: Apache License 2.0. Paper: CC-BY 4.0.
