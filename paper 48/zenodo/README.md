# Paper 48: The Birch and Swinnerton-Dyer Conjecture and LPO

**DOI:** [10.5281/zenodo.18683400](https://doi.org/10.5281/zenodo.18683400)

Paper 48 of the Constructive Reverse Mathematics series. We apply CRM to calibrate the logical strength of the Birch and Swinnerton-Dyer (BSD) conjecture for elliptic curves over Q. The central finding: BSD is the first conjecture in the five-conjecture atlas where the Archimedean polarization is available — Papers 45-47 proved it is blocked at every finite prime.

## Main Results

| Theorem | Statement | Strength |
|---------|-----------|----------|
| B1 | Zero-testing L(E,1) = 0 is equivalent to LPO(R) | LPO (definitional) |
| B2 | Neron-Tate height is positive-definite (Archimedean polarization) | BISH (from axioms) |
| B3 | Regulator Reg_E = det(Neron-Tate) > 0 | BISH (from axioms) |
| B4 | p-adic height NOT positive-definite for rank >= 5 (u(Q_p) = 4) | BISH (from axioms) |

The analytic side of BSD calibrates at LPO; the algebraic side is BISH. The Archimedean polarization (Neron-Tate height) provides the constructive escape from the u-invariant obstruction that blocks Papers 45-47.

## Build Instructions

### Lean 4 bundle

```bash
cd P48_BSD
lake update && lake build
```

- Lean 4 version: v4.29.0-rc1
- Mathlib dependency resolved via lakefile.lean
- Expected: 0 errors, 0 warnings, 0 sorry

### LaTeX paper

```bash
pdflatex paper48.tex
pdflatex paper48.tex   # second pass for cross-references
```

## File Structure

```
zenodo/
  README.md                 -- this file
  LICENSE                   -- Apache 2.0
  paper48.tex               -- LaTeX source
  paper48.pdf               -- compiled paper
  P48_BSD/                  -- Lean 4 bundle
    lean-toolchain
    lakefile.lean
    lake-manifest.json
    Papers.lean
    Papers/P48_BSD/
      Defs.lean             -- 107 lines: definitions, 9 axioms, LPO, regulator
      B1_AnalyticLPO.lean   --  72 lines: Theorem B1 (LPO <-> zero-testing)
      B2_Polarization.lean  --  67 lines: Theorem B2 (PosDef -> InnerProductSpace)
      B3_Regulator.lean     --  44 lines: Theorem B3 (det > 0 via det_pos)
      B4_PadicContrast.lean --  72 lines: Theorem B4 (p-adic obstruction)
      Main.lean             -- 124 lines: assembly + #print axioms audit
```

Total: 486 lines of Lean 4 over 6 files.

## Axiom Audit

- 9 custom axioms (7 load-bearing, 1 documentary, 1 instance)
- 0 sorry
- Classical.choice appears only from Lean/Mathlib infrastructure (R as Cauchy completion), not from any omniscience principle
- B1 (zero_test_iff_LPO): no custom axioms
- B2, B3: only neron_tate_matrix + neron_tate_pos_def
- B4: Q_p, Q_p_field, padic_height, padic_form_isotropic

## Series Context

Part of the Foundation Relativity series applying constructive reverse mathematics to the "five great conjectures" program. Paper 48 is the Archimedean counterpart of Papers 45-47 (Weight-Monodromy, Tate, Finite Mordell). See Paper 50 (Atlas Survey) for the full series overview.

## License

Code: Apache License 2.0. Paper: CC-BY 4.0.
