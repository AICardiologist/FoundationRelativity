# Paper 53: The CM Decidability Oracle

**DOI:** [10.5281/zenodo.18713089](https://doi.org/10.5281/zenodo.18713089)

Paper 53 of the Constructive Reverse Mathematics series. We exhibit a verified decision procedure for numerical equivalence on products of the 13 CM elliptic curves over Q with class number 1, then extend the computation to the dimension-4 boundary where the DPT framework's decidability fails due to exotic Weil classes escaping the Lefschetz ring.

## Main Results

| Theorem | Statement | Strength |
|---------|-----------|----------|
| A | CM decidability oracle for all 13 discriminants | BISH (from 1 axiom) |
| B | DPT certificates: all 3 axioms verified computationally | BISH (from 1 axiom) |
| C | Fourfold boundary: deg(w . w) = 7 > 0 (Hodge-Riemann satisfied) | BISH (pure arithmetic, **no custom axioms**) |
| D | DPT decidability boundary at dimension 4 | Documentary |

Theorem C is the key result: the fourfold sign computation is pure verified arithmetic, depending on no custom axioms at all. The exotic Weil class is healthy (positive self-intersection, algebraic, Hodge-Riemann satisfied) but invisible to the Lefschetz-based decidability machinery.

## Build Instructions

### Lean 4 bundle

```bash
cd P53_CMOracle
lake build
```

- Lean 4 version: v4.29.0-rc1 (pinned in `lean-toolchain`)
- Mathlib dependency resolved via lakefile.lean
- Expected: 0 errors, 0 warnings, 0 sorry

### LaTeX paper

```bash
pdflatex paper53_cm_oracle.tex
pdflatex paper53_cm_oracle.tex   # second pass for cross-references
pdflatex paper53_cm_oracle.tex   # third pass for ToC
```

## File Structure

```
zenodo/
  README.md                 -- this file
  REPRODUCIBILITY.md        -- detailed reproducibility information
  LICENSE                   -- Apache 2.0
  .zenodo.json              -- Zenodo metadata
  CITATION.cff              -- citation metadata
  paper53_cm_oracle.tex     -- LaTeX source
  paper53_cm_oracle.pdf     -- compiled paper (15 pages)
  P53_CMOracle/             -- Lean 4 bundle
    lean-toolchain
    lakefile.lean
    lake-manifest.json
    Papers.lean
    Papers/P53_CMOracle/
      CMData.lean              -- 134 lines: quadratic field arithmetic, 13 CM discriminants
      EndomorphismRing.lean    --  75 lines: CM generators for each D
      CycleAlgebra.lean        --  88 lines: cycles on E x E as Q^4 vectors
      IntersectionPairing.lean -- 105 lines: 4x4 intersection matrix, axioms
      Decider.lean             -- 106 lines: Boolean oracle, correctness axiom
      RosatiCheck.lean         -- 167 lines: positive-definiteness via Sylvester
      Examples.lean            -- 149 lines: #eval demonstrations
      Main.lean                -- 142 lines: Theorems A, B, C, D, axiom audit
      WeilType.lean            --  67 lines: WeilHermitian structure, det, signature
      WeilClass.lean           --  52 lines: eigenspace decomposition, isotropy axioms
      CrossPairing.lean        -- 101 lines: cross-pairing formula, B^2(X) form
      RegressionTest.lean      -- 121 lines: J x J conic verification
      MilneExample.lean        --  73 lines: Milne fourfold H = diag(1,-1,-1,1)
      SignComputation.lean     --  95 lines: Tr(c) computation, Hodge-Riemann check
      BoundaryTheorem.lean     -- 122 lines: Theorems C, D, certificate structure
```

Total: 1,597 lines of Lean 4 over 15 files.

## Axiom Audit

- 10 principled axioms (5 load-bearing, 5 documentary)
- 0 sorry
- Classical.choice appears only from Lean/Mathlib infrastructure (R and C as Cauchy completions), not from any omniscience principle

| # | Axiom | Source | Status |
|---|-------|--------|--------|
| 1 | `basis_spans_CH1_E2` | Betti number computation | Load-bearing |
| 2 | `lieberman_hom_eq_num` | Lieberman 1968 | Load-bearing |
| 3 | `norm_formula_intersection` | CM intersection theory | Load-bearing |
| 4 | `intersectionMatrix_E2_correct` | Fulton 1998 | Load-bearing |
| 5 | `decider_correct` | Summary of 1-4 | Load-bearing |
| 6 | `hermitian_form_van_geemen` | van Geemen CIME 1994 | Documentary |
| 7 | `eigenspace_isotropic` | van Geemen CIME 1994 | Documentary |
| 8 | `cross_pairing_formula` | van Geemen CIME 1994 | Documentary |
| 9 | `milne_cm_type_hermitian` | Milne 2001, Ex. 1.8 | Documentary |
| 10 | `schoen_algebraicity` | Schoen 1988 | Documentary |

## Series Context

Part of the Foundation Relativity series applying constructive reverse mathematics to mathematical physics and the "five great conjectures" program. Papers 50 and 52 develop the DPT (Decidable Polarized Tannakian) framework; the present paper provides the first verified implementation and identifies the dimension-4 boundary. See Paper 50 (Atlas Survey) for the full series overview.

## License

Code: Apache License 2.0. Paper: CC-BY 4.0.
