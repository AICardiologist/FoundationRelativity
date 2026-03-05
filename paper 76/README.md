# Paper 76: CRMLint — An Automated Logical Cost Analyzer for Proof Assistants

**Paper 76, Constructive Reverse Mathematics Series**

Author: Paul Chun-Kit Lee (NYU)
Date: February 2026
DOI: [10.5281/zenodo.18777597](https://doi.org/10.5281/zenodo.18777597)

## Summary

CRMLint is a Lean 4 metaprogram that computes the Constructive Reverse Mathematics (CRM) logical cost of any declaration in the Mathlib library. The tool traces transitive dependencies to classical axioms, classifies each entry point by its CRM pattern (infrastructure artifact vs. essential classical content), and computes the CRM level as the join of essential costs over the hierarchy BISH < BISH+MP < LLPO < WLPO < LPO < CLASS.

The critical contribution is a type-aware classifier (v0.2) that correctly assigns WLPO to `Real.instField` where the naive v0.1 approach misclassified it as BISH. Calibration against 14 Lean 4 bundles from the CRM program yields correct classifications on all test cases. Namespace scans reveal conservation gaps across Mathlib: 70% of `Nat.Prime` and 60% of `Int.ModEq` are classified CLASS despite having BISH statements. Three such gaps are closed with 1–3 line constructive fixes.

## Main Results

| Result | Statement | CRM Level |
|--------|-----------|-----------|
| **Theorem A** | CRMLint correctly classifies all five calibration targets (Nat.add_comm: BISH, Int.add_comm: BISH, add_comm: BISH, zorn_le: CLASS, Real.instField: WLPO) | — |
| **Theorem B** | Type-aware Decidable classification: Decidable(x = y) costs BISH for N/Z/Q/Fin/Bool, WLPO for R/C, LPO for unbounded existentials | — |
| **Hypothesis C** | Conservation gap Delta(T) = proof_cost - statement_cost as heuristic for simpler proof existence | — |

## Contents

```
paper 76/
  paper76.tex                        LaTeX source
  paper76.pdf                        Compiled PDF (16 pages)
  README.md                          This file
  metadata.txt                       Zenodo metadata
  CRMLint/
    lean-toolchain                   leanprover/lean4:v4.29.0-rc2
    lakefile.lean                    Lake build configuration
    lake-manifest.json               Mathlib pin (aac298a)
    CRMLint.lean                     Root import file (6 lines)
    CRMLint/
      Defs.lean                      CRMLevel, ClassicalPattern, result types (168 lines)
      Trace.lean                     Layer 1: BFS classical dependency tracer (128 lines)
      Infrastructure.lean            BISH whitelist, analytic/quotient detection (142 lines)
      Classify.lean                  Layer 2: 12-rule priority classifier (267 lines)
      Report.lean                    Pretty-printing and namespace summaries (74 lines)
      Audit.lean                     #crm_audit, #crm_scan commands (161 lines)
    Test/
      Smoke.lean                     Basic smoke tests (35 lines)
      CaseStudies.lean               3 constructive replacements (129 lines)
      Mathlib.lean                   Mathlib calibration targets (62 lines)
      Scan.lean                      Namespace scan tests (26 lines)
      ScanNumberTheory.lean          Number theory scan (25 lines)
```

## How to Build (Lean)

Requires Lean 4 (v4.29.0-rc2) and an internet connection for Mathlib download.

```bash
cd CRMLint
lake update    # fetch Mathlib4 (first time only)
lake build     # builds CRMLint core (940 lines)
```

**0 sorry. 0 classical axioms in CRMLint's own code. CRMLint itself is BISH.**

## How to Test

```bash
cd CRMLint
lake env lean Test/Smoke.lean           # basic smoke tests
lake env lean Test/CaseStudies.lean     # 3 constructive gap closures
lake env lean Test/Mathlib.lean         # 5-point calibration suite
lake env lean Test/Scan.lean            # namespace scan
lake env lean Test/ScanNumberTheory.lean # Nat.Prime scan
```

## How to Build (LaTeX)

```bash
pdflatex paper76.tex
pdflatex paper76.tex   # second pass for references
```

Output: 16 pages, 0 errors.

## Axiom Inventory

CRMLint is a metaprogram, not a mathematical proof. Running `#print axioms` on any CRMLint definition returns the empty list. The test files import Mathlib and inherit Mathlib's axioms, but these enter only through the declarations being audited, not through CRMLint's own code.

| Component | CRM Cost | Mechanism |
|-----------|----------|-----------|
| Layer 1: BFS trace | BISH | Finite graph traversal |
| Layer 2: Pattern classification | BISH | String matching + type inspection |
| Layer 3: Concentration analysis | BISH | Array filter + fold |
| Infrastructure whitelist | BISH | Substring checks on discrete names |
| **CRMLint overall** | **BISH** | All layers constructive |

## Architecture

1. **Layer 1 (Trace.lean):** BFS through Lean 4 `Environment`, collects (axiomName, callerName) pairs
2. **Layer 2 (Classify.lean):** 12-rule priority classifier with root-context type analysis
3. **Layer 3 (Audit.lean):** Infrastructure/essential split, level = join of essential costs
4. **Layer 4 (future):** Conservation gap detection, DAG surgery, LLM-guided reproof

## Series Context

Paper 76 automates the manual CRM audit methodology developed across Papers 1–75:
- **Papers 1–75:** Manual CRM classification of theorems across mathematics and physics
- **Paper 75:** Conservation gap detection (Genestier–Lafforgue GL LLC calibration)
- **Paper 76:** CRMLint automated analysis (this paper)
- **Paper 77:** Automated constructivisation via CRMLint Squeeze

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)
Copyright 2026 Paul Chun-Kit Lee

## Acknowledgments

Lean 4 formalization uses Mathlib4; we thank the Mathlib contributors.
This paper was drafted with AI assistance (Claude, Anthropic).
The formal verification was developed and checked with Claude (Anthropic).
