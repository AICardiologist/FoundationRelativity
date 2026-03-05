# Paper 104: The Diagnostic Penumbra — CRM of Bayesian Clinical Decision-Making

**Paper 104, Clinical Sub-Series Paper B, of the Constructive Reverse Mathematics Series**

**Author:** Paul Chun-Kit Lee (New York University, Brooklyn, New York)

## Summary

Paper 104 applies Constructive Reverse Mathematics to the diagnostic testing pipeline: contingency tables, Bayesian inference, ROC analysis, and treatment threshold decisions. The central result identifies the **Diagnostic Penumbra** — the grey zone where the Bayesian posterior probability is too close to the treatment threshold for constructive resolution.

## Main Results

- **Theorem A (Diagnostic Penumbra):** The grey zone has width 2δ where δ = δ_prev + δ_cv (prevalence uncertainty + analytical imprecision).
- **Theorem B (Bayesian MP Requirement):** Posterior comparison with real prevalence requires BISH+MP (Markov's Principle).
- **Theorem C (ROC = LPO):** AUC comparison of two tests requires LPO; discrete trapezoidal AUC is BISH.
- **Theorem D (Discrete Bypass):** With rational cohort prevalence, the entire Bayesian chain is BISH.

## Pipeline Classification

| Stage | Component | CRM Level |
|-------|-----------|-----------|
| 1 | Contingency table (count data) | BISH |
| 2 | Test characteristics (sens, spec, PPV, NPV) | BISH |
| 3 | Likelihood ratios | BISH |
| 4 | Bayesian update (rational prevalence) | BISH |
| 5 | Bayesian update (real prevalence) | BISH+MP |
| 6 | Treatment threshold (rational utilities) | BISH |
| 7 | Treatment threshold (continuous utilities) | WKL |
| 8 | Clinical decision (rational posterior & τ) | BISH |
| 9 | ROC AUC comparison (continuous) | LPO |
| 10 | Test comparison (discrete ROC) | BISH |

**Total: 7 BISH + 1 BISH+MP + 1 WKL + 1 LPO = 10 stages (70% BISH)**

Isomorphic to Paper 103 (RCT Statistical Pipeline).

## Clinical Test Cases

1. **Troponin (ESC 0/1h):** 24.7% of chest pain presentations in the grey zone (5–52 ng/L). Mueller validation cohort, N = 7,998.
2. **D-dimer for PE:** Collapsed penumbra at low pretest probability (high sensitivity creates strong posterior separation).
3. **PSA screening:** Degenerate penumbra — the entire range is a grey zone (sensitivity ~27%).

## Lean 4 Bundle

### Build Instructions

```bash
cd "paper 104/P104_DiagnosticTesting"
lake build
```

### Requirements

- Lean toolchain: `leanprover/lean4:v4.29.0-rc2`
- Mathlib: `v4.29.0-rc2`

### Module Structure (10 files, 1,046 lines)

| File | Lines | Description |
|------|-------|-------------|
| OmnisciencePrinciples.lean | 69 | LPO, WLPO, MP definitions and implications |
| ContingencyTable.lean | 87 | 2×2 table, sensitivity, specificity, PPV, NPV |
| BayesianInference.lean | 101 | Rational/real posterior, MP requirement, discrete bypass |
| ROCAnalysis.lean | 82 | AUC as integral, discrete trapezoidal bypass |
| TreatmentThreshold.lean | 85 | Pauker-Kassirer model, rational/continuous utilities |
| DiagnosticPenumbra.lean | 117 | Grey zone characterisation, penumbra width |
| TroponinCalculations.lean | 147 | ESC 0/1h algorithm, Mueller cohort verification |
| ClinicalTestCases.lean | 127 | D-dimer for PE, PSA screening |
| CRMPipeline.lean | 94 | Pipeline classification, native_decide proofs |
| Paper104_Assembly.lean | 137 | Master theorem, axiom documentation |

### Axiom Inventory

**Documentary axioms (4):**
1. `real_posterior_comparison_requires_MP` — posterior comparison needs MP (Bishop-Bridges §2.3)
2. `auc_comparison_requires_LPO` — AUC comparison needs LPO (Bishop-Bridges §2.3)
3. `continuous_threshold_exists` — continuous τ* existence (Pauker-Kassirer)
4. `continuous_threshold_requires_WKL` — continuous τ* needs WKL (Paper 23)

**Infrastructure axioms:** `propext`, `Classical.choice`, `Quot.sound` (Lean/Mathlib standard).

**Sorries: 0**

### Dependencies

- Papers 103 (structural twin)
- Paper 98 (Archimedean Obstruction Thesis)
- Paper 23 (Fan Theorem / WKL)
