# Paper 104: The Diagnostic Penumbra — CRM of Bayesian Clinical Decision-Making

**Paper 104, Clinical Sub-Series Paper B, of the Constructive Reverse Mathematics Series**

**Author:** Paul Chun-Kit Lee (New York University, Brooklyn, New York)

## Summary

Paper 104 applies Constructive Reverse Mathematics to the diagnostic testing pipeline. The central result identifies the **Archimedean Escalation**: the traditional diagnostic pipeline (integer risk scores, cohort prevalence, Mann-Whitney AUC) is **100% BISH**, while the precision medicine pipeline (logistic regression, population prevalence, parametric ROC) drops to **70% BISH** — isomorphic to the RCT pipeline (Paper 103). The 30% gap is the logical cost of replacing discrete heuristics with continuous models.

## Main Results

- **Theorem A (Archimedean Escalation):** Traditional pipeline = 10/10 BISH (100%). Precision pipeline = 7 BISH + 1 BISH+MP + 1 WKL + 1 LPO = 10 stages (70% BISH).
- **Theorem B (Lindemann-Weierstrass Gate):** Logistic prevalence π = 1/(1+e^{-X}) is transcendental for rational X ≠ 0. Bayes' theorem (rational Möbius transformation) preserves transcendence. Comparison with rational threshold requires BISH+MP.
- **Theorem C (ROC Bifurcation):** Empirical AUC = Mann-Whitney U/(n_+ · n_-) ∈ Q → BISH. Parametric (binormal) AUC requires LPO.
- **Theorem D (Discrete Bypass):** Integer risk scores keep the entire pipeline in Q. CRM explains why they perform as well as logistic models.

## Dual Pipeline Classification

| Stage | Component | Traditional | Precision |
|-------|-----------|-------------|-----------|
| 1 | Contingency table | BISH | BISH |
| 2 | Test characteristics | BISH | BISH |
| 3 | Likelihood ratios | BISH | BISH |
| 4 | Pre-test probability | BISH | BISH |
| 5 | Bayesian posterior | BISH | BISH |
| 6 | Treatment threshold | BISH | WKL |
| 7 | Clinical decision | BISH | BISH+MP |
| 8 | ROC AUC comparison | BISH | LPO |
| 9 | Test comparison | BISH | BISH |
| 10 | Net reclassification | BISH | BISH |

**Traditional: 10/10 BISH (100%) | Precision: 7/10 BISH (70%)**

## Clinical Test Cases

1. **Troponin (ESC 0/1h):** 24.7% of chest pain presentations in the observe zone (5–52 ng/L). Mueller validation cohort, N = 7,998. Observe zone is biological, BISH-decidable with cohort data.
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

### Module Structure (10 files, 1,141 lines)

| File | Lines | Description |
|------|-------|-------------|
| OmnisciencePrinciples.lean | 69 | LPO, WLPO, MP definitions and implications |
| ContingencyTable.lean | 87 | 2×2 table, sensitivity, specificity, PPV, NPV |
| BayesianInference.lean | 155 | Logistic model, transcendental gate, rational/real posterior, MP requirement |
| ROCAnalysis.lean | 108 | Mann-Whitney AUC (BISH), parametric AUC (LPO), ROC bifurcation |
| TreatmentThreshold.lean | 85 | Pauker-Kassirer model, rational/continuous utilities |
| DiagnosticPenumbra.lean | 107 | Archimedean Escalation, traditional vs precision pipeline |
| TroponinCalculations.lean | 147 | ESC 0/1h algorithm, Mueller cohort verification |
| ClinicalTestCases.lean | 127 | D-dimer for PE, PSA screening |
| CRMPipeline.lean | 131 | Dual pipeline classification, escalation proof |
| Paper104_Assembly.lean | 125 | Master theorem, axiom documentation |

### Axiom Inventory

**Documentary axioms (5):**
1. `real_posterior_comparison_requires_MP` — posterior comparison needs MP (Bishop-Bridges §2.3)
2. `auc_comparison_requires_LPO` — parametric AUC comparison needs LPO (Bishop-Bridges §2.3)
3. `continuous_threshold_exists` — continuous τ* existence (Pauker-Kassirer)
4. `continuous_threshold_requires_WKL` — continuous τ* needs WKL (Paper 23)
5. `logistic_prevalence_transcendental` — σ(X) = 1/(1+e^{-X}) transcendental for rational X ≠ 0 (Lindemann-Weierstrass)

**Infrastructure axioms:** `propext`, `Classical.choice`, `Quot.sound` (Lean/Mathlib standard).

**Sorries: 0**

### Dependencies

- Paper 103 (structural twin — RCT pipeline)
- Paper 98 (Archimedean Obstruction Thesis)
- Paper 23 (Fan Theorem / WKL)
