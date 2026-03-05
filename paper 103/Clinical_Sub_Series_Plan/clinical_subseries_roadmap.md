# Clinical Sub-Series Roadmap

**Author:** Paul Chun-Kit Lee
**Date:** 2026-03-05
**Status:** Paper 103 complete. Papers 104–107 planned.

---

## Overview

The Clinical Sub-Series applies Constructive Reverse Mathematics to evidence-based medicine. The central discovery (Paper 103): the Archimedean obstruction in clinical inference is identical to the one in arithmetic geometry — rational data passes through a transcendental function (the normal CDF Φ in medicine, Betti realization in AG), creating a logical gap that requires omniscience principles to bridge.

## Completed

### Paper 103 — The Asymptotic Penumbra: CRM of the RCT Statistical Pipeline
- **DOI:** 10.5281/zenodo.18880102
- **Result:** Asymptotic tests require BISH+MP (transcendental gate Φ). Penumbra width = 2ε (Studentized Berry-Esseen). Five theorems (A–E). GUSTO in penumbra; COURAGE/ISCHEMIA BISH-decidable. Equivalence Barrier: d_min ≈ 65,127 events.
- **Pipeline:** 7 BISH + 1 BISH+MP + 1 WKL + 1 LPO = 10 stages (70% BISH)
- **Lean:** 956 lines, 10 files, 58 theorems, 4 sorry (documented)
- **Pages:** 25, References: 34

---

## Planned Papers

### Paper 104 — The Diagnostic Penumbra: CRM of Bayesian Clinical Decision-Making

**Priority: 1 (next paper)**

**Core argument:** Sensitivity, specificity, and predictive values from finite contingency tables are rational (BISH). But the clinical decision invokes Bayes' theorem with a continuous prior (population prevalence π as a real number), and the posterior probability P(D|+) is compared against a treatment threshold τ derived from utility theory over continuous outcomes. This comparison is the same transcendental gate as the p-value problem.

**Mathematical structure:**
- Finite contingency table: TP, FP, FN, TN — all natural numbers → BISH
- Sensitivity = TP/(TP+FN), Specificity = TN/(TN+FP) — rational → BISH
- Bayesian posterior with rational prevalence: P(D|+) = sens·π / [sens·π + (1-spec)(1-π)] — rational → BISH
- Bayesian posterior with real prevalence (population-level): requires real comparison → MP
- ROC curve: continuous function over [0,1] → WLPO for AUC comparison
- Treatment threshold τ from utility theory: argmin of expected loss over continuous outcome space → LPO
- **The "diagnostic grey zone"**: band around τ where posterior ± ε overlaps the threshold — structural twin of the Asymptotic Penumbra

**Clinical test cases:**
- High-sensitivity troponin in acute chest pain (grey zone: 5–52 ng/L)
- D-dimer for PE exclusion (threshold 500 ng/mL, age-adjusted)
- PSA screening (threshold 4.0 ng/mL, continuous controversy)

**Key theorems to prove:**
- **Theorem A (Diagnostic Penumbra):** The diagnostic grey zone has width determined by prevalence uncertainty and test imprecision
- **Theorem B (Bayesian MP Requirement):** Posterior comparison with real prevalence requires BISH+MP
- **Theorem C (ROC = LPO):** AUC comparison for test selection requires LPO (integral over continuous ROC)
- **Theorem D (Discrete Bypass):** With finite prevalence data (cohort study), the entire Bayesian chain is BISH

**Pipeline classification (expected):**
- Contingency table: BISH
- Test characteristics: BISH
- Bayesian update (rational prior): BISH
- Bayesian update (real prior): BISH+MP
- Treatment threshold (utility minimization): WKL or LPO
- ROC AUC: LPO
- Test comparison (discrete): BISH
- Test comparison (continuous): BISH+MP or WLPO

**Parallels with P103:** Structural twin. The diagnostic grey zone IS the Asymptotic Penumbra for Bayesian inference. The paper writes itself as "P103 for diagnostic testing."

**Lean bundle:** P104_DiagnosticTesting/ (~800–1000 lines expected)

---

### Paper 105 — The Exponential Gate: CRM of Pharmacokinetic Inference

**Priority: 3 (can be section of broader paper)**

**Core argument:** Drug concentration C(t) = D·e^{-kt}/V_d maps rational dose/parameters to transcendental concentrations. The exponential function is the transcendental gate (analogous to Φ in P103). Therapeutic window comparison (C_min < C(t) < C_max) is real trichotomy.

**Mathematical structure:**
- Discrete dosing schedule (q6h, q8h): rational → BISH
- Compartment model parameters (k, V_d) from population PK: real → WLPO
- Single-dose C(t): transcendental (e^{-kt}) → comparison requires MP
- Steady-state trough: infinite series → LPO for convergence
- **Therapeutic penumbra:** band where measured trough level ± assay error overlaps the therapeutic window boundary

**Clinical test cases:**
- Vancomycin AUC-guided dosing (therapeutic window 400–600 mg·h/L)
- Warfarin INR management (therapeutic range 2.0–3.0)
- Aminoglycoside peak/trough monitoring

**Key theorem:** The therapeutic penumbra width depends on (assay CV, PK model uncertainty, dosing interval) — computable rational bound analogous to Berry-Esseen.

**Note:** Narrower than P104. Consider combining with decision theory (Paper 107) into a broader "Clinical Decision Theory" paper.

---

### Paper 106 — The Lyapunov Gate: CRM of Cardiac Electrophysiology

**Priority: 2 (mathematically richest)**

**Core argument:** This is the first clinical paper where the non-BISH cost enters through the PHYSICS mechanism (spectral theorem / dynamical systems) rather than the STATISTICS mechanism (normal CDF). This structural distinction connects the clinical sub-series back to the physics arc (Papers 2–44).

**Mathematical structure:**
- Hodgkin-Huxley ODEs: Picard-Lindelöf existence/uniqueness is BISH (Lipschitz + contraction)
- Lyapunov stability: requires sign-definiteness of a quadratic form — u(R) = ∞ enters through the Inertia theorem (not through Φ)
- Bifurcation detection (arrhythmia onset): eigenvalue crossing through imaginary axis = real trichotomy = LPO
- Spiral wave reentry termination: decidability of halting condition for PDE — potentially Σ⁰₂, connecting to Papers 36–39 (quantum undecidability)
- Defibrillation threshold: minimax over continuous parameter space → WKL or LPO

**Clinical test cases:**
- Ventricular tachycardia: spiral wave dynamics, reentry circuit
- Atrial fibrillation: multiple wavelet hypothesis vs rotor hypothesis
- Pacemaker capture threshold optimization
- ICD programming: discrimination algorithms for VT vs SVT

**Key theorems to prove:**
- **Theorem A (ODE Core is BISH):** Hodgkin-Huxley-type cardiac action potential ODE, given Lipschitz data, has BISH existence/uniqueness
- **Theorem B (Stability = LPO):** Lyapunov stability certification requires LPO (eigenvalue comparison of Jacobian at equilibrium)
- **Theorem C (Bifurcation = LPO):** Detecting the transition from stable rhythm to arrhythmia (Hopf bifurcation) requires LPO
- **Theorem D (Reentry Halting):** The question "does this reentry circuit self-terminate?" may be Σ⁰₂-complete (connecting to Paper 36's spectral gap undecidability)
- **Theorem E (Defibrillation Threshold):** Energy minimization for defibrillation = WKL (bounded optimization over continuous space)

**Why this paper matters:** It breaks genuinely new ground. P103 and P104 apply the STATISTICS mechanism (data → Φ → comparison). P106 applies the PHYSICS mechanism (dynamical system → eigenvalue → stability). The clinical sub-series thereby demonstrates that BOTH mechanisms identified in the main programme (Papers 2–44 for physics, Papers 45–102 for arithmetic) appear in medicine. The Archimedean obstruction is truly universal.

**Pipeline classification (expected):**
- Action potential ODE (existence): BISH
- Numerical integration: BISH
- Parameter estimation from clinical data: BISH+MP (same as P103)
- Lyapunov stability: LPO
- Bifurcation detection: LPO
- Reentry termination: Σ⁰₂ (possibly)
- Defibrillation optimization: WKL
- Pacemaker capture threshold: BISH (finite search over discrete settings)

**Lean bundle:** P106_CardiacElectrophysiology/ (~1000–1200 lines expected)

---

### Paper 107 — The QALY Integral: CRM of Health Economic Decision-Making

**Priority: 4**

**Core argument:** Quality-Adjusted Life Years integrate a utility function over a survival curve. Finite-state MDPs with rational transition probabilities are BISH. But infinite-horizon discounted MDPs with continuous utility functions require a fixed-point theorem (Banach contraction → BISH, but policy optimization over continuous space → WKL or LPO). The QALY integral over a parametric survival curve (Weibull, lognormal) extrapolates beyond observation — the claim "treatment A adds 2.3 QALYs over a lifetime horizon" passes through the continuum.

**Clinical test cases:**
- NICE technology appraisal: lifetime survival extrapolation
- $50,000/QALY willingness-to-pay threshold
- Markov model for disease progression (finite state → BISH; continuous time → MP)

**Note:** Enormous policy implications but mathematically recapitulates P103's mechanism (rational data → continuous model → real comparison). Rank below P106 for novelty.

---

## Sub-Series Architecture

| Paper | Topic | Primary CRM mechanism | Non-BISH gate | Connection to main programme |
|-------|-------|----------------------|---------------|------------------------------|
| 103 | RCT statistics | Statistical (Φ) | BISH+MP | Archimedean obstruction (P70) |
| 104 | Diagnostic testing | Statistical (Bayes) | BISH+MP | Archimedean obstruction (P70) |
| 105 | Pharmacokinetics | Exponential map | BISH+MP | Transcendental gate |
| 106 | Electrophysiology | Dynamical systems | LPO | Spectral theorem (Papers 4, 36) |
| 107 | Health economics | Integral/MDP | WKL/LPO | EVT/optimization (Paper 23) |

**The key architectural point:** Papers 103–105 demonstrate the STATISTICS mechanism (data → transcendental function → comparison). Paper 106 demonstrates the PHYSICS mechanism (dynamical system → eigenvalue → stability). Paper 107 demonstrates the OPTIMIZATION mechanism (utility → fixed point → comparison). All three mechanisms were identified in the main programme; the clinical sub-series shows they all appear in a single applied domain (medicine).

---

## Implementation Notes

### For the next agent:

1. **Start with Paper 104 (Diagnostic Testing).** It parallels P103 most closely and establishes the sub-series pattern.
2. **Follow the P103 template:** Lean bundle with ~10 modules, clinical test cases with real trial data, CRM pipeline classification table, comparison with P103.
3. **Lean toolchain:** v4.29.0-rc2 (same as P103).
4. **Key references for P104:**
   - Pauker & Kassirer (1980) — threshold approach to clinical decisions
   - Fagan (1975) — likelihood ratio nomogram
   - Pencina et al. (2008) — Net Reclassification Improvement
   - Sox et al. (2013) — Medical Decision Making textbook
   - Apple et al. (2021) — high-sensitivity troponin guidelines
5. **The diagnostic grey zone for troponin** is the perfect clinical test case: ESC 0/1h algorithm uses 5 ng/L (rule-out) and 52 ng/L (rule-in), with the 5–52 range being the "observe zone" — exactly the Diagnostic Penumbra.
6. **Paul is a cardiologist.** Troponin, cardiac cath decision-making, and EP are his clinical world. Lean into cardiology test cases.

### Lean module structure for P104 (suggested):

```
P104_DiagnosticTesting/
├── Papers/P104_DiagnosticTesting/
│   ├── OmnisciencePrinciples.lean    (reuse from P103)
│   ├── ContingencyTable.lean         (TP, FP, FN, TN, rational stats)
│   ├── BayesianInference.lean        (posterior computation, rational/real)
│   ├── ROCAnalysis.lean              (AUC as integral, LPO)
│   ├── TreatmentThreshold.lean       (utility theory, optimization)
│   ├── DiagnosticPenumbra.lean       (grey zone characterization)
│   ├── TroponinCalculations.lean     (ESC 0/1h algorithm verification)
│   ├── CRMPipeline.lean             (classification table)
│   └── Paper104_Assembly.lean        (master imports + theorem)
├── Papers.lean
├── lakefile.lean
├── lean-toolchain
└── lake-manifest.json
```
