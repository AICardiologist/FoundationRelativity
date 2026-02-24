# Paper 18 — Constructive Stratification of the Standard Model Yukawa RG

**Author:** Paul Chun-Kit Lee (New York University)
**Date:** February 2026
**Series:** Constructive Reverse Mathematics for Mathematical Physics
**DOI:** [10.5281/zenodo.18626839](https://doi.org/10.5281/zenodo.18626839)

## Abstract

The constructive reverse mathematics (CRM) programme has established, across five physics domains, that the passage from finite computation (BISH) to completed infinite limit costs LPO via Bounded Monotone Convergence. This pattern suggests a scaffolding principle: when physicists use LPO-level idealizations, the idealizations may constrain the architecture of explanations, and removing them may reveal BISH-level mechanisms invisible in the conventional formalism. We test this principle on the fermion mass hierarchy through ten numerical investigations (Phases A–B) and a Lean 4 formalization (Phase C).

All ten numerical investigations yield negative results: the Standard Model's infrared dynamics do not determine the mass hierarchy. The Lean 4 formalization establishes a sharp constructive stratification: the one-loop Yukawa RG flow is BISH, step-function thresholds cost WLPO, and CKM eigenvalue-crossing detection costs LPO.

## Contents

```
paper18_writeup_v2.tex       LaTeX source — unified paper (23 pages)
paper18_writeup_v2.pdf       Compiled PDF — unified paper
README.md                    This file

phase1/                      Phase A: One-loop numerical investigation
  rg_mass_hierarchy.py         Python code (~600 lines)
  plots/                       10 output plots
    plot01_top_qfp.png             Top Yukawa quasi-fixed-point convergence
    plot02_btau_ratio_hist.png     b/τ Yukawa ratio distribution
    plot03_btau_heatmap.png        b/τ ratio heatmap over initial conditions
    plot04_hierarchy_scatter.png   Mass hierarchy scatter plot
    plot05_hierarchy_error.png     Hierarchy prediction errors
    plot06_1loop_vs_2loop_qfp.png  1-loop vs 2-loop QFP comparison
    plot07_btau_1L_vs_2L.png       b/τ ratio: 1-loop vs 2-loop
    plot08_koide.png               Koide relation exploration
    plot09_discrete_vs_continuous.png  Discrete vs continuous RG comparison
    plot10_qfp_basin_N.png         QFP basin of attraction vs step count

phase2/                      Phase B: Two-loop numerical investigation
  rg_phase2.py                 Python code (~600 lines)
  plots_phase2/                5 output plots
    inv1_two_loop_comparison.png   Two-loop vs one-loop QFP distributions
    inv2_coupling_vs_N.png         Coupling values vs discrete step count
    inv3_ratio_plane.png           Ratio-space (r_b, r_τ) portrait
    inv4_self_consistency.png      Threshold self-consistency iteration
    inv5_koide_phase.png           Koide phase δ convergence

phase3/                      Phase C: Lean 4 formalization
  P18_YukawaRG/                Lean 4 bundle (5 files, 902 lines)
    lakefile.lean                Project configuration
    lean-toolchain               Toolchain: leanprover/lean4:v4.28.0-rc1
    Papers.lean                  Module root
    Papers/P18_YukawaRG/
      Defs.lean                    SM beta function coefficients (ℚ)
      RatioBeta.lean               Theorem 3: ratio beta negativity
      Threshold_WLPO.lean          Theorem 5: Heaviside step → WLPO
      CKM_LPO.lean                 Theorem 4: eigenvalue gap → LPO
      PicardBISH.lean              Theorems 1–2: Picard iteration is BISH
```

## Running the Code

### Phase A: One-loop numerical investigation

**Dependencies:** Python 3.9+, NumPy, SciPy, Matplotlib

```bash
cd phase1
python3 rg_mass_hierarchy.py
```

**Runtime:** approximately 16 minutes.
**Output:** 10 PNG plots in `plots/`, plus console summary.

### Phase B: Two-loop numerical investigation

**Dependencies:** Python 3.9+, NumPy, SciPy, Matplotlib

```bash
cd phase2
python3 rg_phase2.py
```

**Runtime:** approximately 7 minutes.
**Output:** 5 PNG plots in `plots_phase2/`, plus console summary.

### Phase C: Lean 4 formalization

**Dependencies:** Lean 4 (v4.28.0-rc1), internet access for Mathlib download

```bash
cd phase3/P18_YukawaRG
lake build
```

**First build:** approximately 15–30 minutes (downloads and compiles Mathlib).
**Subsequent builds:** under 1 minute.
**Expected output:** 0 errors, 0 warnings, 0 sorries.

To verify the axiom audit:

```bash
lake env lean Papers/P18_YukawaRG/PicardBISH.lean 2>&1 | grep "axioms"
lake env lean Papers/P18_YukawaRG/CKM_LPO.lean 2>&1 | grep "axioms"
```

## Key Results

### Numerical Investigations (Phases A–B)

| # | Investigation | Phase | Result |
|---|--------------|-------|--------|
| 1 | Top QFP convergence | A | **YES** — visible at N=10 |
| 2 | Discrete vs continuous | A | NO — same physics |
| 3 | Mass hierarchy attractor | A | NO — 0/3,000 match |
| 4 | b/τ attractor | A | NO — weak (6%) |
| 5 | Two-loop QFP shift | A | NO — −0.65% only |
| 6 | Two-loop new QFPs | B | NO — 3.2% std reduction |
| 7 | Large step-size dynamics | B | NO — monotone convergence |
| 8 | Ratio-space fixed points | B | NO — CV=1.48, 13% convergence |
| 9 | Threshold self-consistency | B | NO — m_t/m_b=1.66 (observed 41.3) |
| 10 | Koide phase attractor | B | NO — 0% convergence to δ=2/9 |

**Overall:** 1/10 positive (top QFP only). The SM's infrared dynamics do not determine the fermion mass hierarchy.

### Lean 4 Formalization (Phase C)

| Theorem | Statement | CRM Level |
|---------|-----------|-----------|
| 1 | Picard iterate preserves ℚ[t] | BISH |
| 2 | Picard sequence has computable Cauchy modulus | BISH |
| 3 | Ratio betas negative in top-dominant regime | BISH |
| 4 | Eigenvalue gap decision requires LPO | LPO boundary |
| 5 | Heaviside step-function evaluation requires WLPO | WLPO boundary |

**Constructive stratification:**

```
BISH  ⊊  WLPO (thresholds)  ⊊  LPO (eigenvalue crossings)  ⊊  Classical
 ↑         ↑                     ↑
 Thms 1–3  Thm 5                 Thm 4
```

**Axiom profile:** All theorems compile with 0 errors, 0 warnings, no `sorryAx`. Pure algebraic theorems (over ℚ) use only `propext`. Real-valued theorems additionally use `Classical.choice` and `Quot.sound` through Mathlib's ℝ infrastructure — this is an artifact, not a logical dependency.

## Series

Paper 18 in the Constructive Reverse Mathematics for Mathematical Physics series.

Previous papers with Lean 4 formalizations: Papers 2, 6, 7, 8, 23, 28.

Full archive: [Zenodo DOI 10.5281/zenodo.18626839](https://doi.org/10.5281/zenodo.18626839)

## License

This work is released for academic use.
