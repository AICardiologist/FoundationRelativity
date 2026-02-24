# Paper 42: The Worst Prediction in Physics Is Not a Prediction

**Paper 42 in the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com), February 2026

DOI: [10.5281/zenodo.18654789](https://doi.org/10.5281/zenodo.18654789)

## Overview

This Lean 4 formalization applies the axiom calibration framework of
constructive reverse mathematics to the cosmological constant problem ---
the alleged 10^120 discrepancy between quantum field theory's "prediction"
of vacuum energy and the observed value.

The problem decomposes into three logically distinct claims:

- **Claim I (Dissolved):** The 10^120 is a regulator-dependent artifact.
  The unregularized vacuum energy does not converge to a real number at
  any level of the constructive hierarchy. Different regularization schemes
  produce different finite values. A regulator-dependent quantity has no
  empirical content.

- **Claim II (Reclassified):** The "naturalness" argument is a Bayesian
  prior, not a mathematical derivation. The Hollands-Wald axioms prove
  that the cosmological constant is a free parameter.

- **Claim III (Identified, LPO):** The genuine constraint is the 55-digit
  fine-tuning between the bare cosmological constant and the vacuum
  condensates. Computing the exact interacting condensates requires the
  thermodynamic limit (Fekete's lemma, Paper 29), placing the fine-tuning
  equation at LPO --- the same level as every thermodynamic limit in the
  programme.

## Main Results

| Theorem | Statement | CRM Status |
|---------|-----------|------------|
| `vacuum_energy_divergent` | Unregularized vacuum energy is unbounded | BISH |
| `prediction_regulator_dependent` | Two valid schemes yield different values | BISH |
| `lambda_free_parameter` | Wald ambiguity: Lambda is a free parameter | BISH |
| `casimir_bish` | Casimir energy difference has computable modulus | BISH |
| `condensate_lpo` | Exact interacting condensate exists given LPO | LPO |
| `rg_running_bish` | Perturbative RG running is BISH (Picard-Lindelof) | BISH |
| `fine_tuning_lpo` | Fine-tuning equation holds given LPO | LPO |
| `cc_calibration` | Assembly: 7-part conjunction | BISH + LPO |
| `cc_master` | Master theorem re-exporting assembly | BISH + LPO |

## Significance

The "worst prediction in physics" is not a prediction. The 10^120 is a
property of a calculational choice, not of quantum field theory. The
Casimir effect proves the diagnostic works: energy differences are BISH
and experimentally verified; absolute energies are regulator-dependent
and physically meaningless. The genuine residual --- 55-digit fine-tuning
--- lives at LPO, the same level as every thermodynamic limit in physics.

The CRM analysis provides a formal, machine-checked expression of the
post-naturalness position articulated by Martin (2012), Bianchi-Rovelli
(2010), and Hossenfelder (2019).

## Axiom Profile

```
#print axioms cc_master
-- [Lambda_obs, bmc_from_subadditive,
--  dimreg_value_different, eight_pi_G,
--  lattice_energy_bdd_below, lattice_energy_subadditive,
--  lattice_vacuum_energy, mode_sum_mono,
--  mode_sum_partial, mode_sum_unbounded,
--  picard_lindelof_lambda, propext,
--  regularized_vacuum_energy,
--  Classical.choice, Quot.sound]
```

- 11 physics bridge axioms
- 1 CRM axiom (`bmc_from_subadditive` = Fekete equiv LPO, Paper 29)
- 3 Lean infrastructure (`propext`, `Classical.choice`, `Quot.sound`)

## How to Open and Build

### LaTeX Paper

The compiled PDF is included (`paper42.pdf`). To recompile:

```bash
pdflatex paper42.tex
pdflatex paper42.tex   # second pass for cross-references
```

### Lean 4 Formalization

**Prerequisites:** Lean 4 (v4.28.0-rc1) with elan.

```bash
cd P42_CosmologicalConstant
lake build
```

**Expected output:** 0 errors, 0 warnings, 0 sorry.

To verify the axiom profile:

```bash
# In any .lean file, add:  #print axioms cc_master
```

### Module Structure (10 modules, ~830 lines)

```
Defs.lean              -- Core definitions and bridge axioms (207 lines)
VacuumDivergence.lean  -- Theorem 1: vacuum energy diverges (BISH)
RegulatorDependence.lean -- Theorem 2: regulator-dependent (BISH)
WaldAmbiguity.lean     -- Theorem 3: Lambda is free parameter (BISH)
CasimirBISH.lean       -- Theorem 4: Casimir energy difference (BISH)
CondensateLPO.lean     -- Theorem 5: exact condensate (LPO)
RGRunningBISH.lean     -- Theorem 6: RG running (BISH)
FineTuningLPO.lean     -- Theorem 7: fine-tuning equation (LPO)
CalibrationTable.lean  -- Assembly theorem cc_calibration
Main.lean              -- Master theorem cc_master + axiom audit
```

## Toolchain

- Lean: `leanprover/lean4:v4.28.0-rc1`
- Mathlib4 (pinned via `lake-manifest.json`)

## License

Creative Commons Attribution 4.0 International (CC BY 4.0).

## Citation

```bibtex
@misc{Lee2026P42,
  author = {Lee, Paul Chun-Kit},
  title  = {The Worst Prediction in Physics Is Not a Prediction:
            Axiom Calibration of the Cosmological Constant Problem},
  year   = {2026},
  doi    = {10.5281/zenodo.18654789},
  note   = {Paper~42 of the Constructive Reverse Mathematics Programme}
}
```
