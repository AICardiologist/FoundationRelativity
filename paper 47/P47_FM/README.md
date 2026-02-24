# Paper 47: Constructive Calibration of the Fontaine-Mazur Conjecture

**CRM Stratification of p-adic Galois Representations**

Paper 47 in the Constructive Reverse Mathematics Series
Paul C.-K. Lee (NYU), February 2026

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18682788.svg)](https://doi.org/10.5281/zenodo.18682788)

## Overview

This Lean 4 formalization establishes the constructive reverse mathematics (CRM) calibration of the Fontaine-Mazur Conjecture. The five conditions of Fontaine-Mazur — unramified, de Rham, geometric origin, trace rationality, and polarization — are shown to stratify cleanly across the omniscience hierarchy:

- **Abstract side** (FM1, FM2): LPO over ℚ_p — deciding whether a p-adic Galois representation is unramified or de Rham requires the Limited Principle of Omniscience.
- **Geometric side** (FM3, FM4): BISH — under geometric origin, the Faltings comparison isomorphism and algebraic traces restore decidability without LPO.
- **Obstruction** (FM5): The p-adic u-invariant (u(ℚ_p) = 4) blocks positive-definite Hermitian forms in dimension ≥ 3, obstructing harmonic metric approaches.

## Main Results

| Theorem | Statement |
|---------|-----------|
| `FM1_unramified_iff_LPO` | DecidesIdentity ↔ LPO_Q_p |
| `FM2_deRham_iff_LPO` | DetOracle ↔ LPO_Q_p |
| `geometric_origin_kills_LPO_state_space` | Faltings comparison + rational skeleton → decidable equality (BISH) |
| `trace_decidable_geometric` | Geometric Frobenius traces are decidable via algebraic traces (BISH) |
| `trace_abstract_requires_LPO` | Abstract Frobenius traces require LPO |
| `no_padic_hermitian_form` | No positive-definite Hermitian form over p-adic fields in dim ≥ 3 |
| `fm_calibration_summary` | Five-part conjunction: FM1–FM5 |
| `de_omniscientizing_descent_FM` | Abstract (LPO) vs geometric (BISH) gap |

## Axiom Audit

**26 custom axioms**: 19 load-bearing + 7 completeness/narrative.

All proofs from axioms are machine-checked and sorry-free. The custom axioms model p-adic arithmetic geometry types not present in Mathlib (ℚ_p as a p-adic field, Galois representation spaces, de Rham modules, Faltings comparison isomorphism). No axiom encodes the conclusion of any theorem — all axioms are structural or encode standard number-theoretic facts.

`Classical.choice` appears in all theorems due to Mathlib's typeclass infrastructure (an infrastructure artifact). Constructive stratification is established by proof content (explicit witnesses vs principle-as-hypothesis), not by axiom checker output (cf. Paper 10 §Methodology).

## Project Structure

```
P47_FM/
  lakefile.lean
  lean-toolchain          (leanprover/lean4:v4.29.0-rc1)
  Papers.lean
  Papers/P47_FM/
    Defs.lean              (280 lines) — 26 custom axioms, type infrastructure
    FM1_Unramified.lean    (126 lines) — Unramified ↔ LPO (encoding pattern)
    FM2_deRham.lean         (70 lines) — de Rham ↔ LPO (1×1 matrix encoding)
    FM3_Descent.lean       (188 lines) — Geometric origin → BISH (Faltings)
    FM4_Traces.lean        (123 lines) — Trace decidability (geometric vs abstract)
    FM5_Obstruction.lean    (73 lines) — Hermitian form obstruction
    Main.lean              (156 lines) — Master theorem + axiom audits
```

7 files, ~1016 lines.

## Build

```bash
lake build    # 0 errors, 0 warnings, 0 sorry — 1774 build jobs
```

Requires Lean 4.29.0-rc1 and Mathlib.

## References

- Fontaine and Mazur (1995), "Geometric Galois representations"
- Faltings (1988), "p-adic Hodge theory"
- Bridges and Richman (1987), *Varieties of Constructive Mathematics*
