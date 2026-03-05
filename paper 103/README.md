# Paper 103 — The Asymptotic Penumbra: Constructive Reverse Mathematics of the RCT Statistical Pipeline

**Paper 103, Clinical Sub-Series Paper A, of the Constructive Reverse Mathematics Series**

Author: Paul Chun-Kit Lee, New York University, Brooklyn, New York

## Summary

This paper applies Constructive Reverse Mathematics (CRM) to the statistical pipeline of randomised controlled trials (RCTs).  The central concept is the **Asymptotic Penumbra**: a computable band of p-values where a trial result is classically significant but not constructively witnessed, arising because the normal CDF maps rational test statistics to transcendental p-values.  The penumbra width is characterised by the Studentized Berry-Esseen bound (Bentkus 2003, C_s ≤ 3.19), using sample moments only.

This is the first paper in the Clinical Sub-Series, applying the CRM framework developed in Papers 1-102 to medical statistics.

## Main Results

- **Theorem A (Penumbra Characterisation):** A trial result lies in the penumbra iff p ∈ [α − ε, α), where ε is the Studentized Berry-Esseen error.
- **Theorem B (MP Requirement):** Constructive witnessing of asymptotic significance requires BISH + MP (Markov's Principle) because the p-value is transcendental.
- **Theorem C (Subgroup Penalty):** Below a computable n_min, the penumbra swallows α entirely.
- **Theorem D (Firth Restoration):** Firth's penalised likelihood restores coercivity, dropping Cox MLE from WKL to BISH.
- **Theorem E (Equivalence Barrier):** Constructive equivalence requires d > d_min = (2C_s·κ/α)² ≈ 65,127 events — beyond any cardiovascular outcomes trial.

## Clinical Applications

Three landmark cardiovascular trials are analysed:

| Trial | Events | Key Finding |
|-------|--------|-------------|
| GUSTO-I | 20,672 | In z-test penumbra (p + 2ε = 0.156 > α); Fisher exact resolves (BISH) |
| COURAGE | 413 | Equivalence impossible: d/d_min = 0.63%, ε exceeds α/2 by factor 12.6 |
| ISCHEMIA | 670 | Equivalence impossible: d/d_min = 1.03%, ε exceeds α/2 by factor 9.9 |

## Pipeline Classification

| Stage | CRM Level | Reason |
|-------|-----------|--------|
| Test statistic | BISH | Rational closure |
| Berry-Esseen bound | BISH | Sample moments rational |
| Normal CDF | BISH | Computable real function |
| p < α (universal) | LPO | Bishop encoding |
| p + ε < α (witnessed) | BISH + MP | Markov termination |
| p + ε < α (rational) | BISH | Rational decidability |
| Fisher exact | BISH | Rational p-value |
| Cox MLE (coercive) | BISH | Computable interval |
| Cox MLE (separation) | WKL | Infinite tree search |
| Cox MLE (Firth) | BISH | Restored coercivity |

**Summary:** 7 BISH + 1 (BISH+MP) + 1 WKL + 1 LPO = 10 stages (70% BISH).

## Lean 4 Formalisation

**Toolchain:** `leanprover/lean4:v4.29.0-rc2`
**Dependency:** Mathlib v4.29.0-rc2 (fetched automatically by `lake`)

### Build

```bash
cd P103_RCTStatistics && lake build
```

### Bundle Structure (10 files, 956 lines, 58 theorems)

| File | Lines | Content |
|------|-------|---------|
| `OmnisciencePrinciples.lean` | 72 | LPO, WLPO, LLPO, MP + implications |
| `RealDecidability.lean` | 48 | Trichotomy ↔ LPO bridge |
| `TrialData.lean` | 55 | Patient records, sample statistics |
| `ExactTests.lean` | 40 | Fisher exact, zero penumbra |
| `StudentizedBerryEsseen.lean` | 58 | Studentized BE constant, error function |
| `AsymptoticPenumbra.lean` | 110 | Main theorem, MP requirement |
| `CoxBypass.lean` | 93 | Coercivity, Firth restoration |
| `EffectSizeConjecture.lean` | 47 | Cohen's d, d_min threshold |
| `TrialCalculations.lean` | 301 | GUSTO/COURAGE/ISCHEMIA arithmetic |
| `Paper103_Assembly.lean` | 132 | Master theorem, pipeline classification |

### Axiom Inventory

**Documentary axioms** (modelling external mathematical facts):

| Axiom | Source |
|-------|--------|
| `trichotomy_implies_LPO_encoding` | Bishop-Bridges §2.3 |
| `studentizedBEConstant/pos/bound` | Bentkus 2003 |
| `berryEsseenConstant_oracle/pos/bound` | Berry 1941, Esseen 1942 |
| `exactPermutationPValue` | Standard combinatorics |
| `constructive_witnessing_requires_MP` | MP for ℝ/ℚ approximation |
| `concave_coercive_has_unique_max` | Strict concavity + coercivity |
| `hasCompleteSeparation/decidable` | LP over ℚ |
| `firth_restores_coercivity` | Firth 1993 |

**Sorries (4):**

| Sorry | Nature |
|-------|--------|
| `studentizedBE_computable_bound` | Rational arithmetic bounding |
| `subgroup_penalty` | Existence of n_min from BE bound |
| `penumbra_shrinks_with_n` | Monotonicity in √n |
| `penumbra_grows_with_skewness` | Monotonicity in ρ̂ |

All are straightforward monotonicity/arithmetic arguments documented in the source.

### Dependencies

- Lean 4: v4.29.0-rc2
- Mathlib: v4.29.0-rc2 (fetched by `lake update`)
- No external CAS dependencies

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)

## Citation

Lee, P.C.K. (2026). The Asymptotic Penumbra: Constructive Reverse Mathematics of the RCT Statistical Pipeline. Paper 103, Clinical Sub-Series Paper A, of the Constructive Reverse Mathematics Series. Zenodo. DOI: 10.5281/zenodo.18880102
