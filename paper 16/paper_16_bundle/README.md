# Technical Note 16: The Born Rule as a Logical Artefact

Technical note in the constructive calibration programme. Lean 4 formalization
verifying that finite-dimensional Born-rule probability is BISH-constructive
(finite sums, matrix algebra, no choice), while the frequentist strong law
(SLLN) requires Dependent Choice over N (DC_omega). The DC_omega layer is
axiomatised, not proved from scratch. Contribution is programme completeness —
filling the DC_omega row of the calibration table — not mathematical novelty.

**Zenodo DOI:** 10.5281/zenodo.18575377

## Main Theorems

### Part A — BISH Content (Level 0)

```lean
theorem born_prob_nonneg {d : N} (psi : Fin d -> C)
    (spec : SpectralDecomp d) (i : Fin d) :
    0 <= bornProb psi spec i

theorem born_prob_sum_one {d : N} (psi : Fin d -> C)
    (spec : SpectralDecomp d) (hpsi : cnorm_sq psi = 1) :
    sum i, bornProb psi spec i = 1

theorem expectation_real {d : N} (psi : Fin d -> C)
    (A : Matrix (Fin d) (Fin d) C) (hA : A.conjTranspose = A) :
    (expectationValue psi A).im = 0

theorem variance_nonneg {d : N} (psi : Fin d -> C)
    (A : Matrix (Fin d) (Fin d) C) (mu : C) :
    0 <= cnorm_sq ((A - mu * 1).mulVec psi)

theorem bernoulli_variance_bound (p : R) (hp : 0 <= p) (hp1 : p <= 1) :
    p * (1 - p) <= 1 / 4

theorem chebyshev_bernoulli_bound (p : R) (hp : 0 <= p) (hp1 : p <= 1)
    (N : Nat) (hN : 0 < N) (eps : R) (heps : 0 < eps) :
    p * (1 - p) / (N * eps ^ 2) <= 1 / (4 * N * eps ^ 2)
```

Theorems 1-5 are finite-dimensional linear algebra — correctness verification,
not discovery. Born probabilities are non-negative and sum to 1. Expectation
values of Hermitian operators are real. Variance is non-negative. The Chebyshev
bound gives explicit finite-sample error control. All BISH — finite sums,
matrix algebra, no limits, no choice.

### Part B — DC_omega Content (Level 2)

```lean
theorem frequentist_convergence : SLLN :=
  slln_of_dc dc_omega_holds
```

The strong law of large numbers (frequentist convergence of measurement
frequencies to Born probabilities) requires Dependent Choice over N (DC_omega).
This is axiomatised: `dc_omega_holds` asserts DC_omega, `slln_of_dc` asserts
that DC_omega implies SLLN. The full constructive proof of SLLN from DC_omega
remains an open problem.

## Programme Integration

| Domain              | Paper | BISH Content              | Non-BISH Content           |
|---------------------|-------|---------------------------|----------------------------|
| Stat. Mech.         | P8    | Finite-volume free energy | f_infinity exists (LPO)    |
| Gen. Rel.           | P13   | Radial coordinate bounds  | r -> 0 exactly (LPO)      |
| Quantum Meas.       | P14   | Finite-time decoherence   | Exact collapse (LPO)      |
| Conservation Laws   | P15   | Local conservation        | Global energy (LPO)        |
| **Born Rule**       | **P16** | **Probability, weak law** | **SLLN (DC_omega)**      |

Papers 8, 13, 14, 15 populate the LPO axis. This note, together with Paper 6
(Heisenberg uncertainty), populates the DC_omega axis. The Born rule is not a
new domain — it is a new aspect of quantum mechanics already covered by Papers
4, 6, 11, 14. See Paper 10 for the certification methodology.

## Dependencies

- **Lean 4:** `leanprover/lean4:v4.28.0-rc1`
- **Mathlib4:** commit `7091f0f601d5aaea565d2304c1a290cc8af03e18` (pinned in `lake-manifest.json`)

## File Manifest

### Lean Source Files (`P16_BornRule/Papers/P16_BornRule/`)

| File | Lines | Role |
|------|-------|------|
| `Defs.lean` | 86 | Core definitions: cdot, cnorm_sq, SpectralDecomp, bornProb |
| `BornProbability.lean` | 127 | Theorem 1: Born probability (BISH) |
| `Expectation.lean` | 37 | Theorem 2: Expectation reality (BISH) |
| `Variance.lean` | 29 | Theorem 3: Variance non-negativity (BISH) |
| `RelativeFreq.lean` | 67 | Theorem 4: Relative frequency bounds (BISH) |
| `WeakLaw.lean` | 47 | Theorem 5: Chebyshev bound (BISH) |
| `DCAxiom.lean` | 31 | DC_omega definition + axiom |
| `StrongLaw.lean` | 51 | Theorem 6: SLLN requires DC_omega |
| `Main.lean` | 89 | Assembly + `#print axioms` audit |

**Total:** 564 lines, 9 files, 0 sorry, 0 errors.

### Other Files

| File | Description |
|------|-------------|
| `paper16_writeup.tex` | LaTeX source for the technical note |
| `paper16_writeup.pdf` | Compiled PDF (11 pages) |
| `README.md` | This file |

## Build

```bash
cd P16_BornRule
lake exe cache get    # download prebuilt Mathlib oleans
lake build            # ~2 min with cache, ~45 min without
```

Expected output: 1662 jobs, 0 errors, 0 sorry, 0 warnings.

## Axiom Certificate

**BISH theorems** (`born_prob_nonneg`, `born_prob_sum_one`, `expectation_real`,
`variance_nonneg`, `bernoulli_variance_bound`, `chebyshev_bernoulli_bound`,
`relative_freq_nonneg`, `relative_freq_le_one`, `relative_freq_sum`,
`cnorm_sq_nonneg`):
- `[propext, Classical.choice, Quot.sound]` — standard Mathlib infrastructure only
- Classical.choice traces to `Fin.fintype` and `Real.instField` (type infrastructure)
- No custom axioms, no omniscience principles

**DC_omega theorems** (`frequentist_convergence`):
- Above + `Papers.P16.dc_omega_holds`, `Papers.P16.slln_of_dc`
- dc_omega_holds axiomatizes Dependent Choice over N
- slln_of_dc axiomatizes the strong law as a consequence of DC

**CRM Audit Details (Paper 10 methodology):**
- No `Classical.em`, no `Classical.byContradiction` anywhere in source
- `by_cases` not used in any proof
- All BISH theorems have clean axiom closure (no custom axioms)

## Architecture

```
Defs.lean
  ├── BornProbability.lean              (Born probability, BISH)
  │     ├── Expectation.lean            (Expectation reality, BISH)
  │     └── Variance.lean               (Variance non-negativity, BISH)
  ├── RelativeFreq.lean                 (Frequency bounds, BISH)
  ├── WeakLaw.lean                      (Chebyshev bound, BISH)
  └── Main.lean                         (assembly + axiom audit)

DCAxiom.lean
  └── StrongLaw.lean                    (SLLN requires DC_omega)
        └── Main.lean
```

## Mathematical Content

**Part A (BISH):** Born probabilities p_i = Re<psi, P_i psi> for a spectral
decomposition {P_i} form a valid probability distribution: non-negative and
sum to 1. The expectation value of a Hermitian operator is real. The variance
is non-negative. Relative frequencies of N measurements sum to 1. The
Chebyshev/weak law bound gives explicit 1/(4N*eps^2) error control. This is
finite-dimensional linear algebra — the BISH content is unsurprising.

**Part B (DC_omega):** The strong law of large numbers — that measurement
frequencies converge almost surely to Born probabilities — requires Dependent
Choice over N. The DC enters through: (1) countable product probability
space construction, (2) Borel-Cantelli lemma, (3) almost-sure convergence.
The DC_omega layer is axiomatised in this note; the full constructive SLLN
proof remains open.

**Open problem:** Prove SLLN equivalent to DC_omega over BISH (exact
calibration, not just the upper bound DC_omega >= SLLN axiomatised here).

## License

CC BY 4.0. See repository root for details.
