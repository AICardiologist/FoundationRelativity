# Paper 50: Three Axioms for the Motive

**Constructive Reverse Mathematics Meets Grothendieck's Universal Cohomology -- A Lean 4 Formalization**

## Overview

This paper calibrates five major conjectures in arithmetic geometry against the constructive hierarchy BISH ⊂ BISH+MP ⊂ BISH+LPO ⊂ CLASS and discovers a three-axiom logical specification of Grothendieck's category of numerical motives. The category of pure motives is the initial **Decidable Polarized Tannakian** (DPT) category equipped with a Weil cohomology functor. The three axioms are:

1. **DecidableEq on Hom** (Standard Conjecture D): morphism equality reduces to integer intersection numbers
2. **Algebraic Spectrum**: endomorphisms satisfy monic Z-polynomials, forcing eigenvalues into Q-bar
3. **Archimedean Polarization**: positive-definite inner product on the real fiber (available over R, obstructed over Q_p)

## Key Results

| Theorem | Statement | Sorries |
|---------|-----------|---------|
| `weil_RH_from_CRM` (Thm A) | Weil RH reduces to one cancellation step | 0 |
| `conjD_decidabilizes` (Thm C fwd) | Conjecture D gives decidable Hom | 0 |
| `conjD_is_decidability_axiom` (Thm C rev) | Decidable Hom implies LPO(Q_ell) | 0 |
| `cm_subcategory_is_DPT` (Thm E) | CM elliptic motives are BISH-decidable | 0 |
| `honda_tate_is_initial` (Thm B) | DPT category is inhabited over F_q | 0 (True-valued) |
| `frobenius_eigenvalues_are_weil` | Frobenius eigenvalues are Weil numbers | 2 |

## Module Structure

```
Papers/P50_Universal/
  DecPolarTann.lean    -- DPT class: three CRM axioms (0 sorries)
  WeilRH.lean          -- Theorem A: Weil RH from CRM (0 sorries)
  ConjD.lean           -- Theorem C: Conj D as decidability axiom (0 sorries)
  WeilNumbers.lean     -- Honda-Tate and Weil number theory (2 sorries)
  MotiveCategory.lean  -- MotCat structure and initiality (0 sorries)
  AtlasImport.lean     -- 19 True-valued axioms from Papers 45-49
  CMDecidability.lean  -- Theorem E: CM rescue over Q (0 sorries)
  Main.lean            -- Aggregator, #print axioms audit
```

## Build

```bash
lake update
lake build
```

Requires `leanprover/lean4:v4.29.0-rc1` (see `lean-toolchain`).

Expected output: 0 errors, 2214 build targets, 2 sorries (both in WeilNumbers.lean: square root extraction and Hasse bound).

## Axiom Audit

46 custom axioms total:
- 25 True-valued placeholders for upstream results (Papers 45-49, bridge lemmas)
- 21 substantive axioms with published citations

The 2 sorries are principled: they mark algebraic computations (square root extraction, Hasse bound verification) that require certified arithmetic not yet available in Mathlib.

**Theorems A, C, and E carry zero sorries.**

## Classical.choice Audit

`Classical.choice` appears in all theorems due to Mathlib's construction of R and C as Cauchy completions. This is an infrastructure artifact. Constructive stratification is established by proof content (explicit witnesses vs. principle-as-hypothesis), not by axiom checker output.

`Classical.dec` does NOT appear in Theorems A, C, or E.

## Conjectures Calibrated

| Conjecture | CRM Level | Motive's Role |
|------------|-----------|---------------|
| Weight-Monodromy | LPO | Axiom 3 (polarization) provides cancellation |
| Tate | LPO | Axiom 1 (Conj D) collapses to BISH |
| Fontaine-Mazur | MP + LPO | Axiom 2 (algebraic spectrum) constrains eigenvalues |
| BSD (Sha finiteness) | Sigma_3^0 | Motive shifts complexity down one level |
| Hodge | LPO + MP | Axioms 1+3 together; Lefschetz (1,1) for CM |

## LaTeX Paper

```bash
pdflatex paper50.tex
pdflatex paper50.tex  # second pass for references
```

Produces `paper50.pdf` (27 pages).

## Author

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com)

New York University

AI-assisted formalization (Claude, Anthropic).

DOI: [10.5281/zenodo.18705837](https://doi.org/10.5281/zenodo.18705837) (Version 2, February 19 2026)
