# Paper 24: LLPO Equivalence via Kochen-Specker Contextuality

**The Constructive Cost of Single-System No-Go Theorems**

Paper 24 in the Constructive Reverse Mathematics Series
Paul C.-K. Lee (NYU), February 2026

## Overview

This Lean 4 formalization establishes that Kochen-Specker contextuality has the same constructive cost (LLPO) as Bell nonlocality (Paper 21), despite being a physically distinct phenomenon. The KS sign decision — the assertion that at least one measurement context lacks predetermined values — is equivalent to LLPO over BISH.

This is the second LLPO calibration in the series, confirming the structural identity between Bell nonlocality and KS contextuality:

```
        LPO
       / | \
      /  |  \
   WLPO  MP  ...
    |
   LLPO  ← Bell (Paper 21) AND KS contextuality (Paper 24)
    |
   BISH            FT (Paper 23)
```

## Main Results

| Theorem | Statement |
|---------|-----------|
| `cega_uncolorable` | The CEGA 18-vector KS graph is uncolorable (BISH) |
| `llpo_iff_ks_sign` | LLPO ↔ KSSignDecision |
| `ks_stratification` | Three-level: (BISH) uncolorability ∧ (LLPO ↔ KSSignDecision) ∧ (WLPO → LLPO) |
| `finite_context_witness` | For any coloring of a finite KS graph, a failing context exists |

## The CEGA 18-Vector KS Set

18 vectors in R^4 using {0, ±1} coordinates, organized into 9 orthogonal quadruples (contexts). Each vector appears in exactly 2 contexts.

Uncolorability verified by `native_decide` over 2^18 = 262,144 candidate colorings (completes in ~4 seconds).

## Axiom Audit

**ONE custom axiom:** `llpo_real_of_llpo` (LLPO → real sign decision).

This is the same axiom as Paper 21, establishing the standard equivalence between binary-sequence LLPO and real-valued LLPO (Ishihara 2006, Bridges-Richman 1987).

Additionally, `Lean.ofReduceBool` and `Lean.trustCompiler` appear from `native_decide` — these are kernel axioms, not custom mathematical axioms.

## Project Structure

```
P24_KochenSpecker/
  lakefile.lean
  lean-toolchain          (leanprover/lean4:v4.28.0-rc1)
  Papers.lean
  Papers/P24_KochenSpecker/
    Defs/
      KSGraph.lean         KSGraph, KSColoring, satisfiesContext, isKSValid, isKSUncolorable
      CEGAData.lean        cegaGraph (18 vertices, 9 contexts)
      LLPO.lean            LLPO, LPO, WLPO, AtMostOne, hierarchy
      EncodedAsymmetry.lean evenField, oddField, ksAsymmetry, KSSignDecision
    PartA/
      Uncolorability.lean  cega_uncolorable (by native_decide)
      FiniteSearch.lean     finite_context_witness, ks_failing_context
      PartA_Main.lean      Summary and axiom audit
    PartB/
      SignIff.lean         ksAsymmetry sign-iff lemmas (under AtMostOne)
      Forward.lean         ks_sign_of_llpo (LLPO → KSSignDecision)
      Backward.lean        llpo_of_ks_sign (KSSignDecision → LLPO)
      PartB_Main.lean      llpo_iff_ks_sign
    Main/
      Stratification.lean  ks_stratification (three-level)
      AxiomAudit.lean      Comprehensive #print axioms
    Main.lean              Root imports
```

16 files, ~887 lines.

## Build

```bash
lake build    # 0 errors, 0 warnings, 0 sorry
```

Requires Lean 4.28.0-rc1 and Mathlib. The `native_decide` proof (Uncolorability.lean) requires compiled Lean and takes ~4 seconds.

## Structural Finding

Two physically distinct quantum no-go theorems have the **same logical cost**:

| Phenomenon | Physics | Logical Cost | Paper |
|------------|---------|-------------|-------|
| Bell nonlocality | Spatially separated systems | LLPO | 21 |
| KS contextuality | Single-system measurements | LLPO | 24 |

CRM reveals that Bell nonlocality and KS contextuality are the **same logical phenomenon** — "disjunction without constructive witness" — in different physical clothing.

## References

- Kochen, S. and Specker, E.P. (1967). J. Math. Mech. 17, 59-87.
- Cabello, A., Estebaranz, J.M., Garcia-Alcaine, G. (1996). Phys. Lett. A 212, 183-187.
- Ishihara, H. (2006). Reverse mathematics in Bishop's constructive mathematics.
- Bridges, D. and Richman, F. (1987). Varieties of Constructive Mathematics.
