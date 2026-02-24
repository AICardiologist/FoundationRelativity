# Paper 71 — The Archimedean Principle in Cryptography and Numerical Computation

Engineering Applications of Constructive Reverse Mathematics

## Contents

- `paper71.tex` — LaTeX source
- `paper71.pdf` — Compiled paper (15 pages)
- `P71_QuantumCRM/` — Lean 4 formalization bundle

**DOI:** [10.5281/zenodo.18752015](https://doi.org/10.5281/zenodo.18752015)

## Lean 4 Bundle

**Toolchain:** leanprover/lean4:v4.28.0-rc1 (+ Mathlib)

**Build:**
```
cd P71_QuantumCRM
lake build
```

**Result:** 0 errors, 0 warnings, 0 sorry

### File Structure

| File | Content |
|------|---------|
| `Defs.lean` | CRM hierarchy, descent types, target types, conjugacy levels, dimensional arguments |
| `Problems.lean` | Cryptographic problem profiles, scheme profiles, approximation regimes, algorithm types |
| `Security.lean` | All four main theorems + assembly |
| `Integrality.lean` | Sum-of-integer-squares lemma (signed permutation row condition) |
| `Main.lean` | Root module + axiom audit |

### Axiom Audit

- Classification theorems (native_decide): `Lean.ofReduceBool`, `Lean.trustCompiler`
- Integrality lemma (Mathlib proof): `propext`, `Classical.choice`, `Quot.sound`

## Summary

Four engineering consequences of the Archimedean Principle (Paper 70):

1. **Archimedean Security** — Lattice crypto resists Shor; RSA/ECC do not
2. **SVP Phase Transition** — Exponential approximation is BISH (LLL); polynomial is BISH+MP (BKZ)
3. **Conjugacy Design Principle** — Kyber > NTRU > RSA ordered by spectral conjugacy
4. **Eigendecomposition Integrality** — Algebraic-direct is BISH; eigendecompose+round is BISH+MP
