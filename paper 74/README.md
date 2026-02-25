# Paper 74: Algebraic Spectrum Is Necessary for Constructive Eigenvalue Decidability

**Paper 74, Constructive Reverse Mathematics Series**

## Summary

We prove the reverse characterization of DPT Axiom 2: algebraic spectrum
(geometric origin) is not merely sufficient but *necessary* for BISH-decidable
eigenvalue comparison. Combined with the forward direction (Paper 45), this
gives a biconditional:

> Algebraic spectrum ⇔ BISH eigenvalue decidability

This completes the DPT axiom trilogy:
- Paper 72: Axiom 3 ↔ BISH cycle-search (cost without: LPO)
- Paper 73: Axiom 1 ↔ BISH morphism decidability (cost without: LPO)
- Paper 74: Axiom 2 ↔ BISH eigenvalue decidability (cost without: WLPO)

The key distinction: Axiom 2 costs WLPO (equality test), not LPO (existential
search). Eigenvalue comparison is a single equality test on a spectral parameter,
not a search through an infinite structure.

## Main Results

- **Theorem A** (Forward): Algebraic spectrum → BISH eigenvalue comparison.
- **Theorem B** (Biconditional): eigenvalue_cost(s) = BISH iff s = algebraic.
- **Theorem C** (Characterization): Axiom 2 is necessary and sufficient.
- **Corollary**: Deligne constraint — BISH or full analytic spectrum, not both.

## Lean 4 Formalization

Bundle: `P74_Axiom2Reverse/`

| File | Content |
|------|---------|
| `Defs.lean` | CRM hierarchy, SpectrumType, axiomatized eigenvalue costs |
| `Forward.lean` | Theorem A: algebraic → BISH |
| `Reverse.lean` | Theorem B: biconditional + Deligne constraint |
| `Characterisation.lean` | Theorem C: full assembly + sharpened principle |
| `Main.lean` | Aggregator with #check statements |

**Build:** `lake build` from `P74_Axiom2Reverse/` directory.
Toolchain: `leanprover/lean4:v4.29.0-rc2`, Mathlib4.
Zero `sorry`, zero warnings, zero propext, 4 axioms (2 data + 2 propositional).

## Axiom Inventory

| Axiom | Value | Reference |
|-------|-------|-----------|
| `algebraic_eigenvalue_cost` + `_eq` | BISH | Paper 45 C1, Deligne (1974) |
| `continuous_eigenvalue_cost` + `_eq` | WLPO | Paper 45 C2, Bump (1997) |

## Dependencies

- Paper 45: Weil eigenvalue CRM (algebraic spectrum = BISH, continuous = WLPO)
- Paper 50: DPT axiom system (Axiom 2 definition)
- Paper 72: DPT characterization (Axiom 3 biconditional, minimality)
- Paper 73: Axiom 1 reverse (Conjecture D biconditional)

## Author

Paul Chun-Kit Lee, New York University, Brooklyn, NY
