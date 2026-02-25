# Paper 73: Standard Conjecture D Is Necessary for Constructive Morphism Decidability

**Paper 73, Constructive Reverse Mathematics Series**

## Summary

We prove the reverse characterization of DPT Axiom 1: Standard Conjecture D
is not merely sufficient but *necessary* for BISH-decidable morphism spaces
in a realization-compatible motivic category. Combined with the forward
direction (Papers 46, 50), this gives a biconditional:

> Conjecture D &hArr; BISH morphism decidability (in a faithful motivic category)

Jannsen's theorem (1992) confirms the trade-off is sharp: numerical motives
are semisimple and BISH-decidable *without* Conjecture D, but lack faithful
l-adic realization.

## Main Results

- **Theorem A** (Forward): Conjecture D converts LPO-dependent homological
  equivalence to BISH-decidable numerical equivalence.
- **Theorem B** (Biconditional): morphism_cost(r) = BISH iff r = detachable
  iff Conjecture D holds.
- **Theorem C** (Characterization): Axiom 1 is necessary and sufficient.
- **Corollary**: Jannsen obstruction — BISH or faithful, not both, without D.

## Lean 4 Formalization

Bundle: `P73_Axiom1Reverse/`

| File | Content |
|------|---------|
| `Defs.lean` | CRM hierarchy, RadicalStatus, axiomatized morphism costs |
| `Forward.lean` | Theorem A: Conj D -> BISH |
| `Reverse.lean` | Theorem B: biconditional + Jannsen obstruction |
| `Characterisation.lean` | Theorem C: full assembly + sharpened principle |
| `Main.lean` | Aggregator with #check statements |

**Build:** `lake build` from `P73_Axiom1Reverse/` directory.
Toolchain: `leanprover/lean4:v4.29.0-rc2`, Mathlib4.
Zero `sorry`, zero warnings, 4 axioms (2 data + 2 propositional).

## Axiom Inventory

| Axiom | Value | Reference |
|-------|-------|-----------|
| `conjD_morphism_cost` + `_eq` | BISH | Paper 46 T2/T4b, Paper 50 S6 |
| `no_conjD_morphism_cost` + `_eq` | LPO | Paper 46 T4a |

## Dependencies

- Paper 46: Tate CRM (homological equiv requires LPO, Conj D decidabilizes)
- Paper 50: DPT axiom system (Conj D as Axiom 1)
- Paper 72: DPT characterization (Axiom 3 biconditional, minimality)

## Author

Paul Chun-Kit Lee, New York University, Brooklyn, NY
