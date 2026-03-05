# Paper 87: The Omniscience Cost of the Hodge Conjecture

Paper 87 of the Constructive Reverse Mathematics Series.

## Summary

The first CRM analysis of a Clay Millennium Problem. We measure the logical cost of the Hodge condition — the test that determines whether a rational cohomology class on an abelian variety is of type (p,p).

## Main Results

- **Theorem A**: When algebraic metadata is available (CM type via Shiga-Wolfart, or known Mumford-Tate group via Moonen-Zarhin), the Hodge test is BISH-decidable.
- **Theorem B**: The uniform Hodge test (a single algorithm for arbitrary period matrices as Cauchy sequences) is equivalent to WLPO.
- **Theorem C**: HodgeTestCost(state) = BISH iff algebraic metadata is available.
- **Theorem D**: Over Q-bar, algebraic period entries iff CM (Shiga-Wolfart 1985).

## What This Paper Does NOT Claim

- It does not prove or disprove the Hodge conjecture.
- It does not establish a biconditional between the Hodge conjecture and an omniscience principle.

## Lean 4 Bundle

- **Location**: `P87_HodgeCost/`
- **Toolchain**: `leanprover/lean4:v4.29.0-rc2`
- **Lines**: 602
- **Sorry count**: 0

### Build Instructions

```bash
cd P87_HodgeCost
lake build
```

### Axiom Inventory

**Infrastructure** (standard Lean/Mathlib):
- `propext`, `Classical.choice`, `Quot.sound`

**Mathematical** (encoding proven theorems):
- `AnalyticPeriodMatrix`, `hodge_projection` — abstract Siegel upper half-space
- `embed_real`, `embed_proj` — period matrix perturbation (embedding reduction)
- `cm_hodge_cost_eq` — Shiga-Wolfart + K-linear algebra → BISH
- `mt_hodge_cost_eq` — MT invariants + Q-linear algebra → BISH
- `bare_hodge_cost_eq` — Bridges-Richman 1987 → WLPO
- `shiga_wolfart` — Shiga-Wolfart 1985 + Wüstholz 1989

### File Structure

| File | Lines | Content |
|------|-------|---------|
| CRMLevel.lean | 56 | CRM hierarchy |
| HodgeTest.lean | 148 | Uniform test, embedding reduction, WLPO equivalence |
| CMDecidable.lean | 116 | Theorem A, cost function |
| Biconditional.lean | 82 | Theorem C |
| ShigaWolfart.lean | 107 | Theorem D |
| Paper87_HodgeCost.lean | 93 | Main file, axiom inventory |

## Dependencies

- Papers 72-74: DPT biconditional framework
- Papers 79-85: Computational evidence for Theorem A
- Bridges-Richman (1987): WLPO ↔ real equality
- Shiga-Wolfart (1985): Algebraic periods ↔ CM
- Moonen-Zarhin (1999): Hodge classes on generic abelian varieties

## License

Creative Commons Attribution 4.0 International (CC BY 4.0).
