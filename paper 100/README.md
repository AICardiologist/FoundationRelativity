# Paper 100: The Kuga-Satake Bifurcation

**K3 Hodge Classes via Shioda-Inose Descent**

Paper 100 of the Constructive Reverse Mathematics Series.
Sixteenth CRMLint application. First CRM analysis of K3 Hodge theory.

## Main Results

**Theorem A (K3 Hodge Bifurcation).** The CRM cost of verifying the Hodge conjecture for a projective K3 surface bifurcates at Picard number rho = 20:
- At rho = 20 (singular K3): CRM = BISH. Shioda-Inose gives CM elliptic curves; CM theory makes algebraicity decidable.
- At generic rho < 20: CRM = CLASS. Mumford-Tate group is maximal; Betti realization required.
- The jump BISH -> CLASS is maximal (no intermediate CRM level).

**Theorem B (CRMLint Decomposition).** 11 BISH + 5 CLASS = 16 components (69% BISH).

**Theorem C (Structural Parallel).** The K3 bifurcation is structurally identical to Paper 86's Kani-Rosen bifurcation for hyperelliptic Jacobians: a discrete algebraic invariant controls whether CLASS collapses to BISH.

**Conservation Conjecture.** Every CLASS theorem with a BISH-statable conclusion admits a lower-level proof. Open; consistent with all evidence from Papers 84-100.

## Lean Bundle

**Directory:** `P100_KugaSatake/`
**Lines:** 700 (0 sorry, 0 warnings)
**Toolchain:** leanprover/lean4:v4.29.0-rc2

### Build Instructions

```bash
cd P100_KugaSatake
lake build
```

### File Structure

| File | Content | Lines |
|------|---------|-------|
| CRMLevel.lean | CRM hierarchy and ordering | 65 |
| K3Lattice.lean | K3 lattice, Hodge numbers, Picard bounds | 133 |
| KugaSatake.lean | KS dimension, Clifford algebra, CM data, MT groups | 154 |
| Bifurcation.lean | Bifurcation theorem, CRM audit, Conservation Conjecture | 192 |
| Paper100_Assembly.lean | Main theorem (17 conjuncts), programme summary | 156 |

### Axiom Inventory

`#print axioms kuga_satake_main` produces:
- `propext` — Lean kernel axiom (proposition extensionality)
- `Quot.sound` — Lean kernel axiom (quotient soundness)
- `Classical.choice` — from `native_decide` on string list lengths (infrastructure, not mathematical content)

No mathematical Classical.choice. The formal content (lattice arithmetic, dimension formulas, CRM level assignments) is entirely constructive. Classical citations (Betti realization, Hodge theory, Mumford-Tate) appear in the paper text only.

## Key Mathematical Content

- **K3 lattice:** H^2(X,Z) = U^3 + E_8(-1)^2, rank 22, signature (3,19)
- **Kuga-Satake dimension:** 2^(20-rho) from transcendental lattice of rank 22-rho
- **Shioda-Inose at rho=20:** X -> Kum(E_1 x E_2) with CM elliptic curves
- **CM examples:** discriminants -3, -4, -7, -23, -163 (Heegner numbers)
- **Mumford-Tate:** dim 2 (CM torus) vs dim r(r-1)/2 (generic SO(T))

## Dependencies

- Lean 4 (v4.29.0-rc2)
- Mathlib (v4.29.0-rc2)

## Author

Paul Chun-Kit Lee, New York University, Brooklyn, New York.
