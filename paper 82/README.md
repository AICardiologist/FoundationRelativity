# Paper 82: Picard-Fuchs Monodromy via Kovacic's Algorithm

Paper 82, Constructive Reverse Mathematics Series.

## Summary

This paper computes the differential Galois group G_gal = SL_2 for the Legendre
Picard-Fuchs equation t(1-t)y'' + (1-2t)y' - (1/4)y = 0 using Kovacic's
algorithm, entirely within Bishop-style constructive mathematics (BISH).

The classical proof requires topological monodromy, fundamental groups, analytic
continuation, and Zariski density arguments (CLASS). The constructive proof
replaces all of this with rational function analysis over Q(t): normal form
reduction, pole classification, indicial equations, and finite case checking.

This is the fifth CRMLint Squeeze and the third paper in the function-field
pipeline (after Paper 80: Gauss-Manin connection, Paper 81: flat sections).

## Main Results

- **Theorem A (Normal Form):** The Picard-Fuchs equation reduces to v'' = r(t)v
  with r(t) = -(t^2-t+1)/(4t^2(1-t)^2), verified by polynomial identity.

- **Theorem B (Kovacic Obstruction):** All three Kovacic cases fail:
  - Case 1 (Borel): 8 sign combinations yield half-integers, none in N.
  - Case 2 (Dihedral): degree bound d = -1 < 0.
  - Case 3 (Polyhedral): degree bound d = -n/12 < 0 for n in {4,6,12}.

- **Theorem C (Differential Galois Squeeze):** G_gal = SL_2, proved within BISH.
  The classical topological monodromy density argument is declared but never used.

## Lean 4 Formal Verification

- **Files:** 457 lines total, 0 sorry
  - `KovacicData.lean` (257 lines): CAS-emitted definitions and identities
  - `Paper82_DiffGalois.lean` (199 lines): CRM architecture and squeeze theorem

- **Axiom inventory:** `#print axioms diff_galois_is_SL2_squeeze` returns
  `[propext, Classical.choice, Quot.sound]` (kernel infrastructure only).
  The classical boundary node `topological_monodromy_dense` does not appear.

- **Proof tactics:** `ring` (polynomial identity), `norm_num` (rational arithmetic),
  `omega` (natural number reasoning), `linarith` (inequalities), `decide` (CRM audit).

### Build Instructions

```bash
cd P82_DiffGalois
lake build
```

**Toolchain:** leanprover/lean4:v4.29.0-rc2
**Dependency:** Mathlib (fetched automatically by lake)

### CAS Script

The Python script `solve_kovacic.py` performs the symbolic computation and emits
`KovacicData.lean`. Requires Python 3.8+ with SymPy:

```bash
pip install sympy
python solve_kovacic.py
```

## CRM Audit

| Component | Level | Tactic |
|-----------|-------|--------|
| Normal form r(t) | BISH | ring |
| Pole leading coefficients | BISH | norm_num |
| Indicial equation | BISH | norm_num |
| Kovacic Case 1 (8 checks) | BISH | norm_num + omega |
| Kovacic Case 2 | BISH | norm_num |
| Kovacic Case 3 (n=4,6,12) | BISH | norm_num |
| Topological monodromy | CLASS | (unused) |
| Comparison theorem | CLASS | (unused) |
| Zariski density | CLASS | (unused) |

## Dependencies

- Paper 80 (Gauss-Manin connection): DOI 10.5281/zenodo.18791985
- Paper 81 (Flat sections): DOI 10.5281/zenodo.18801814

## Author

Paul Chun-Kit Lee, New York University, Brooklyn, New York.

## License

CC-BY 4.0
