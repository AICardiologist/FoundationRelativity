# Paper 86: The Hodge Conjecture for Exotic Weil Classes via Kani-Rosen Splitting

Paper 86 of the Constructive Reverse Mathematics Series.

## Main Results

**Theorem A (Kani-Rosen Splitting).** The genus-4 curve C_t: y^2 = x^9 - tx^5 + x admits an involution mu(x,y) = (1/x, y/x^5) generating a D_8 action. The Jacobian splits: J(C_t) ~ J(Q_1) x J(Q_2) where Q_1, Q_2 are genus-2 quotient curves.

**Theorem B (Quotient Isomorphism).** Over C, Q_1 ≅ Q_2, so J(C_t) ~ A^2 for abelian surface A = J(Q_1).

**Theorem C (Hodge Conjecture).** For generic t, the exotic Weil class omega in wedge^4(V_+) on J(C_t)^2 is algebraic.

## Lean 4 Verification

```bash
cd P86_KaniRosen
lake build          # zero sorry, zero errors
```

### File Structure

- `Papers/P86_KaniRosen/QuotientData.lean` — CAS-emitted polynomial identities (ring/decide)
- `Papers/P86_KaniRosen/Paper86_KaniRosen.lean` — Main squeeze theorem, CRM audit

### Axiom Inventory

```
#print axioms kani_rosen_hodge_squeeze
-- [propext, Quot.sound]
```

No Classical.choice. The squeeze theorem is entirely constructive.

## CAS Verification

```bash
python3 verify_kani_rosen.py    # SymPy cross-check
```

## CRM Classification

- **BISH content:** Reciprocal involution, D_8 relation, Chebyshev factorizations, quotient curve equations, isomorphism Q_1 ≅ Q_2, differential decomposition, diagonal crossing det ≠ 0.
- **CLASS content:** Kani-Rosen theorem (1989), Zarhin MT group, Weyl invariant theory.
- **Ninth CRMLint Squeeze.**

## Dependencies

- Paper 84: Established exotic Weil class, proved tau_+ = 0 (flatness).
- Paper 85: Universal flatness across genus-4 families.
- Paper 86: Proves algebraicity for the Paper 84 family.

## Author

Paul Chun-Kit Lee, New York University
