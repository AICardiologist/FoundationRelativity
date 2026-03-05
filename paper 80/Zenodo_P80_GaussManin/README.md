# Paper 80: Algebraic Gauss-Manin via Griffiths Pole Reduction

**Paper 80, Constructive Reverse Mathematics Series**
Paul Chun-Kit Lee, New York University

## Summary

Paper 80 upgrades the CRMLint Squeeze protocol from exact arithmetic
over Q (Papers 77-78) to symbolic algebra over the function field Q(t).
The target is the Legendre elliptic family y^2 = x(x-1)(x-t).  The
Classical Boundary Node is the Ehresmann-Gauss-Manin theorem (analytic
continuation, Ehresmann fibration, transcendental analysis).  The
constructive path computes the Gauss-Manin connection matrix via
Griffiths pole reduction in algebraic de Rham cohomology over Q[t],
verified by the `ring` tactic in Lean 4 (0 sorry).

## Main Results

- **Theorem A (Picard-Fuchs):** The PF operator L = t(1-t)d^2/dt^2 + (1-2t)d/dt - 1/4 is computed algebraically via pole reduction
- **Theorem B (Connection Matrix):** The 2x2 Gauss-Manin connection matrix M(t) is verified by polynomial identity
- **Theorem C (CRM Descent):** CLASS (Ehresmann-Gauss-Manin) -> BISH (polynomial algebra over Q[t])
- **Infrastructure upgrade:** `ring` tactic over Q(t) replaces `native_decide` over Z

## Files

| File | Description |
|------|-------------|
| `paper80.tex` | LaTeX source |
| `paper80.pdf` | Compiled paper |
| `solve_gauss_manin.py` | SymPy CAS script (emits GMData.lean) |
| `P80_GaussManin/` | Lean 4 bundle |

## Lean 4 Build Instructions

```bash
cd P80_GaussManin
lake update       # downloads Mathlib (first time only)
lake build        # builds all files
```

### Requirements

- **Lean toolchain:** `leanprover/lean4:v4.29.0-rc2`
- **Mathlib:** latest (resolved via `lake update`)
- **Python:** 3.10+ with SymPy >= 1.12 (for CAS script only)

### Lean File Structure

| File | Lines | Content |
|------|-------|---------|
| `GMData.lean` | 278 | CAS-emitted polynomial identities: PF coefficients, connection matrix, Griffiths division, coboundary identity, hypergeometric recurrence and closed form |
| `Paper80_GaussManin.lean` | 245 | CRM architecture: hierarchy, CLASS boundary node (Ehresmann), BISH Squeeze theorem, tactic upgrade demo, CRM audit |
| **Total** | **523** | **0 sorry** |

## Axiom Inventory

| Theorem | Axioms | Status |
|---------|--------|--------|
| `pf_coeff_*` identities | (none) | BISH |
| `griffiths_division` | (none) | BISH |
| `gauss_manin_squeeze` | propext, Classical.choice, Quot.sound | BISH* |
| `ehresmann_gauss_manin_existence` | (itself -- axiom) | CLASS (unused) |

*Classical.choice is Lean kernel infrastructure (decidable equality for Q),
not mathematical classical content.

## Dependencies

- Paper 77: CRMLint Squeeze protocol
- Paper 72: DPT biconditional characterization
- Paper 50: DPT framework

## CRM Classification

- **BISH components:** Griffiths pole reduction, polynomial identities (`ring`), PF operator coefficients
- **CLASS components:** Ehresmann fibration theorem, analytic continuation, transcendental period integrals (all unused by squeeze)

## License

CC BY 4.0
