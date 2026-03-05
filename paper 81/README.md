# Paper 81: The Fixed Part Theorem via Tensor Gauss-Manin

**Paper 81, Constructive Reverse Mathematics Series**
Paul Chun-Kit Lee, New York University

## Summary

Paper 81 computes the 4x4 tensor Gauss-Manin connection on H^1 ⊗ H^1
for the Legendre elliptic family via the Kronecker sum N(t) = M⊗I₂ + I₂⊗M,
where M is the base connection matrix from Paper 80.  The symplectic
intersection form W = (0,1,-1,0) is verified as a constant flat section,
and the constant kernel of N(t) is shown to be exactly one-dimensional
(span{W}).  This is the algebraic analogue of Deligne's Theorem of the
Fixed Part (1972), proved entirely by polynomial linear algebra over Q[t]
within BISH.

## Main Results

- **Theorem A (Tensor Connection):** N(t) = [[2t,-1,-1,0],[t,0,0,-1],[t,0,0,-1],[0,t,t,-2t]]
- **Theorem B (Flat Section):** N(t)·W = 0 for all t ∈ Q; N(t)·S ≠ 0
- **Theorem C (Fixed Part Squeeze):** constant kernel = span{W}, 1-dimensional
- **CRM Descent:** CLASS (Deligne's monodromy theorem) → BISH (polynomial linear algebra)

## Files

| File | Description |
|------|-------------|
| `paper81.tex` | LaTeX source (15 pages, 20 references) |
| `paper81.pdf` | Compiled paper |
| `solve_flat_sections.py` | SymPy CAS script (emits FlatData.lean) |
| `P81_FlatSections/` | Lean 4 bundle |

## Lean 4 Build Instructions

```bash
cd P81_FlatSections
lake update       # downloads Mathlib (first time only)
lake build        # builds all files
```

### Requirements

- **Lean toolchain:** `leanprover/lean4:v4.29.0-rc2`
- **Mathlib:** latest (resolved via `lake update`)
- **Python:** 3.10+ with SymPy ≥ 1.12 (for CAS script only)

### Lean File Structure

| File | Lines | Content |
|------|-------|---------|
| `FlatData.lean` | 263 | CAS-emitted tensor connection entries, 25 identities |
| `Paper81_FlatSections.lean` | 194 | CRM architecture, squeeze theorem, audit |
| **Total** | **457** | **0 sorry** |

## Axiom Inventory

| Theorem | Axioms | Status |
|---------|--------|--------|
| `flat_W_row0` through `flat_W_row3` | (none) | BISH |
| `kernel_K_row0` through `kernel_K_row3` | (none) | BISH |
| `S_image_nonzero` | (none) | BISH |
| `constant_kernel_forces_a_zero` | (none) | BISH |
| `flat_sections_squeeze` | propext, Classical.choice, Quot.sound | BISH* |
| `deligne_fixed_part_existence` | (itself — axiom) | CLASS (unused) |

*Classical.choice is Lean kernel infrastructure (decidable equality for Q),
not mathematical classical content.

## Dependencies

- Paper 80: Base Gauss-Manin connection matrix M(t)
- Paper 50: DPT framework
- Paper 72: Biconditional characterization theorem

## CRM Classification

- **8 BISH components:** polynomial identities (ring), structural equalities (rfl),
  non-flatness witness (decide), constant kernel restriction (linarith)
- **3 CLASS components:** Deligne's Theorem of the Fixed Part, topological monodromy
  representation, comparison theorem (all unused by the squeeze)

## License

CC BY 4.0
