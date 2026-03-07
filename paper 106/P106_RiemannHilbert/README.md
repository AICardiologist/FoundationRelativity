# Paper 106: CRM Audit of the Riemann-Hilbert Correspondence

**Eighteenth CRMLint Application**

Paper 106 of the Constructive Reverse Mathematics Series.

## Summary

First CRM audit of the regular holonomic Riemann-Hilbert correspondence (Deligne 1970, Kashiwara 1984, Mebkhout 1980). The proof decomposes into 16 atomic components across four phases:

- **10 BISH** + **4 WLPO** + **1 LPO** + **1 CLASS** = 16 components (62.5% constructive)

Three main results:
- **Theorem A**: Deligne's canonical extension is equivalent to LPO via the floor function on R.
- **Theorem B**: GAGA descent (Montel's theorem) is the unique CLASS component, confirming the Archimedean Obstruction Thesis (Paper 98).
- **Theorem C**: For rational parameters, the Deligne obstruction collapses to BISH. Test case: 2F1(1/4, 1/3; 2/3; z).

## Lean 4 Build

```bash
cd P106_RiemannHilbert
lake build
```

**Toolchain**: `leanprover/lean4:v4.29.0-rc2`
**Mathlib**: via `lakePackages` (see `lakefile.lean`)

## File Structure

| File | Lines | Content |
|------|-------|---------|
| `CRMLevel.lean` | 75 | CRM hierarchy (BISH/LLPO/WLPO/LPO/CLASS), join, ordering |
| `RHData.lean` | 120 | CAS-emitted verification data: ODE parameters, indicial roots, exponent differences, non-resonance, Fuchs relation, Deligne shifts, Kummer matrix (documentary) |
| `Paper106_RiemannHilbert.lean` | 209 | Main file: component decomposition, Theorems A-C, test case verification, axiom inventory |

**Total**: 404 lines, 0 sorry, 0 warnings.

## Axiom Inventory

| Theorem | Axioms | Source |
|---------|--------|--------|
| `total_components` | (none) | `decide` on Nat is axiom-free |
| `constructive_fraction` | (none) | `decide` on Nat is axiom-free |
| `test_fuchs` | propext, Classical.choice, Quot.sound | Mathlib's DivisionRing hierarchy (artifact) |
| `test_deligne_in_strip` | propext, Classical.choice, Quot.sound | Mathlib's DivisionRing hierarchy (artifact) |
| `diff_zero_not_int` | propext, Quot.sound | No Classical.choice |

**Documentary axioms** (unused in any proof term):
- `floor_implies_LPO`: A total floor function on R implies LPO (Bridges-Richman 1987)
- `gaga_descent_requires_LEM`: GAGA descent requires LEM (Cartan A/B via Montel)

## Classical.choice Audit

Classical.choice in `test_fuchs` and `test_deligne_in_strip` enters through Mathlib's generic `DivisionRing`/`LinearOrderedField` hierarchy (totalized inverse 0⁻¹ = 0), not from logical content. The Rat type is 100% computable. Constructive stratification is established by proof content, not axiom checker output.

## Dependencies

- Lean 4 (v4.29.0-rc2)
- Mathlib4

## Author

Paul Chun-Kit Lee, New York University, Brooklyn, New York.

## License

CC BY 4.0
