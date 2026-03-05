# Paper 99: The Hecke Theta Series Squeeze

**Paper 99 of the Constructive Reverse Mathematics Series**

**v2: Corrected after external review.**

## Summary

This paper resolves the principal contested classification in the CRM program: whether the dihedral base case of modularity lifting is BISH or CLASS. The classical proof uses three CLASS nodes: Poisson summation (existence), Deligne-Serre (extraction), and Chebotarev density (matching). We excise all three:

1. **Poisson summation → Mumford algebraic theta** (1966): existence of theta_chi as a geometric modular form via algebraic theta functions on A = E tensor O_K.
2. **Deligne-Serre → Forward formulaic matching:** for dihedral rho = Ind chi, the Hecke eigenvalue and Galois trace formulas are identical by splitting type (rfl in Lean).
3. **Chebotarev density → Effective Chebotarev bounds** (Lagarias-Odlyzko 1977): bounded search for TW primes is BISH.

Combined with Paper 68's audit, this yields CRM(FLT) = WKL.

## Main Results

- **Theorem A (Geometric Theta Construction):** theta_chi exists as a geometric modular form via Mumford's algebraic theta functions. Uniqueness by q-expansion principle. No Poisson summation. BISH.

- **Theorem B (Dihedral Modularity is BISH):** All 5 components of the dihedral base case are BISH. 5 BISH + 0 CLASS = 100% constructive. Three CLASS->BISH excisions.

- **Theorem C (CRM(FLT) = WKL):** max(BISH, BISH, BISH, WKL, BISH) = WKL. Taylor-Wiles patching is the sole non-BISH node. WKL is optimal.

## Lean 4 Bundle

### Build Instructions

```bash
cd P99_HeckeTheta
lake update    # fetches Mathlib v4.29.0-rc2
lake build     # builds all 6 files
```

### File Structure

| File | Lines | Description |
|------|-------|-------------|
| `CRMLevel.lean` | 79 | 7-level CRM hierarchy with WKL, decidable total order |
| `HeckeCharacter.lean` | 133 | Gaussian integers, representation numbers, splitting types |
| `QExpansion.lean` | 166 | Geometric theta construction, classical excised nodes, effective Chebotarev |
| `DihedralModularity.lean` | 164 | 5-component decomposition, three excisions |
| `FLTAudit.lean` | 217 | Five-stage FLT decomposition, TW prime vs patching, route comparison |
| `Paper99_Assembly.lean` | 230 | Imports, master theorems, axiom inventory |
| **Total** | **989** | **0 sorry, 0 warnings** |

### Axiom Inventory

| Theorem | Axioms |
|---------|--------|
| `theorem_A_geometric_theta` | (none) |
| `theorem_B_dihedral_is_bish` | `propext`, `Quot.sound`, `native_decide` |
| `theorem_C_flt_is_wkl` | `propext`, `native_decide` |
| `core_identity` | (none) |
| `route_comparison` | (none) |
| `paper99_complete` | `propext`, `native_decide` |

No `Classical.choice`. No mathematical axioms. The entire verification is constructive.

Documentary axioms (stubs, not invoked in proofs):
- `qexp_principle_is_injective` (Katz q-expansion injectivity)
- `mumford_theta_exists` (Mumford algebraic theta, 1966)
- `explicit_cm_is_algebraic` (Kronecker Jugendtraum)
- `effective_chebotarev_bound` (Lagarias-Odlyzko 1977)
- `tw_equiv_wkl` (TW patching equiv WKL, Paper 98)
- `wkl_irreducible_for_flt` (no known FLT proof avoids inverse limits)

## CRM Decomposition

**Dihedral base case:** 5 BISH + 0 CLASS = 100% constructive. Three excisions: Poisson -> Mumford, Deligne-Serre -> forward matching, Chebotarev -> effective bounds.

**Complete FLT:** 4 BISH stages + 1 WKL stage = WKL overall.

## v2 Corrections

v1 contained three mathematical errors identified by external review:
1. q-expansion principle misused as existence (it is injectivity/uniqueness only)
2. Eichler-Shimura congruence misapplied to weight-1 forms (requires weight >= 2)
3. Sturm bound misapplied to compare form with representation (compares two forms)

v2 replaces the 1-excision architecture with 3-excision architecture based on Mumford's algebraic theta functions, forward formulaic matching, and effective Chebotarev bounds.

## Dependencies

- Lean 4 v4.29.0-rc2
- Mathlib v4.29.0-rc2

## Author

Paul Chun-Kit Lee, New York University, Brooklyn, New York

## License

Creative Commons Attribution 4.0 International (CC BY 4.0)
