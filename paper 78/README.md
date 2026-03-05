# Paper 78: The Local Langlands Correspondence for GL₂(ℚ₂) Is Constructively Decidable

**Paper 78, Constructive Reverse Mathematics Series**
Paul Chun-Kit Lee, New York University

## Summary

Paper 78 applies the CRMLint Squeeze protocol to the Local Langlands
Correspondence (LLC) for wildly ramified supercuspidal representations
of GL_2(Q_2).  The Classical Boundary Node is Harris-Taylor's existence
theorem (Shimura varieties, etale cohomology, Lefschetz fixed-point).
The constructive path uses Bushnell-Kutzko type theory and
Bushnell-Henniart's explicit matching to reduce the LLC to a
character-trace identity over Z, verified by `decide` in Lean 4.

## Main Results

- **Theorem A (Squeeze):** The LLC for supercuspidal representations of GL_2(Q_2) arising from BK types descends from CLASS to BISH
- **Theorem B (Character-Trace Identity):** Matching identity verified as integer computation by `decide`
- **Theorem C (CRM Descent):** CLASS -> BISH (sharpest possible, no intermediate omniscience)
- **CRM Descent:** CLASS (Harris-Taylor existence) -> BISH (BK explicit matching over Z)

## Files

| File | Description |
|------|-------------|
| `paper78.tex` | LaTeX source (19 pages) |
| `paper78.pdf` | Compiled paper |
| `P78_WildLanglands/` | Lean 4 bundle |

## Lean 4 Build Instructions

```bash
cd P78_WildLanglands
lake update       # downloads Mathlib (first time only)
lake build        # builds all files
```

### Requirements

- **Lean toolchain:** `leanprover/lean4:v4.29.0-rc2`
- **Mathlib:** latest (resolved via `lake update`)

### Lean File Structure

| File | Lines | Content |
|------|-------|---------|
| `Paper78_WildLanglands.lean` | 206 | CRM hierarchy, BK types, Harris-Taylor axiom (CLASS), test case, Squeeze theorem, CRM audit |
| `WildLanglandsData.lean` | 189 | CAS-emitted character values, Galois traces, Frobenius eigenvalues, central char z=5, 9 matching theorems |
| **Total** | **395** | **0 sorry** |

Note: `WildLanglandsData.lean` is emitted by the Python CAS script
(`solve_wild_langlands.py`).

## Axiom Inventory

| Axiom | CRM Level | Used by Squeeze? |
|-------|-----------|-----------------|
| `harris_taylor_existence` | CLASS | No |
| `propext` | Lean kernel | Yes (infrastructure) |
| `Quot.sound` | Lean kernel | Yes (infrastructure) |
| `Classical.choice` | Lean kernel | Maybe (Mathlib import) |

All 9 matching theorems in `WildLanglandsData.lean` are proved by
`decide` (kernel-level computation on concrete integer data).

## Dependencies

- Paper 77: CRMLint Squeeze protocol
- Paper 72: DPT biconditional characterization
- Paper 50: DPT framework

## CRM Classification

- **BISH components:** BK type data, character computation, trace matching (all `decide`)
- **CLASS components:** Harris-Taylor existence theorem, Shimura varieties, etale cohomology (all unused by squeeze)

## License

CC BY 4.0
