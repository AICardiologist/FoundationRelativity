# Paper 72: The DPT Characterization Theorem — Positive-Definite Height Is Necessary and Sufficient for Constructive Cycle-Search

**Paper 72, Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee, New York University, Brooklyn, NY

## Summary

We prove the reverse characterization of DPT Axiom 3: positive-definite
height pairing is not merely sufficient but *necessary* for BISH-decidable
cycle-search. Combined with the forward direction (Paper 70), the
Archimedean Principle becomes a biconditional:

> Positive-definite height (Axiom 3) &hArr; BISH cycle-search decidability

Without positive-definite height, cycle-search requires LPO (unbounded
existential search over an infinite lattice with no convergence guarantee).
The DPT axiom system is therefore the minimal axiom set for constructive
motivic decidability.

## Main Results

- **Theorem A** (Forward): Positive-definite height enables bounded
  cycle-search (BISH).
- **Theorem B** (Reverse): Without positive-definite height, cycle-search
  costs LPO.
- **Theorem C** (Characterization): Axiom 3 is necessary and sufficient.
  DPT axioms are minimal.
- **Corollary** (DPT-vs-FS Partition): Discrete sector (R, BISH, DPT) vs
  continuous sector (Q_p, CLASS, Fargues-Scholze) is logically forced.

## Lean 4 Bundle

**Directory:** `P72_DPTCharacterisation/`
**Toolchain:** `leanprover/lean4:v4.28.0-rc1`
**Build:** `cd P72_DPTCharacterisation && lake build`
**Lines:** ~350 lines
**Sorry count:** 0

### File Structure

| File | Content |
|------|---------|
| `Defs.lean` | CRM hierarchy, DPT axioms, height/search cost types |
| `HeightSearch.lean` | Forward: positive-definite height -> BISH search |
| `Minimality.lean` | Reverse: no height -> LPO search cost |
| `Characterisation.lean` | Assembly: biconditional + minimality |
| `Main.lean` | Entry point, `#check` statements |

### Axiom Inventory

| Axiom | Value | Reference |
|-------|-------|-----------|
| `pos_def_search_cost` + `_eq` | BISH | Paper 50 S5, Paper 70 Thm A |
| `no_pos_def_search_cost` + `_eq` | LPO | New (this paper) |

## Dependencies

- Paper 50: DPT axiom system (three axioms for the motive)
- Paper 70: Archimedean Principle (forward direction)

## Paper

- `paper72.tex` -- LaTeX source (10 pages)
- `paper72.pdf` -- compiled PDF
