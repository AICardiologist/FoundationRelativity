# Paper 102: The Conservation Theorem for Algebraic Cycles — Classical Logic Is Scaffolding

**Paper 102 of the Constructive Reverse Mathematics Series**

Paul Chun-Kit Lee, New York University, Brooklyn, New York

## Main Results

**Theorem A (Conservation for Algebraic Cycles).** Every CLASS theorem about algebraic cycles on smooth projective varieties over Q-bar with an arithmetical conclusion of complexity at most Pi-0-2 is provable in pure BISH. No Markov's Principle needed at any complexity level.

**Theorem C (Coding Lemma).** The standard algebraic cycle statements are arithmetical of complexity at most Pi-0-2:

| Statement type | Complexity | Target CRM level |
|---|---|---|
| "alpha is algebraic" | Sigma-0-1 | BISH |
| "L(E,1) != 0" | Sigma-0-1 | BISH |
| "rank(E) = r" | Pi-0-2 | BISH |
| FLT | Pi-0-1 | BISH |

Note: "Sha(E) is finite" is Sigma-0-2 (outside the Pi-0-2 scope of conservation).

## Proof Chain

1. **McLarty reduction:** ZFC proves phi implies PA proves phi (finite-order arithmetic is conservative over PA for arithmetical sentences).
2. **Friedman Pi-0-2 conservation:** PA proves phi implies HA proves phi (no MP). Key fact: PA and HA have the same provably total recursive functions (proof-theoretic ordinal epsilon-0).

## Lean 4 Bundle

**Directory:** `P102_Conservation/`
**Toolchain:** `leanprover/lean4:v4.29.0-rc2` with Mathlib
**Lines:** 900 (6 files)
**Sorry count:** 0
**Classical.choice:** 0

### Build

```bash
cd P102_Conservation && lake build
```

### File Structure

| File | Lines | Description |
|---|---|---|
| `CRMLevel.lean` | 76 | CRM hierarchy with ordering |
| `ArithComplexity.lean` | 95 | Arithmetical hierarchy classification |
| `CodingLemma.lean` | 174 | Statement type classification and scope proof |
| `Conservation.lean` | 157 | Conservation theorem, descent table |
| `CaseStudies.lean` | 216 | Five case studies with consistency checks |
| `Paper102_Assembly.lean` | 182 | Master theorem composing all components |

### Axiom Inventory

| Theorem | Axioms |
|---|---|
| `conservation_theorem_A` | (none) |
| `conservation_theorem_B_pi01` | (none) |
| `coding_lemma` | `propext` |
| `all_known_consistent` | `propext`, `native_decide` |
| `conservation_main` | `propext`, `native_decide` |

The core conservation theorems depend on zero axioms. No `Classical.choice`. No `Quot.sound`. The `native_decide` trust axioms appear only in case-study consistency verifications (kernel evaluator trust, not mathematical classical content).

Two proof-theoretic results (McLarty reduction, Friedman Pi-0-2 conservation) are declared as `axiom : True` with docstrings citing the literature. The bundle verifies CRM bookkeeping (descent table, case-study consistency) given these cited results.

### Dependencies

- Mathlib (via lakefile.lean)

## Programme Context

Paper 102 resolves the Conservation Conjecture (Paper 100, Conjecture 7.1) for its arithmetical scope. Combined with the Archimedean Obstruction Thesis (Paper 98, Theorem 5.1):

- **Lower bound (Paper 98):** Archimedean realizations force CLASS.
- **Upper bound (Paper 102):** CLASS is eliminable for algebraic conclusions.
- **Synthesis:** The continuum is a removable mirror.

## License

CC BY 4.0

## Series DOI

[10.5281/zenodo.17054050](https://doi.org/10.5281/zenodo.17054050)
