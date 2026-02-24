# Paper 26: The Godel-Gap Correspondence

**A Lean 4 Formalization of the Order-Embedding of the Lindenbaum Algebra
of Pi-0-1 Sentences into the Bidual Gap l-infinity/c_0**

Part of the Constructive Reverse Mathematics (CRM) calibration series.

## Main Result

The Lindenbaum algebra of Pi-0-1 sentences of Peano Arithmetic, quotiented
by provable equivalence, order-embeds into the bidual gap l-infinity/c_0.

- **Godel-Gap map Phi**: LindenbaumPi01 -> BidualGap (injective)
- **Gap detection**: Phi([phi]) = [0] iff phi is refutable
- **Calibration**: WLPO <-> Pi-0-1 consistency decidable <-> gap detection decidable

## Module Structure

| Module | Content | Lines |
|--------|---------|-------|
| `Basic.lean` | WLPO, bounded sequences, bidual gap | 110 |
| `ArithmeticSide.lean` | Axiomatized PA, Lindenbaum algebra | 291 |
| `AnalyticSide.lean` | Rows, rowChar, logical gap sublattice | 131 |
| `GodelSequence.lean` | Godel sequence v^phi, key properties | 147 |
| `Correspondence.lean` | Phi, injectivity, gap detection | 220 |
| `CalibrationLink.lean` | WLPO <-> gap detection | 137 |
| `Main.lean` | Aggregator and axiom audit | 177 |
| **Total** | | **1,213** |

## Building

```bash
lake build
```

Requires `leanprover/lean4:v4.28.0-rc1` (see `lean-toolchain`).

## Axiom Profile

- **Standard Lean axioms**: propext, Classical.choice, Quot.sound
- **Custom axioms (30)**: Standard metamathematical properties of PA
  (sentences, Godel numbering, decidable proof predicate, provable
  equivalence, consistency). All are theorems in any standard
  formalization of Godel numbering.
- **Sorries (3)**: Technical arguments about well-orderings and
  indicator functions of disjoint infinite sets.

## CRM Calibration

| Result | Principle | Paper |
|--------|-----------|-------|
| Bidual gap != 0 | WLPO | 2 |
| Gap detection decidable | WLPO | 26 |
| Pi-0-1 consistency decidable | WLPO | 26 |
| Gap contains Lindenbaum algebra | (structural) | 26 |

## Paper

The accompanying paper `paper26_godel_gap.tex` provides the mathematical
exposition. Compile with:

```bash
pdflatex paper26_godel_gap.tex
pdflatex paper26_godel_gap.tex
```

## Author

Paul Chun-Kit Lee (dr.paul.c.lee@gmail.com)

AI-assisted formalization (Claude, Anthropic).

DOI: [10.5281/zenodo.18615457](https://doi.org/10.5281/zenodo.18615457)
