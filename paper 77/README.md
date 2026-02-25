# Paper 77: Automated De-Omniscientisation — Reverse-Engineering Classical Proofs via DAG Surgery

Paper 77, Constructive Reverse Mathematics Series

Author: Paul Chun-Kit Lee, New York University
Date: February 2026
DOI: (pending)

## Overview

This paper introduces the **CRMLint Squeeze**, a systematic protocol for reverse-engineering classical proofs into constructive ones by combining CRM logical cost analysis with AI-driven combinatorial search. The method identifies the Classical Boundary Node (CBN) — the exact lemma where a classical proof invokes an omniscience principle — excises it from the Lean 4 environment, and tasks an RL-trained prover with closing the gap using only BISH-admissible tactics. The CRM classification acts as a reward function: +10 for a BISH closure, -1 for any branch introducing CLASS dependencies.

The primary target is Greg Anderson's exotic Weil classes on CM abelian fourfolds (E^4). The Hodge Conjecture guarantees an algebraic cycle exists (CLASS), but provides no construction. Finding the cycle is a bounded Q-linear algebra problem in the Chow group — a finite combinatorial search over intersection products of abelian subvarieties, CM endomorphism graphs, and twisted diagonal embeddings.

This paper marks the transition of the CRM program from *diagnostic* (auditing classical proofs, Papers 1-76) to *generative*: using the logical cost metric as a loss function that forces the production of explicit algebraic structures.

### Main Results

| Result | Statement | Type |
|--------|-----------|------|
| Protocol | CRMLint Squeeze: Scaffold -> X-Ray -> Excise -> Squeeze | Methodological |
| Target | Anderson exotic Weil class on E^4 as bounded Q-linear search | Architectural |
| Architecture | Lean 4 stub separating CLASS axiom from BISH Sigma-target | Formal |

## Contents

```
paper 77/
  README.md                          This file
  metadata.txt                       Plain-text Zenodo metadata
  paper77.tex                        LaTeX source
  paper77.pdf                        Compiled PDF (when available)
  P77_DAGSurgery/
    lean-toolchain                   leanprover/lean4:v4.29.0-rc2
    lakefile.lean                    Lake build configuration
    Papers.lean                      Root import file
    Papers/P77_DAGSurgery/
      Paper77_CMFourfold.lean        CM fourfold squeeze architecture
```

## How to Build (Lean)

Requires Lean 4 (v4.29.0-rc2) and an internet connection for Mathlib download.

```bash
cd P77_DAGSurgery
lake update    # fetch Mathlib4 (first time only)
lake build     # build — will report 1 sorry (the squeeze target)
```

The single `sorry` in `Paper77_CMFourfold.lean` is the squeeze target. It will be replaced by the AI prover's output when the MCTS run completes.

## How to Build (LaTeX)

```bash
pdflatex paper77.tex
pdflatex paper77.tex   # second pass for references
```

## Lean Stub Structure

The stub physically separates:
1. **The Classical Boundary Node** (`hodge_conjecture_existence`): marked CLASS, present but unused
2. **The constructive Sigma-target** (`exotic_cycle_constructive`): the goal the AI must close
3. **Restricted generators**: `projection_graph`, `cm_graph`, `twisted_diagonal` — the only permitted building blocks

CRMLint verifies that the completed proof does not transitively depend on the classical axiom.

## CRM Series Context

Paper 77 is part of the Constructive Reverse Mathematics program (Papers 1-77). It is the first paper in the series that is *methodological* rather than *classificatory*. Papers 1-76 asked "what is the logical cost of theorem X?" Paper 77 asks "given the logical cost, can we force an AI to discover a cheaper proof?"

Future targets:
- Paper 78: Explicit Local Langlands for wildly ramified representations
- Paper 79: Standard Conjecture D for abelian fourfolds (dim 4)

## License

Lean 4 code: Apache License 2.0
LaTeX paper and PDF: CC-BY 4.0
Copyright 2026 Paul Chun-Kit Lee

## Acknowledgments

Lean 4 formalization produced using AI code generation (Claude Code)
under human direction. The CRMLint Squeeze protocol was developed
collaboratively between the author and AI. Deep mathematics is due to
Anderson, Weil, Hodge, Lieberman, and the arithmetic geometry community.
