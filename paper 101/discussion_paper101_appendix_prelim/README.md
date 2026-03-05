# CRMlint — Constructive Reverse Mathematics Proof Analysis Toolkit

**Author:** Paul Chun-Kit Lee  
**Date:** March 2026  
**Context:** Companion tools for Paper 98 (The Motivic CRM Architecture) and Paper 99 (CRMlint as Proof-Engineering Tool)

---

## Overview

This toolkit implements three generations of CRM analysis, from theoretical
framework through Mathlib validation to large-scale LaTeX scanning:

```
                    Paper 98 (Theory)
                         │
             ┌───────────┼───────────┐
             ▼           ▼           ▼
         crmlint.py  crmlint_    crmlint_
         (core       crawler.py  scanner.py
          framework) (Mathlib    (LaTeX
                      validation) at scale)
             │           │
             ▼           ▼
         crmlint_    crmlint_
         structure.py mathlib_report.txt
         (3-axis      
          profiling)   
             │
             ▼
         crmlint_structure_report.txt
```

---

## Files

### Python (4 modules, 3,417 lines total, zero external dependencies)

| File | Lines | Purpose |
|------|------:|---------|
| `crmlint.py` | 1,161 | **Core framework.** CRM hierarchy, realization functors with CRM costs, proof DAG model, substitution database (8 seed entries from Papers 50–97), comparison isomorphisms, Archimedean obstruction theorem. This is Paper 98 in code. |
| `crmlint_crawler.py` | 653 | **Mathlib crawler.** Fetches Lean 4 source files from Mathlib4 GitHub, parses declarations, heuristic-classifies each by CRM level using tactic/keyword signatures. Validated against 627 declarations across 10 files. |
| `crmlint_structure.py` | 793 | **Three-axis proof profiler.** Computes seven-dimensional proof profile vectors: CRM level (logical cost), proof complexity (structural cost: size, depth, width), modularity (architectural cost: coupling, automation ratio, rewrite density). Classifies proofs into types: TRIVIAL, ALGEBRAIC, COMPUTATIONAL, TOPOLOGICAL, ANALYTIC, CLASSICAL, BIFURCATING. |
| `crmlint_scanner.py` | 810 | **LaTeX scanner (Squeeze 2.0 triage).** Keyword + citation pattern matching against ~80 technique markers and ~120 landmark paper citations. Scans a directory of .tex files in seconds. Outputs per-paper bottleneck maps, aggregate CRM heatmaps, temporal drift analysis, CSV/JSON export. Anti-marker system suppresses false positives (e.g., algebraic "integral" vs. analytic integration). |

### Reports (2 files)

| File | Description |
|------|-------------|
| `crmlint_mathlib_report.txt` | CRM classification output from the crawler: 627 declarations, 10 Mathlib files, domain-level cross-tabulation. Key finding: 96.3% BISH. |
| `crmlint_structure_report.txt` | Three-axis profiling output: proof type distribution, tactic frequency histogram, Archimedean vs. non-Archimedean structural comparison. Key finding: Archimedean proofs are 1.7× longer, 2.8× deeper, have 4.3× more external dependencies, and 0.56× lower automation ratio. |

### Documents (2 .docx files)

| File | Description |
|------|-------------|
| `crmlint_roadmap.docx` | **CRMlint: From Forensics to Engineering.** Roadmap document for Paper 99. Three-stage architecture (obstruction detector → substitution engine → constrained proof search), seed substitution database, axiom interface problem, candidate targets for CRMlint-guided simplification. |
| `crmlint_report.docx` | **CRMlint: Proof Structure & Complexity Analysis.** Full report on the three-axis profiling methodology and results. 12 sections covering methodology, data, CRM distribution, proof types, tactic analysis, structural complexity, Archimedean thesis verification, anomalies, relationship to Paper 98, implications for Paper 99. |

---

## Usage

### Quick start: scan a single paper

```bash
python crmlint_scanner.py paper.tex
```

Output: CRM signature, bottleneck identification, section location, marker list.

### Scan an entire directory (e.g., arXiv dump)

```bash
python crmlint_scanner.py ./papers/ --compact
```

One-line-per-paper output sorted by CRM level descending. Papers at the top
are the most classical — the ones where Squeeze 2.0 has the most to offer.

### Export for downstream analysis

```bash
python crmlint_scanner.py ./papers/ --csv results.csv
python crmlint_scanner.py ./papers/ --json results.json
```

### Temporal drift (CRM levels across publication years)

```bash
python crmlint_scanner.py ./papers/ --temporal
```

Tests the Archimedean Obstruction Thesis diachronically: are subfields
becoming more constructive over time?

### Filter by CRM level (show only classical papers)

```bash
python crmlint_scanner.py ./papers/ --min-level WKL --compact
```

### Run the Mathlib crawler

```bash
python crmlint_crawler.py
```

Fetches 10 pre-configured Mathlib files from GitHub, classifies all
declarations, outputs aggregate report. Requires internet access.

### Run the structure analyzer (on crawler output)

```bash
python crmlint_structure.py
```

Runs the three-axis profiler on the same 10 Mathlib files. Outputs
proof type distribution, tactic histogram, complexity statistics,
and the Archimedean structural comparison.

### Use the core framework programmatically

```python
from crmlint import (
    CRMLevel, RealizationFunctor, ComparisonIsomorphism,
    ProofDAG, SUBSTITUTION_DATABASE
)

# Build a proof path
dag = ProofDAG()
dag.add_node("galois_def", level=CRMLevel.BISH, desc="Galois deformation ring")
dag.add_node("hecke", level=CRMLevel.BISH, desc="Hecke algebra")
dag.add_node("petersson", level=CRMLevel.CLASS, desc="Petersson inner product")
dag.add_edge("galois_def", "petersson")
dag.add_edge("hecke", "petersson")

# Compute signature
print(dag.signature())  # CLASS

# Find bottlenecks
bottlenecks = dag.bottlenecks()
# → [Node("petersson", CLASS)]

# Check substitution database
for sub in SUBSTITUTION_DATABASE:
    if sub.applies_to("petersson"):
        print(f"Substitution: {sub.classical} → {sub.constructive}")
        print(f"Reduction: {sub.cost_before} → {sub.cost_after}")
```

---

## Architecture: Three Generations

### Generation 1: Theoretical Framework (`crmlint.py`)
Paper 98 in code. Models the CRM hierarchy, six realization functors
(Betti, de Rham, étale, crystalline, Hodge, automorphic) with their
CRM costs, comparison isomorphisms, and the Archimedean Obstruction
Theorem. Proof DAGs compute signatures by max-propagation. The
substitution database stores known CRM-reducing alternatives.

**Validates Paper 98's claim:** σ(P) = max(σ(motive), max σ(Rᵢ), max σ(Cⱼ))

### Generation 2: Empirical Validation (`crmlint_crawler.py` + `crmlint_structure.py`)
Tests Paper 98's predictions against real Mathlib proofs. The crawler
fetches and classifies; the structure analyzer computes seven-dimensional
proof profiles. Together they confirm: algebraic = BISH, analytic = CLASS,
and Archimedean proofs are structurally heavier on every measured axis.

**Validates Paper 98's prediction:** non-Archimedean ⟹ BISH

### Generation 3: LaTeX Scanner (`crmlint_scanner.py`)
Squeeze 2.0 triage tool. Operates on .tex source, not Lean. Scans
thousands of papers in seconds using keyword + citation pattern matching.
Identifies classical bottlenecks without formalizing the proof. Designed
for the use case: "I want to know which of these 500 papers on arXiv
have excisable Archimedean content before I invest months on any one."

**Enables Paper 99:** automated bottleneck detection at scale

---

## Keyword Dictionary (crmlint_scanner.py)

The scanner's classification accuracy depends on ~80 keyword markers
and ~120 citation markers, curated from Papers 50–97. Key categories:

| CRM Level | Example Markers |
|-----------|----------------|
| CLASS | trace formula, Petersson inner product, analytic continuation, Hodge decomposition, ∂∂̄-lemma, elliptic regularity, Arakelov, period integral, Riemann existence, Chebotarev density, Euler system, Harish-Chandra, heat kernel |
| LPO | bounded monotone convergence, thermodynamic limit, least upper bound property |
| WLPO | decidability of real equality, intermediate value theorem, noncomputable def |
| WKL | Taylor-Wiles patching, inverse limit of finite objects, Bolzano-Weierstrass, sequential compactness, Tychonoff, König's lemma |
| BISH | (default) finite algebra, combinatorics, Galois cohomology, étale, Witt vectors, deformation rings, Hecke eigenvalues, Fontaine-Laffaille |

Anti-markers suppress false positives: "integral closure" (algebraic, not
analytic), "trace of matrix" (not trace formula), "spectral sequence"
(not spectral decomposition), "compact group" (not compactness argument).

---

## Substitution Database (crmlint.py)

Eight seed entries extracted from Papers 50–97:

| Classical Technique | Constructive Alternative | Reduction |
|---|---|---|
| Petersson inner product | Taylor–Wiles patching | CLASS → WKL |
| Hodge decomposition | Algebraic Hodge filtration | CLASS → BISH |
| Chebotarev density | Explicit Frobenius at finite primes | CLASS → BISH |
| Analytic continuation of L-functions | Algebraic special value formulas | CLASS → BISH |
| Spectral decomposition (trace formula) | Shtuka moduli (function fields) | CLASS → BISH |
| Arakelov height pairing | Néron–Tate via algebraic descent | CLASS → BISH |
| Hodge decomposition (generic) | Kani–Rosen splitting (special locus) | WLPO → BISH |
| RET (Riemann Existence Theorem) | Étale fundamental group (finite case) | CLASS → BISH |

---

## Known Limitations

1. **Heuristic classification.** The crawler and scanner use surface-syntax
   pattern matching, not semantic analysis of elaborated proof terms.
   False positives (algebraic "integral") and false negatives (WKL hidden
   behind API lemmas) are mitigated but not eliminated by anti-markers.

2. **No transitive dependency tracking.** The scanner classifies each paper
   independently. A paper that cites a CLASS result without naming the
   technique (e.g., "by [Wiles95, Theorem 3.1]") will be classified BISH
   unless the citation matches the lookup table. The citation dictionary
   covers ~120 landmark papers but not the full literature.

3. **LaTeX-only input.** The scanner operates on .tex source. Papers
   available only as PDF require tex extraction (e.g., via LaTeX-OCR
   or arXiv source download) before scanning.

4. **The WLPO/WKL boundary is subtle.** These levels are logically
   incomparable over BISH, and distinguishing them from surface syntax
   is unreliable. The scanner may misclassify at this boundary.

---

## Next Steps (Paper 99)

1. **Lean 4 metaprogram backend.** Replace heuristic classification with
   exact axiom tracing via Lean 4's `Environment.find?` and
   `Expr.foldConsts`. Zero false positives, zero false negatives for
   formalized proofs.

2. **arXiv bulk scan.** Point `crmlint_scanner.py` at the full arXiv
   number theory and algebraic geometry archives. Produce the first
   empirical CRM heatmap of published mathematics.

3. **Temporal validation.** Test whether condensed mathematics
   (Scholze–Clausen) shows decreasing CRM levels over time, as the
   Archimedean Obstruction Thesis predicts.

4. **New discovery.** Paper 99 must contain at least one genuinely new
   CRM-reducing substitution discovered by the pipeline, not just a
   rediscovery of known alternatives.

---

## Dependencies

- Python 3.8+
- No external packages (stdlib only)
- Internet access for `crmlint_crawler.py` (fetches from GitHub)
- .tex files for `crmlint_scanner.py`

---

## Licence

Part of the CRM Programme (Papers 50–98).
