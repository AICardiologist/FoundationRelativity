# WORK ORDER: CRMlint Scanner Tasks for Paper 101
## "The CRM Signature of Berkovich Motives"

**Date:** March 3, 2026  
**Priority:** Required before Paper 101 submission  
**Deliverables:** Scanner output files + supplementary appendix for Paper 101

---

## TASK 1: Obtain LaTeX Sources

**What:** Download the .tex sources for both Scholze papers from arXiv.

| Paper | arXiv ID | Version |
|-------|----------|---------|
| Berkovich Motives | 2412.03382 | v3 (Jan 22, 2026) |
| Geometrization of Local Langlands, Motivically | 2501.07944 | v1 (Jan 23, 2026) |

**How:** arXiv provides LaTeX source downloads for both papers. Download the .tar.gz source bundles. Extract the main .tex files.

**Output:** `scholze_berkovich.tex`, `scholze_motivic_geom.tex` placed in working directory.

**Note:** If source is unavailable (some authors opt out), use `arxiv_vanity` HTML or extract text from PDF via `pdftotext -layout`. Scanner works on raw text; LaTeX markup is preferred but not required.

---

## TASK 2: Run CRMlint Scanner on Both Papers

**What:** Execute `crmlint_scanner.py` on both tex files.

**Command:**
```bash
python crmlint_scanner.py scholze_berkovich.tex --output berkovich_scan.json --csv berkovich_scan.csv
python crmlint_scanner.py scholze_motivic_geom.tex --output motivic_geom_scan.json --csv motivic_geom_scan.csv
```

**Expected output per file:**
- Per-section bottleneck map (section → list of CRM markers with line numbers)
- Aggregate CRM heatmap (keyword frequency by CRM level)
- Flagged locations with CLASS/WLPO/WKL markers and surrounding context

**Expected behavior (based on architectural audit):**
- CLASS markers in introduction/motivation sections (trace formula, ι comparison, period integrals — all describing the *classical* approach being replaced)
- WLPO/CLASS alerts in foundational Banach ring sections (norm, real-valued, continuous valuation, complete, spectrum) — these are the *parasitic* alerts the referee wants documented
- WKL markers throughout proof sections (inverse limit, profinite, perfectoid, completion, projective limit)
- BISH markers for algebraic constructions (correspondence, algebraic cycle, weight structure, Hecke, deformation ring, Witt vector, Fontaine-Laffaille)

---

## TASK 3: Classify Scanner Alerts into Three Categories

**What:** Manually review each scanner alert and classify it.

**Categories:**

| Category | Description | Example |
|----------|-------------|---------|
| **A: Motivational CLASS** | CLASS keyword appears in discussion of classical approach being replaced, not in the proof | "the trace formula requires L² spectral decomposition" in introduction |
| **B: Parasitic WLPO** | Real-analytic terminology triggered by Banach ring formalism, not structurally essential | "Banach ring with norm valued in ℝ≥0" in §2-3 of Berkovich paper |
| **C: Structural WKL** | Genuine inverse limit / profinite construction in the proof | "inverse limit of perfectoid algebras" in proof of cancellation theorem |

**Output:** Classified alert table as `scanner_classification.csv` with columns: `file, line, keyword, context, category (A/B/C), CRM_level, section_type (proof/motivation/definition)`

**This classification is the core evidence for Paper 101 Section 9.** The referee specifically requested:
- Category B alerts documented as evidence that the scanner *correctly detected* the surface anomaly
- Narrative that Category B alerts prompted the human architectural analysis of Audit 3.1
- Category A alerts shown to be confined to motivational sections
- Category C alerts shown to be the structural WKL content

---

## TASK 4: Produce Summary Statistics

**What:** Aggregate the classified alerts into tables for the paper.

**Table 1: Alert Distribution by Category**
```
Category | Berkovich Motives | Motivic Geometrization | Total
---------|-------------------|------------------------|------
A (Motivational CLASS) | ? | ? | ?
B (Parasitic WLPO)     | ? | ? | ?
C (Structural WKL)     | ? | ? | ?
```

**Table 2: Alert Distribution by Section Type**
```
Section Type | CLASS alerts | WLPO alerts | WKL alerts | BISH alerts
-------------|-------------|-------------|------------|------------
Introduction/Motivation | ? | ? | ? | ?
Definitions/Foundations | ? | ? | ? | ?
Proof sections          | ? | ? | ? | ?
```

**Key claim to verify:** Zero Category A (CLASS) alerts in proof sections. All CLASS markers confined to motivation. This is the scanner's contribution to the WKL verdict.

---

## TASK 5: Produce Supplementary Appendix

**What:** Format the scanner output as a supplementary file for Paper 101.

**Format:** LaTeX appendix (`paper101_appendix_scanner.tex`) containing:

1. Brief description of scanner methodology (keyword dictionary size, citation pattern count, anti-marker system)
2. Table 1 and Table 2 from Task 4
3. Full classified alert list for both papers (abbreviated context, 5-10 words around each keyword)
4. Reproduction instructions: exact commands to re-run the scanner

**Length:** 3-5 pages. This is evidence, not narrative.

---

## TASK 6: Scanner Dictionary Update (if needed)

**What:** Check whether the scanner's keyword dictionary needs new entries for Berkovich-specific terminology.

**Terms to check are in the dictionary:**
- Banach ring, norm, valuation, complete → should map to WLPO or CLASS
- Perfectoid, inverse limit, profinite, projective limit → should map to WKL
- Arc-topology, ball-invariant, condensed → check if present; add if missing
- Berkovich spectrum, adic space, spectral space → check if present; add if missing
- Motivic sheaf, 6-functor, Tate twist → should map to BISH

**Terms to check for anti-markers:**
- "spectrum" in "spectral action" or "Bernstein center" context → should NOT trigger CLASS (this is algebraic Spec, not L² spectral)
- "complete" in "complete Banach ring" context → should trigger WKL (profinite completion), not CLASS (metric completeness of ℝ)

**If updates needed:** Edit `crmlint_scanner.py` keyword dictionary, document changes, re-run Tasks 2-5.

---

## TASK 7: Cross-Validation Against Audit

**What:** Verify that the scanner output is consistent with the architectural audit (Paper 101, Section 3).

**Checklist:**

- [ ] Scanner finds no CLASS markers in geometric Satake sections (confirms Audit 3.3: BISH)
- [ ] Scanner finds WKL markers in Fargues-Fontaine / perfectoid sections (confirms Audit 3.4: WKL)
- [ ] Scanner finds no L²/harmonic analysis/Plancherel markers in spectral action sections (confirms Audit 3.5: BISH, "spectral" is algebraic Spec not L² spectral)
- [ ] Scanner finds WLPO markers in Banach ring foundation sections (confirms Audit 3.1: parasitic WLPO)
- [ ] Scanner finds CLASS markers only in intro/motivation (confirms Audit 3.7: no Archimedean input in proof)

**If any check fails:** Investigate the discrepancy. Either the scanner has a false positive/negative (update dictionary), or the architectural audit missed something (update Paper 101).

---

## DELIVERABLES SUMMARY

| # | File | Description | Status |
|---|------|-------------|--------|
| 1 | `scholze_berkovich.tex` | Source file | To obtain |
| 2 | `scholze_motivic_geom.tex` | Source file | To obtain |
| 3 | `berkovich_scan.json` | Raw scanner output | To generate |
| 4 | `motivic_geom_scan.json` | Raw scanner output | To generate |
| 5 | `scanner_classification.csv` | Classified alerts | To produce |
| 6 | `paper101_appendix_scanner.tex` | Supplementary appendix | To write |
| 7 | Updated `crmlint_scanner.py` | Dictionary updates if needed | If needed |

**Timeline:** All tasks completable in one working session once tex sources are obtained.

**Dependencies:** Paper 101 Section 9 references this scanner output. The appendix must exist before submission.
