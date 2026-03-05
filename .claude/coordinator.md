# Agent Coordinator — CRM Series

**Purpose:** Track parallel agent work across git worktrees. Every agent reads this before starting and writes updates after milestones.

**Rules:**
1. Read this file first — check for conflicts with your planned work.
2. Claim your task by adding an entry below before starting.
3. Update your entry after each meaningful milestone.
4. Mark `done` and note the branch/PR when finished.
5. Do not modify other agents' entries.

---

## Active Tasks

### edit/p101-revision — Paper 101: Full format-compliant revision
- **Status:** done (v5)
- **Worktree:** ../worktrees/p101-revision
- **Last update:** 2026-03-04 17:30
- **What's done:**
  - Math corrections: p^Q error, Weight-Monodromy attribution, scanner removal
  - Lean 4 bundle: 6 files, 831 lines, 0 sorry, 0 warnings
  - Full format guide compliance: Theorems A/B/C/D, Preliminaries, Main Results (Theorem-Proof), CRM Audit, Formal Verification (code snippets, axiom table, #print axioms, Classical.choice audit), Discussion, 25 refs
  - README.md and metadata.txt
  - 16 pages, 3 commits
- **What's next:** user reviews, merges to main
- **Blockers:** none
- **Branch:** edit/p101-revision

### feat/p99-hecke-theta — Paper 99: The Hecke Theta Series Squeeze
- **Status:** done
- **Worktree:** ../worktrees/p99-hecke
- **Last update:** 2026-03-03 12:00
- **What's done:**
  - Lean 4 bundle: 846 lines, 6 files, 45 theorems, 0 sorry, 0 Classical.choice
  - Theorem A: Algebraic Hecke theta via q-expansion principle (BISH)
  - Theorem B: Dihedral modularity is BISH (7 BISH + 0 CLASS)
  - Theorem C: CRM(FLT) = WKL (5-stage audit: 4 BISH + 1 WKL)
  - CRMLevel.lean: 7-level hierarchy with WKL, join/joinList, native_decide proofs
  - HeckeCharacter.lean: Gaussian integer model, r_χ(n), splitting types, Hecke=Galois by rfl
  - QExpansion.lean: Poisson→CLASS vs q-expansion→BISH, Eichler-Shimura/Sturm both BISH
  - DihedralModularity.lean: 7-component decomposition, excision structure, native_decide
  - FLTAudit.lean: 5-stage FLT, BaseRoute comparison (3 routes), flt_crm_optimal
  - Paper99_Assembly.lean: master theorems, #print axioms, axiom inventory
  - Axiom inventory: propext + Quot.sound (infrastructure only), no mathematical axioms on main path
  - paper99.tex: 15 pages, 25 references, 1 TikZ excision diagram, clean compile
  - README.md, metadata.txt complete
  - 1 commit on branch feat/p99-hecke-theta (ffe3b8d)
- **What's next:** user uploads Zenodo zip, assigns DOI, merges to main
- **Blockers:** none
- **Branch:** feat/p99-hecke-theta

### feat/p98-motivic-crm — Paper 98: The Motivic CRM Architecture
- **Status:** done
- **Worktree:** ../worktrees/p98-motivic-crm
- **Last update:** 2026-03-01 14:00
- **What's done:**
  - Lean 4 bundle: 607 lines, 6 files, 0 sorry, 0 warnings, 0 Classical.choice
  - Theorem A (Archimedean Obstruction): proved by helper lemmas + list induction
  - Calibration theorems: Hodge, BSD, TW excision (native_decide/decide)
  - Langlands signature preservation, function field constructivity
  - Physics documentary signatures
  - Axiom inventory: propext + Quot.sound (infrastructure only), no mathematical axioms
  - LaTeX: 16 pages, 25 references, all format guide sections present
  - Gemini editorial review integrated (7 improvements)
  - Physics calibrations section, Discussion section (de-omniscientising descent, open problems) added
  - README.md, metadata.txt complete
  - 2 commits on branch feat/p98-motivic-crm
- **What's next:** user uploads Zenodo zip, assigns DOI, merges to main
- **Blockers:** none
- **Branch:** feat/p98-motivic-crm

### edit/p86-review-fixes — Paper 86: Address external mathematical review
- **Status:** done
- **Worktree:** ../worktrees/p86-review
- **Last update:** 2026-02-28 23:00
- **What's done:**
  - Fixed fatal dimension-counting fallacy (Section 5): replaced End=Z/GSp_4/Weyl chain with Ribet (1983) — unconditional HC for powers of abelian surfaces
  - Fixed Weil fourfold MT group error (Section 9.6): End⊗Q ⊇ Q(i), MT ⊆ GU(2,2), not End=Z/GSp_8
  - Removed hallucinated discriminant values (Sections 5 and 9.5)
  - Fixed Kani-Rosen idempotent exponent: J(C_t/V_4)^2 not J(C_t/V_4)
  - Updated abstract, introduction, CRM audit (10 BISH + 3 CLASS), squeeze theorem, conclusion, bibliography
  - Added Ribet (1983) reference; removed unused Chai-Oort and Moonen17 references
  - Included honest erratum remark explaining the v1 dimensional error
  - Recompiled PDF: 15 pages, clean build, no errors
- **What's next:** user reviews changes, recompiles final PDF, updates Zenodo
- **Blockers:** none
- **Branch:** edit/p86-review-fixes

### feat/p93-structural-vanishing — Papers 93+94: Structural Vanishing + Normal Function Squeeze
- **Status:** done
- **Worktree:** ../worktrees/p93-structural-vanishing
- **Last update:** 2026-02-28 12:00
- **What's done:**
  - **Paper 93 (NEW):** The Structural Vanishing Theorem — why τ₊ = 0 universally
    - Two independent proofs: Varchenko exponent cancellation + Deligne/PL monodromy
    - CRM: 13 BISH + 4 CLASS. 15 pages, 525 lines Lean (0 sorry)
    - DOI: 10.5281/zenodo.18816697
    - Internal peer review: PASS. Format guide compliant, human-readable proofs, TikZ figure
  - **Paper 94 (renumbered from old P93):** The Normal Function Squeeze — CY3 Griffiths group
    - Detection BISH, existence CLASS. 11 BISH + 3 CLASS. 15 pages, 566 lines Lean (0 sorry)
    - DOI pending
  - Both Lean bundles build clean (Mathlib v4.29.0-rc2)
  - Both papers compiled, copied to ~/FoundationRelativity/
  - Committed on branch feat/p93-structural-vanishing
- **What's next:** user uploads Zenodo zips, assigns DOI for P94, merges to main
- **Blockers:** none
- **Branch:** feat/p93-structural-vanishing

### feat/p87-hodge-cost — Paper 87: The Omniscience Cost of the Hodge Condition
- **Status:** done
- **Worktree:** ../worktrees/p87-hodge-cost
- **Last update:** 2026-02-27 20:00
- **What's done:**
  - First CRM analysis of a Clay Millennium Problem
  - Lean 4 bundle: 602 lines, 6 files, 0 sorry, clean `lake build` (766 jobs)
  - Theorem A: CM/MT metadata → BISH (Shiga-Wolfart + Moonen-Zarhin)
  - Theorem B: Uniform Hodge test ↔ WLPO (embedding reduction)
  - Theorem C: Biconditional (cost = BISH ↔ algebraic metadata)
  - Theorem D: Shiga-Wolfart boundary (algebraic periods ↔ CM over Q̄)
  - Axiom inventory: propext, Classical.choice, Quot.sound (infrastructure) + 8 mathematical axioms
  - paper87.tex: 12 pages, 22 references, 1 TikZ figure, clean compile
  - README.md, metadata.txt complete
  - Committed on branch feat/p87-hodge-cost
- **What's next:** user uploads Zenodo zip, assigns DOI
- **Blockers:** none
- **Branch:** feat/p87-hodge-cost

### fix/p68-section-fixes — Paper 68 LaTeX fixes (two active failure modes)
- **Status:** done
- **Worktree:** ../worktrees/p68-fixes
- **Last update:** 2026-02-25 16:00
- **What's done:**
  - Failure 4 (§7.4): retracted false BISH claim for Kassaei–Pilloni classicality; rigid analytic geometry → Krull/BPI → CLASS
  - Completing the proof (§8.3): added Kronecker decidability note for absolutely-irreducible / reducible case-split on ρ̄_{E,2}
  - Committed on branch fix/p68-section-fixes, copied back to main repo
- **What's next:** user recompiles PDF, re-zips for Zenodo
- **Blockers:** none
- **Branch:** fix/p68-section-fixes

### feat/p76-crmlint — Paper 76 CRMLint: Automated CRM Logical Cost Analyzer
- **Status:** in-progress (LaTeX draft complete, Lean v0.2 done)
- **Worktree:** ../worktrees/p76-crmlint
- **Last update:** 2026-02-26 01:30
- **What's done:**
  - CRMLint v0.2: 940 lines Lean 4, zero sorry, builds clean against Mathlib (v4.29.0-rc2)
  - **v0.2 FIX:** Real.instField WLPO hallucination — type-aware root-context classifier
  - Layer 1: BFS dependency tracer (Trace.lean, 128 lines)
  - Layer 2: 12-rule priority classifier with root-context fallback (Classify.lean, 267 lines)
  - Infrastructure.lean: separates BISH discrete from WLPO analytic, Quotient.out → CLASS
  - Batch scanner: `#crm_scan` command for namespace-level atlas
  - Five-point calibration: all correct (Nat.add_comm→BISH, Int.add_comm→BISH, zorn_le→CLASS, add_comm→BISH, Real.instField→WLPO)
  - Namespace scans: Nat (70% BISH), ZMod (51% BISH, 2% WLPO), Real (21% WLPO, 77% CLASS)
  - Paper 76 LaTeX: 11 pages, compiles clean, TikZ architecture figure
- **What's next:**
  - Format guide compliance check
  - StatementClassifier layer (automate statement costing)
  - Zenodo packaging
- **Blockers:** none
- **Branch:** feat/p76-crmlint

### feat/p73-axiom1 — Paper 73 Axiom 1 Reverse Characterisation
- **Status:** done
- **Worktree:** ../worktrees/p73-axiom1
- **Last update:** 2026-02-24 23:45
- **What's done:**
  - Lean 4 bundle: 6 files (~250 lines), zero sorry, 4 axioms (2 data + 2 prop, all referenced)
  - `lake build` passes (81 jobs, 0 errors, 0 warnings)
  - Theorem A (forward: Conj D → BISH), Theorem B (biconditional), Theorem C (characterisation)
  - Jannsen obstruction + escape (numerical motives: BISH but unfaithful)
  - Sharpened Axiom 1 Principle (biconditional)
  - LaTeX paper: paper73.tex (~500 lines, 10 pages) with CRM audit and descent table
  - MotivicCategory structure with realization_compatible flag
- **Branch:** feat/p73-axiom1

### feat/p78-wild-langlands — Paper 78: LLC for GL₂(ℚ₂) Is Constructively Decidable
- **Status:** done
- **Worktree:** ../worktrees/p78-wild-langlands
- **Last update:** 2026-02-26 04:00
- **What's done:**
  - Python CAS: `solve_wild_langlands.py` (280 lines) — explicit BK type computation for E = ℚ₂(i), conductor-2 character θ, 16 test elements, Frobenius eigenvalues α₁ = 1, α₂ = -1
  - Lean 4 bundle: 354 lines (0 sorry, 0 axioms on constructive path), `lake build` clean (3121 jobs)
  - `WildLanglandsData.lean` (192 lines): CAS-emitted, 8 decidable theorems by `decide`
  - `Paper78_WildLanglands.lean` (162 lines): CRM hierarchy, BK types, Harris-Taylor axiom (CLASS, unused), combined Squeeze theorem, CRM audit
  - Axiom inventory: `#print axioms wild_llc_squeeze` → propext, Classical.choice, Quot.sound (no harris_taylor_existence)
  - `#print axioms character_trace_matching` → (none) — pure kernel computation
  - paper78.tex: 16 pages, 24 references, 2 TikZ figures, full 16-element table
  - README.md, metadata.txt complete
- **What's next:** user uploads Zenodo zip, assigns DOI
- **Blockers:** none
- **Branch:** feat/p78-wild-langlands

### feat/p80-gauss-manin — Paper 80: Algebraic Gauss-Manin over Function Fields
- **Status:** in-progress (Lean build CLEAN, LaTeX pending)
- **Worktree:** ../worktrees/p80-gauss-manin
- **Last update:** 2026-02-26 14:30
- **What's done:**
  - `solve_gauss_manin.py`: SymPy Griffiths pole reduction for Legendre family y²=x(x-1)(x-t)
  - `GMData.lean`: 14 polynomial identities (ring/norm_num), PF coefficients, connection matrix, Griffiths division, hypergeometric closed form aₙ = C(2n,n)²/4^(2n)
  - `Paper80_GaussManin.lean`: CRM architecture, CLASS boundary (Ehresmann), BISH Squeeze, tactic upgrade demo, CRM audit (7 BISH, 3 CLASS unused)
  - `lake build` CLEAN: 8036 jobs, 0 errors, 0 warnings
  - Axiom inventory: `gauss_manin_squeeze` → propext, Classical.choice, Quot.sound (no ehresmann)
  - Two commits on branch feat/p80-gauss-manin
- **What's next:**
  - LaTeX draft (paper80.tex)
  - Post-completion pipeline (format guide, peer review, figures)
- **Blockers:** none
- **Branch:** feat/p80-gauss-manin

### feat/p79-conjD — Paper 79: Std Conj D for Weil Fourfolds Is Constructively Decidable
- **Status:** in-progress (Lean build running, Python computation COMPLETE)
- **Worktree:** N/A (working in main repo `paper 79/`)
- **Last update:** 2026-02-26 12:15
- **What's done:**
  - **Mathematical pivot:** Q(zeta_15) sweep confirmed exotic dim = 0 for all 16 CM types (Hazama-Ribet obstruction: cyclotomic deg ≤ 8 cannot host exotic classes). Pivoted to Generic Weil Fourfold with K = Q(i).
  - `solve_generic_weil.py`: Weil class w = v1∧v2∧v3∧v4, v_k = e_k - I·f_k. Gram matrix G = diag(8,8). Positive definite. Computed in <1s.
  - `ConjDData.lean`: emitted with G11=8, G12=0, G22=8, native_decide proofs.
  - `Paper79_ConjD.lean`: full CRM architecture — CLASS boundary node (abstract Lefschetz), BISH bridge (Sylvester on 2×2 integer matrix), CRM audit table, axiom inventory.
  - `paper79.tex`: LaTeX scaffold (10 sections stubbed, needs filling with Weil narrative).
  - Also present: `solve_conjD.py` (dual eigenvector algorithm, correct but target has no exotics), `sweep_cm_types.py` (precomputed all 70 wedge-4 dual vectors).
- **What's next:**
  - `lake build` (running now — Mathlib fetch + compile)
  - Fill LaTeX sections with Generic Weil narrative
  - Post-completion pipeline (format compliance, peer review, figures)
- **Blockers:** lake build time (~30-60 min)
- **Branch:** (to be created: feat/p79-conjD)

### feat/p81-flat-sections — Paper 81: Algebraic Flat Sections / Fixed Part
- **Status:** done
- **Worktree:** N/A (working in main repo `paper 81/`)
- **Last update:** 2026-02-27 02:00
- **What's done:**
  - `solve_flat_sections.py`: SymPy Kronecker sum, flat section verification, kernel computation
  - `FlatData.lean` (263 lines): CAS-emitted 16 tensor entries, 25 identities (ring/rfl/decide/linarith)
  - `Paper81_FlatSections.lean` (194 lines): CRM architecture, squeeze theorem, CRM audit
  - `lake build` CLEAN: 8037 jobs, 0 errors, 0 sorry
  - Axiom inventory: `flat_sections_squeeze` → propext, Classical.choice, Quot.sound (no deligne_fixed_part_existence)
  - paper81.tex: 15 pages, 20 references, 1 TikZ figure, comparison table (Papers 77-81)
  - paper81.pdf: clean compile, no undefined references
  - Format compliance audit: PASS (all criteria met)
  - Peer review: PASS (Lean/CRM 7/7, Math 10/10, Product continuity conditional on DOI)
  - README.md, metadata.txt complete
  - CLAUDE.md, CRM_PROGRAMME_ROADMAP.md, CRM_SESSION_HANDOFF.md updated
- **What's next:** user uploads Zenodo zip, assigns DOI, fills DOI placeholder in paper81.tex line 39
- **Blockers:** none
- **Branch:** main (direct)

### feat/p82-diff-galois — Paper 82: Constructive Differential Galois Theory (Kovacic)
- **Status:** done
- **Worktree:** N/A (working in main repo `paper 82/`)
- **Last update:** 2026-02-27 05:00
- **What's done:**
  - `solve_kovacic.py` (200 lines): SymPy normal form, pole analysis, Kovacic 3-case checking, emits KovacicData.lean
  - `KovacicData.lean` (257 lines): CAS-emitted, ring/norm_num/omega/linarith proofs
  - `Paper82_DiffGalois.lean` (199 lines): CRM architecture, squeeze theorem, CRM audit
  - `lake build` CLEAN: 8039 jobs, 0 errors, 0 sorry, 0 warnings
  - Axiom inventory: `diff_galois_is_SL2_squeeze` → propext, Classical.choice, Quot.sound (no topological_monodromy_dense)
  - paper82.tex: 15 pages, 20 references, 1 TikZ figure
  - paper82.pdf: clean compile, no undefined references
  - Format compliance audit: PASS (all 15 criteria)
  - Peer review: PASS (Lean/CRM clean, math correct after Case 3 fix, product continuity OK)
  - README.md, metadata.txt complete
  - CLAUDE.md, CRM_PROGRAMME_ROADMAP.md, CRM_SESSION_HANDOFF.md updated
- **What's next:** user uploads Zenodo zip, assigns DOI
- **Blockers:** none
- **Branch:** main (direct)

### feat/p83-generic-picard — Paper 83: Generic Picard Number of Legendre Surface Family
- **Status:** done
- **Worktree:** N/A (working in main repo `paper 83/`)
- **Last update:** 2026-02-27 08:00
- **What's done:**
  - `Paper83_GenericPicard.lean` (282 lines, 0 sorry, 0 axioms in squeeze theorem)
  - `lake build` CLEAN: 3120 jobs, 0 errors, 0 warnings
  - Axiom inventory: `generic_picard_squeeze` → **(none)** — cleanest in entire series
  - `paper83.tex`: 15 pages, 21 references, 1 TikZ figure, clean compile
  - Format compliance audit: PASS (15/15 criteria)
  - Peer review: PASS (all 3 reviews, fixes applied)
  - README.md, metadata.txt complete
  - Author info updated: Paul Chun-Kit Lee, New York University, Brooklyn, New York
- **What's next:** user uploads Zenodo zip, assigns DOI
- **Blockers:** none
- **Branch:** main (direct)

### feat/p84-exotic-trace — Paper 84: The Exotic Trace Probe
- **Status:** done
- **Worktree:** N/A (working in main repo `paper 84/`)
- **Last update:** 2026-02-27 12:00
- **What's done:**
  - `solve_exotic_trace.py`: SymPy Griffiths-Bezout reduction for genus-4 curve y^2 = x^9 - tx^5 + x
  - `TraceData.lean` (51 lines): CAS-emitted trace coefficients, V_+ matrix entries
  - `Paper84_ExoticTrace.lean` (338 lines): CRM architecture, 15-conjunct squeeze theorem, CRM audit
  - `lake build` CLEAN: 3121 jobs, 0 errors, 0 sorry
  - Axiom inventory: `exotic_trace_squeeze` → **(none)** — zero axiom dependence
  - paper84.tex: 15 pages, 18 references, 1 TikZ figure (pipeline), 3 tables
  - Format compliance: PASS (15/15)
  - Peer review: PASS (monodromy sign fix applied, all math verified)
  - README.md, metadata.txt complete
  - DOI: 10.5281/zenodo.18802819
- **What's next:** user uploads Zenodo zip
- **Blockers:** none
- **Branch:** main (direct)

---

## Completed Tasks

### feat/p77-dagsurgery — Paper 77: Explicit Hodge Decompositions for E⁴
- **Status:** done
- **Worktree:** N/A (created directly in main repo)
- **Last update:** 2026-02-26
- **What's done:**
  - paper77.tex: 21 pages, 24 references, honest framing (methods paper, not mathematical breakthrough)
  - P77_DAGSurgery/ Lean bundle: 798 lines (sparse), 0 sorry, 0 warnings, 3121 build jobs
  - Asymmetric offloading: Python CAS computes → Lean kernel verifies via native_decide
  - 36 explicit Hodge (2,2) decompositions, 0 exotic Weil classes confirmed
  - Four peer reviews (2 rounds), all fixes applied
  - Zenodo zip built: `Paper77_ExplicitHodgeE4.zip` (458 KB, 16 files) on Desktop
  - DOI assigned: 10.5281/zenodo.18779210
  - README.md, metadata.txt, master_paper_list.txt updated
  - Roadmap, session handoff, coordinator updated
- **What's next:** user uploads Zenodo zip
- **Blockers:** none
- **Branch:** main (direct)

### feat/p72-characterisation — Paper 72 DPT Characterisation
- **Status:** done
- **Worktree:** ../worktrees/p72-characterisation
- **Last update:** 2026-02-24 23:00
- **What's done:**
  - Lean 4 bundle: 5 files (~350 lines), zero sorry, 8 axioms (all referenced)
  - `lake build` passes (81 jobs, 0 errors, 0 warnings)
  - Theorems A (minimality), B (height-search equivalence), C (characterisation)
  - Sharpened Archimedean Principle (biconditional)
  - LaTeX paper: paper72.tex (~500 lines) with low-rank counterexample remark
  - v3 fixes: deleted P_α language, axiomatised costs (Paper 69 pattern),
    ℤ-density strengthening, SL₂ acknowledgment, scope limitation preserved
- **Branch:** feat/p72-characterisation

---

## Outstanding Work Queue

These items need agents assigned:

### feat/p91-markman-audit — Paper 91: The Logical Cost of Unconditional Hodge
- **Status:** done
- **Worktree:** ../worktrees/p91-markman-audit
- **Last update:** 2026-02-27 21:10
- **What's done:**
  - `palindromic_cycle.py` (280 lines): SymPy CAS extending P86 Kani-Rosen to 2-parameter palindromic family
  - `CycleData.lean` (177 lines): CAS-emitted polynomial identities, all `by ring`/`by decide`
  - `MarkmanAudit.lean` (226 lines): Theorems A-C, 5 CLASS + 4 BISH nodes, documentary axioms
  - `CycleClassMap.lean` (101 lines): Theorem D, 20/0 impossibility, Hodge Horizon irreducibility
  - `CRMLevel.lean` (61 lines): CRM hierarchy (reused from P87)
  - `Paper91_MarkmanAudit.lean` (103 lines): main file, imports, axiom inventory
  - `lake build` CLEAN: 3124 jobs, 0 errors, 0 sorry (668 total Lean lines)
  - Axiom inventory: propext + Quot.sound (infrastructure), 5 documentary axioms, NO Classical.choice in proofs
  - `paper91.tex` (1269 lines): 15 pages, 25 references, 1 TikZ figure, 2 tables
  - Format guide audit: PASS (15 pages, US spelling, Zenodo-only, section structure OK)
  - Peer review: PASS (Theorem C logic fixed, year corrections, format expansion)
  - README.md, metadata.txt complete
  - Zenodo zip: `Paper91_MarkmanAudit.zip` (353 KB, 14 files) on Desktop
  - 2 commits on branch feat/p91-markman-audit
- **What's next:** user uploads Zenodo zip, assigns DOI, merges branch to main
- **Blockers:** none
- **Branch:** feat/p91-markman-audit

### Priority 1 — Editorial
- [ ] **Paper 69 editorial revision** — 8 edit items, CRITICAL: expand Remark 3.3 (algebraic-vs-transcendental boundary)
- [ ] **Paper 70 editorial revision** — Brouwer inoculation sentence, trim Discussion §8, two TikZ figures

### Priority 2 — Remaining Papers
- [ ] **Paper 66** — 5 fixes needed (form-class resolution for non-cyclic totally real cubics)
- [ ] **Paper 67** — 3 blanks to fill (synthesis monograph Papers 45–66)
- [ ] **Paper 63** — pending DOI (Intermediate Jacobian Obstruction)

### Priority 3 — Infrastructure
- [ ] **Paper 71 Lean bundle** — verify/create `Papers/P71_Archimedean/` if not present
- [ ] **Zenodo DOI audit** — verify all 66 DOIs resolve correctly
