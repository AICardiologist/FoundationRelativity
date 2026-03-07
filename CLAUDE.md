# Constructive Reverse Mathematics Series — Agent Instructions

## Identity
- **Author:** Paul Chun-Kit Lee (NYU, interventional cardiologist, Brooklyn)
- **Repo:** `AICardiologist/FoundationRelativity` on GitHub
- **Programme:** 100-paper CRM series (98 active, 2 withdrawn, 2 retired). ~99,000+ lines Lean 4.
- **Central finding:** The logical cost of mathematics is the logical cost of ℝ.

## Communication Style
- Substance over praise. Critically engage. Disagree when warranted.
- No lists unless requested. No follow-up questions at end of responses.
- Terse mathematical prose. Domain-separated: Medical | Math-Physics | Investment | Philosophy/Theology.

---

## Git Worktree Workflow (MANDATORY)

**Every agent MUST use git worktrees for parallel work.** Never work directly on `main`.

### Setup
```bash
# Create a worktree for your task (from the main repo root)
git worktree add ../worktrees/<task-name> -b <branch-name> main

# Example: working on Paper 69 editorial
git worktree add ../worktrees/p69-editorial -b edit/p69-editorial main

# Example: working on Paper 68 Lean recovery
git worktree add ../worktrees/p68-lean -b feat/p68-lean-recovery main
```

### Rules
1. **One worktree per task.** Each agent gets its own worktree and branch.
2. **Branch naming:** `feat/<paper>-<description>`, `edit/<paper>-<description>`, `fix/<description>`.
3. **Never modify `main` directly.** All changes go through branches → PR.
4. **Commit early, commit often.** Small atomic commits with clear messages.
5. **Write to coordinator file** after each meaningful milestone (see below).
6. **Clean up:** `git worktree remove ../worktrees/<task-name>` when done.

### Worktree Directory Structure
```
/Users/quantmann/
├── FoundationRelativity/          # Main repo (main branch)
├── worktrees/                     # All agent worktrees live here
│   ├── p69-editorial/
│   ├── p68-lean/
│   └── ...
```

---

## Coordinator File

**Path:** `/Users/quantmann/FoundationRelativity/.claude/coordinator.md`

Every agent writes status updates here so other agents (and Paul) know what's happening. Format:

```markdown
## [Branch Name] — [Agent ID or Task Name]
- **Status:** in-progress | blocked | done
- **Worktree:** ../worktrees/<name>
- **Last update:** YYYY-MM-DD HH:MM
- **What's done:** ...
- **What's next:** ...
- **Blockers:** ...
```

Read this file before starting work to avoid conflicts. Write to it after each milestone.

---

## Project Structure

### Lean 4 Bundles
- Pattern: `Papers/P{N}_{Name}/` with `lakefile.lean`, `Papers.lean`, `lean-toolchain`
- Toolchain: `leanprover/lean4:v4.29.0-rc2` (Papers 80–94); earlier papers use `v4.28.0-rc1`
- Each bundle is self-contained: `lake build` from bundle root
- Zero `sorry` policy — all proofs must be complete

### Paper Sources (LaTeX + PDF)
- Located in `paper {N}/` directories inside `~/FoundationRelativity/` (note: space in path — always quote)
- Each paper's Lean bundle lives inside its paper directory: `paper {N}/P{N}_{Name}/`
- **All paper directories must be in the main repo root** (`~/FoundationRelativity/`), not scattered elsewhere

### Master Documents
- `master folder/master_paper_list.txt` — complete paper list with DOIs
- `master folder/CRM_PROGRAMME_ROADMAP.md` — programme architecture and status
- `master folder/CRM_SESSION_HANDOFF.md` — session context for new agents
- `master folder/paper_format_guide.md` — LaTeX structure template
- `master folder/CRM_Series_Booklet.tex` — all 80 abstracts

### Logical Hierarchy
```
BISH ⊂ BISH+MP ⊂ BISH+LLPO ⊂ BISH+WLPO ⊂ BISH+LPO ⊂ CLASS
```
- FT (Fan Theorem): independent, physically dispensable
- DC (Dependent Choice): independent, physically dispensable
- Ceiling: BISH + LPO for all empirical physics

### Abbreviation Glossary (MANDATORY — agents get these wrong)
- **DPT** = Decidable Polarized Tannakian (NOT "Decidability of Pure Trace" or any other expansion). Source: Paper 50, §1.
- **GAGA** = Géométrie Algébrique et Géométrie Analytique (Serre 1956). Algebraic-analytic comparison.
- **AOT** = Archimedean Obstruction Thesis (Paper 98). CLASS enters through Betti realization only.
- **CBN** = Classical Boundary Node. The exact lemma where a proof invokes a non-constructive principle.
- **VHC** = Variational Hodge Conjecture. Spreading algebraicity from special to generic fibers.
- **LLC** = Local Langlands Correspondence. NOT "limited liability company."
- **LTE** = Liquid Tensor Experiment (Scholze's Lean formalization project).
- **FLT** = Fermat's Last Theorem. NOT "Fermat's Little Theorem."
- **CRM** = Constructive Reverse Mathematics. The programme's framework.
- **MT** = Mumford-Tate (group). NOT "machine translation" or "Montana."

---

## Paper Format (from paper_format_guide.md)
1. Title (include "Paper N, of Constructive Reverse Mathematics Series")
2. Abstract (summarize key finding)
3. Introduction (2–3pp): Theorems A/B/C, CRM primer, state of art, atlas fit
4. Preliminaries (1pp): Definitions, logical principles, no proofs
5. Main Results (5–10pp): Theorem-Proof format, flag axiom usage
6. CRM Audit (1pp): Classification, what descends from where to where
7. Formal Verification (2–3pp): Lean file, axiom inventory, `#print axioms`
8. Discussion (1pp): Connection to de-omniscientising descent
9. Conclusion (0.5pp): Honest, precise significance
10. Acknowledgments: AI disclosure, Mathlib citation
- References: 15–30 primary sources. Spell "program" US. Zenodo only (no GitHub).

---

## Current Status (2026-03-04)

### Complete — All 100 Papers Complete
- Papers 1–75: All written, compiled, Lean verified where applicable. 72 active DOIs.
- Papers 66–70: Editorial sweep complete.
- Papers 72–75: DPT axiom trilogy + conservation test. DOIs assigned.
- Paper 77: COMPLETE. Explicit Hodge decompositions for E⁴. 21 pages, 798 lines Lean. DOI: 10.5281/zenodo.18777596.
- Paper 78: COMPLETE. The Local Langlands Correspondence for GL₂(ℚ₂) Is Constructively Decidable. 19 pages, 395 lines Lean (0 sorry). Peer reviewed (2 rounds). DOI: 10.5281/zenodo.18789008.
- Paper 80: COMPLETE. Algebraic Gauss-Manin via Griffiths pole reduction over Q(t). 14 pages, 477 lines Lean (0 sorry). DOI: 10.5281/zenodo.18791985.
- Paper 76: COMPLETE. CRMLint automated CRM logical cost analyzer. 940 lines Lean, 0 sorry. DOI: 10.5281/zenodo.18779362.
- Paper 92: COMPLETE. Cohomological flatness for genera 5–8 via Zariski Grid Specialization. 15 pages, 333 lines Lean (0 sorry, 0 Classical.choice). DOI: 10.5281/zenodo.18816696.
- Paper 93: COMPLETE. Structural Vanishing Theorem — why τ₊ = 0 universally. Two proofs (Varchenko + Deligne). 13 BISH + 4 CLASS. 22 pages, 525 lines Lean (0 sorry). DOI: 10.5281/zenodo.18816989.
- Paper 94: COMPLETE. The Griffiths Group of the Mirror Quintic: A CRMLint Squeeze. Detection BISH, existence CLASS. 11 BISH + 3 CLASS. 15 pages, 566 lines Lean (0 sorry). DOI: 10.5281/zenodo.18820969.
- Paper 95: COMPLETE. The BSD Squeeze: CRMLint Decomposition of the Gross-Zagier-Kolyvagin Proof. Fourteenth CRMLint application. First CRM audit of a Clay Millennium Problem proof. 37a1 test case. 15 BISH + 6 CLASS = 21 components (71%). 796 lines Lean (58 theorems, 0 sorry). DOI: 10.5281/zenodo.18821019.
- Paper 96: COMPLETE. The Root Number Bifurcation: CRM Cost of BSD Detection Controlled by the Functional Equation. Fifteenth CRMLint application. BSD analogue of palindromic bifurcation (P89). 10 BISH + 3 CLASS = 13 components (77%). 16 pages, 1,033 lines Lean (86 theorems, 0 sorry). DOI: 10.5281/zenodo.18869924.
- Paper 97: COMPLETE. BSD Landscape Survey — Null Finding. Internal note. No new CRMLint opportunities beyond P95–96.
- Paper 98: COMPLETE. The Motivic CRM Architecture. Capstone synthesis of Papers 50–97. Archimedean Obstruction Thesis: CLASS enters through Betti realization only. Three calibration theorems. Companion monograph. 607 lines Lean (0 sorry). DOI: 10.5281/zenodo.18902037.
- Paper 99: COMPLETE (v2). The Hecke Theta Series Squeeze. Sixteenth CRMLint application. CRM(FLT) = WKL. Three CLASS→BISH excisions: Poisson→Mumford, Deligne-Serre→forward matching, Chebotarev→effective bounds. Validates Paper 98 empirically. DPT→motives→proof structure is predictive. 21 pages, 32 refs, 1,180 lines Lean (7 files, 0 sorry, 0 Classical.choice). DOI: 10.5281/zenodo.18821004.

### Clinical Sub-Series (Papers 103–105)
- Paper 103: COMPLETE. The Asymptotic Penumbra — first Clinical Sub-Series. DOI: 10.5281/zenodo.18880102.
- Paper 104: COMPLETE. The Algorithmic Penumbra — Clinical Sub-Series Paper B. DOI: 10.5281/zenodo.18889356.
- Paper 105: COMPLETE. The Dynamical Penumbra — Clinical Sub-Series Paper C. CRM of cardiac electrophysiology (FitzHugh-Nagumo). 5 BISH + 1 WLPO + 1 WKL + 1 LPO = 8 components (62.5% BISH). Widest CRM hierarchy span in Clinical Sub-Series. 15 pages, 3 TikZ figures, 27 refs, 1,246 lines Lean (9 files, 0 sorry, 0 Classical.choice). DOI pending.

### D-Modules / Higher Categories (Paper 106)
- Paper 106: COMPLETE. CRM Audit of the Riemann-Hilbert Correspondence. Eighteenth CRMLint application. First CRM audit of a categorical equivalence theorem. 10 BISH + 4 WLPO + 1 LPO + 1 CLASS = 16 components (62.5% constructive). Deligne canonical extension = LPO (floor function); GAGA descent = sole CLASS (Montel). ∞-categorical machinery (Lurie) is logically inert; Scholze condensed avoidance explained by CRM. 14–15 pages, 22 refs, 404 lines Lean (3 files, 0 sorry). DOI pending.

### Remaining Administrative
- Paper 105: DOI pending. Zenodo upload needed. Branch `feat/p105-dynamical-penumbra` ready for merge.
- Paper 106: DOI pending. Zenodo upload needed.
- `git push origin main` — multiple unpushed commits.
- Merge feature branches.

### Generative Phase (Papers 76–91)
- Paper 76: COMPLETE. CRMLint automated CRM logical cost analyzer. Full design in `CRM_PROGRAMME_ROADMAP.md` §7. DOI: 10.5281/zenodo.18779362.
- Paper 77: COMPLETE. Asymmetric offloading demonstrated (Python CAS → Lean verify).
- Paper 78: COMPLETE. The Local Langlands Correspondence for GL₂(ℚ₂) Is Constructively Decidable. Second CRMLint application (Langlands program). DOI: 10.5281/zenodo.18789008.
- Paper 79: COMPLETE. Standard Conjecture D for Abelian Fourfolds of Weil Type Is Constructively Decidable. Third CRMLint application. Generic Weil fourfold with K=ℚ(i), Gram matrix G=8I₂, positive definite by native_decide. CLASS → BISH descent.
- Paper 80: COMPLETE. Algebraic Gauss-Manin via Griffiths Pole Reduction: A CRMLint Squeeze. Third CRMLint application — upgrades from Q-arithmetic (native_decide) to Q(t)-algebra (ring). 15 pages, 523 lines Lean (0 sorry). DOI: 10.5281/zenodo.18791985.
- Paper 81: COMPLETE. The Fixed Part Theorem via Tensor Gauss-Manin: A CRMLint Squeeze. Fourth CRMLint application. Tensor Gauss-Manin connection on H¹⊗H¹ via Kronecker sum. 15 pages, 457 lines Lean (0 sorry). DOI: 10.5281/zenodo.18801814.
- Paper 82: COMPLETE. Picard-Fuchs Monodromy via Kovacic's Algorithm: A CRMLint Squeeze. Fifth CRMLint application. G_gal = SL₂ for Legendre Picard-Fuchs by rational function analysis. 15 pages, 457 lines Lean (0 sorry). DOI: 10.5281/zenodo.18801822.
- Paper 83: COMPLETE. Generic Picard Number of E_t × E_t: Resolving the Unbounded Degree Trap — A CRMLint Squeeze. Sixth CRMLint application. Capstone synthesis of P80–82: Künneth decomposition + flat section dim (P81) + Kovacic maximality (P82) → Picard rank = 3. 15 pages, 282 lines Lean (0 sorry, zero axioms). DOI: 10.5281/zenodo.18801826.
- Paper 84: COMPLETE (v3). Exotic Weil Classes as Flat Sections: Gauss-Manin Block Decomposition — A CRMLint Squeeze. Seventh CRMLint application. Genus-4 hyperelliptic family y²=x⁹-tx⁵+x with Q(i)-action, order-8 automorphism. G_gal(W_k) = SL₂ per block, det(SL₂) = 1 → G_gal(∧⁴V₊) = {1}. Positive result: exotic Weil class is a global flat section. 15 pages, 389 lines Lean (0 sorry, zero axioms). DOI: 10.5281/zenodo.18802819.
- Paper 85: COMPLETE (v3). Universal Trace Vanishing for Exotic Weil Classes: A CRMLint Squeeze. Eighth CRMLint application. V₊ is Lagrangian (eigenvalue argument: i²=-1≠1). Symplectic constraint gives tr(M₊)=-tr(M₋) but NOT tr(M₊)=0. τ₊=0 verified computationally for y²=x⁹+tx⁷+x. Multi-genus evidence (g=2,...,5, 8 families): τ₊=0 universally. v1 erratum: incorrectly claimed V₊ is symplectic. 15 pages, 296 lines Lean (0 sorry, propext+Quot.sound only on squeeze). DOI: 10.5281/zenodo.18806608. Internally reviewed 2026-02-28.
- Paper 86: COMPLETE (v2). The Hodge Conjecture for Exotic Weil Classes via Kani-Rosen Splitting: A CRMLint Squeeze. Ninth CRMLint application. Hidden reciprocal involution μ(x,y)=(1/x, y/x⁵) generates D₈ with σ. Kani-Rosen: J(C_t) ~ J(Q₁)×J(Q₂), Q₁≅Q₂ over ℂ, so J(C_t) ~ A². Generic End(A)=ℤ → MT(A)=GSp₄ (Zarhin) → all Hodge classes algebraic (Weyl). Lean (0 sorry, propext+Quot.sound only). DOI: 10.5281/zenodo.18809903. Internally reviewed 2026-02-28.
- Paper 87: COMPLETE. The Omniscience Cost of the Hodge Conjecture: A CRM Analysis. First CRM analysis of a Clay Millennium Problem. Uniform Hodge test requires WLPO; with CM metadata drops to BISH. 602 lines Lean (0 sorry). DOI: 10.5281/zenodo.18809903.
- Paper 88: COMPLETE (v2). Fermat Domination and the Variational Hodge Conjecture: A CRMLint Squeeze. Tenth CRMLint application. Non-palindromic obstruction blocks Kani-Rosen for y²=x⁹+tx⁷+x. CM specialization at t=0: Fermat domination F₁₆→C₀. Shioda + VHC → conditional algebraicity. CRMLint bifurcation: split → unconditional (P86), simple → conditional (P88). 15 pages, 411 lines Lean (0 sorry). DOI: 10.5281/zenodo.18809905. Internally reviewed 2026-02-28.
- Paper 89: COMPLETE. Absolute Hodge Classes for the Universal Hyperelliptic Weil Locus: A CRMLint Squeeze. Eleventh CRMLint application. Full 3-parameter universal family C_{a,b,c}: y²=x⁹+ax⁷+bx⁵+cx³+x. τ₊(a,b,c)=0 for all three parameter directions, verified as polynomial identities in Z[a,b,c] by ring. Palindromic locus {a=c} = Kani-Rosen locus. Natural endpoint of Griffiths + Fermat pipeline. 13 pages, 418 lines Lean (0 sorry). DOI: 10.5281/zenodo.18809909.
- Paper 90: COMPLETE. The Squeeze Is a Microscope: Automated Constructivization from CRMLint to the Hodge Horizon. Synthesis monograph covering generative phase (P76-89). Four theorems: (A) Squeeze Protocol, (B) Bifurcation of Weil Locus, (C) Hodge Horizon = WLPO, (D) Asymmetric Offloading. Three-part structure. 22 pages, 35 refs, no Lean bundle (synthesis paper). DOI: 10.5281/zenodo.18809911.
- Paper 91: COMPLETE. The Logical Cost of Unconditional Hodge: CRM Audit of Markman-Floccari-Fu Theorem. CRM audit of Markman arXiv:2502.03415. Theorems: (A) 4 BISH + 5 CLASS decomposition, (B) Squeeze 90% vs Markman 44% BISH, (C) VHC consistent a posteriori, (D) cycle class map irreducibly CLASS (20/0 impossible, 19/1 best). Explicit palindromic cycle via Kani-Rosen. 15 pages, 25 refs, 668 lines Lean (0 sorry, 0 Classical.choice). DOI: 10.5281/zenodo.18809917. Branch: feat/p91-markman-audit.
- Paper 92: COMPLETE. Cohomological Flatness for Genera 5-8 via Zariski Grid Specialization: A CRMLint Squeeze. Twelfth CRMLint application. Extends trace vanishing to genera 5–8 via Zariski Grid Specialization (integer fiber evaluation + `norm_num` + Schwartz–Zippel). Genus 5 by `ring`, genera 6–8 by grid. 15 pages, 333 lines Lean (98 theorems, 0 sorry, 0 Classical.choice). DOI: 10.5281/zenodo.18816696.
- Paper 93: COMPLETE (v2). The Structural Vanishing Theorem: Why Exotic Weil Classes Are Universally Flat. Explanatory capstone for P84–92. Two independent proofs: (1) hypergeometric (Varchenko exponent cancellation + Vieta freeze), (2) topological (Deligne regularity + Picard–Lefschetz). CRM decomposition: 13 BISH + 4 CLASS. Closes the structural proof open since P85. 22 pages, 525 lines Lean (0 sorry). DOI: 10.5281/zenodo.18816989. Internally reviewed 2026-02-28.
- Paper 94: COMPLETE. The Griffiths Group of the Mirror Quintic: A CRMLint Squeeze. Thirteenth CRMLint application. First CRM analysis of Calabi–Yau middle cohomology (mirror quintic). Detection (Walcher source term) BISH; existence (Abel–Jacobi, Baire) CLASS. Voisin decomposition: 11 BISH + 3 CLASS. 15 pages, 566 lines Lean (0 sorry). DOI: 10.5281/zenodo.18820969.
- Paper 95: COMPLETE. The BSD Squeeze: CRMLint Decomposition of the Gross-Zagier-Kolyvagin Proof. Fourteenth CRMLint application. First CRM audit of a Clay Millennium Problem proof. Elliptic curve 37a1 (rank 1, w=−1). Hecke arithmetic (28 sub-results, native_decide) BISH; Gross-Zagier/Kolyvagin CLASS. 15 BISH + 6 CLASS = 21 components (71%). Silverman height bounds by linarith. 796 lines Lean (58 theorems, 0 sorry). DOI: 10.5281/zenodo.18821019.
- Paper 96: COMPLETE. The Root Number Bifurcation: CRM Cost of BSD Detection Controlled by the Functional Equation. Fifteenth CRMLint application. BSD analogue of palindromic bifurcation (P89). Rank 0 test case: 11a1 (w=+1), detection BISH via modular symbols (L(E,1)/Ω⁺ = 1/5 by norm_num). 2-descent excision for 37a1 (rank bound BISH, Sha finiteness CLASS). Universal detection/existence table across P84–96. 10 BISH + 3 CLASS = 13 components (77%). 16 pages, 1,033 lines Lean (86 theorems, 0 sorry). DOI: 10.5281/zenodo.18869924.

### Capstone Phase (Papers 97–100)
- Paper 97: COMPLETE. BSD Landscape Survey — Null Finding. Internal note. No new CRMLint opportunities beyond P95–96.
- Paper 98: COMPLETE. The Motivic CRM Architecture: Why the Six Domains of Mathematics Have Different Logical Signatures. Capstone synthesis of Papers 50–97. Archimedean Obstruction Thesis (Theorem 5.1): CLASS enters arithmetic geometry through Betti realization only. Three calibration theorems: (I) Hodge bifurcates at WLPO, (II) BSD rank/Sha decouples, (III) TW patching = WKL. Companion monograph "The Logical Cost of Everything." 607 lines Lean (0 sorry, 0 Classical.choice). DOI: 10.5281/zenodo.18902037.
- Paper 99: COMPLETE (v2, referee-accepted). The Hecke Theta Series Squeeze: Resolving the Dihedral Base Case of Modularity via Mumford's Algebraic Theta Functions. Sixteenth CRMLint application. CRM(FLT) = WKL. Three CLASS→BISH excisions: Poisson→Mumford algebraic theta (de Rham), Deligne-Serre→forward formulaic matching (étale), Chebotarev→effective bounds (arithmetic). Validates Paper 98's Archimedean Obstruction Thesis. DPT→motives→proof structure is a predictive deductive chain. Ghost proof appendix (Lamé 1847). v1 had 3 fatal errors (referee); v2 corrects with 3-excision architecture. 21 pages, 32 refs, 1,180 lines Lean (7 files, 0 sorry, 0 Classical.choice). DOI: 10.5281/zenodo.18821004.
- Paper 100: COMPLETE (v4, internally reviewed). The Kuga-Satake Bifurcation: Absolute Hodge Classes on K3 Surfaces via Shioda-Inose Structure. Seventeenth CRMLint application. K3 Hodge campaign capstone. Kuga-Satake construction Cl⁺(T(X)) → A_KS. Bifurcation at ρ=20: CM structure → BISH detection; generic ρ → CLASS (Betti realization). 10 BISH + 5 CLASS = 15 components (67%). Conservation Conjecture as principal open problem. 16 pages, 26 refs, 729 lines Lean (5 files, 0 sorry, 0 Classical.choice). DOI: 10.5281/zenodo.18821010.

---

## Post-Completion Pipeline (after Lean + LaTeX draft)

After the Lean bundle builds and the LaTeX draft compiles, every paper goes through this pipeline before publication:

### Phase 1 — Format Compliance
1. **Format guide audit** — check against `master folder/paper_format_guide.md` (DOI: 10.5281/zenodo.18765700). When the format guide DOI is missing from a reference, ask the user.
2. Fix all deficiencies: section structure, reference count (15–30), page count (15–20), US spelling ("program"), Zenodo-only links.

### Phase 2 — Internal Peer Review
3. **Lean/CRM review** — zero sorry, axiom inventory complete with references, `#print axioms` output accurate, Classical.choice audit clean.
4. **Math review** — proofs correct, no logical gaps, claims match formal content, scope limitations stated.
5. **Product continuity** — consistent notation across series, parallel structure with companion papers maintained, no internal contradictions.

### Phase 3 — Edit + Figures
6. **Edit** based on review findings.
7. **Consider figures** — at least one TikZ figure for key conceptual content (trade-offs, descent diagrams, comparison tables). Ensure figures render correctly.
8. **Peer review with editor** — graphics OK, no factual errors, references resolve.

### Phase 4 — Package
9. **Recompile LaTeX/PDF** — clean build, no undefined references, no warnings.
10. **README.md** — summary, main results, Lean build instructions, axiom inventory, dependencies.
11. **metadata.txt** — no HTML, full useful description for Zenodo (title, author, affiliation, date, description, keywords, license, related identifiers, upload type).

### Phase 5 — Publish
12. **Zip package** — paper PDF + LaTeX source + Lean bundle (source only, no `.lake/`) + README + metadata.
13. **Upload to Zenodo** — use metadata.txt, assign DOI.
14. **PR to GitHub** — from feature branch to main.
15. **Update master folder** — `master_paper_list.txt` (add DOI), `CRM_Series_Booklet.tex` (add abstract), `CRM_PROGRAMME_ROADMAP.md` (update status), `CRM_SESSION_HANDOFF.md` (update context).
16. **Update CLAUDE.md** — move paper from "Future Papers" to "Complete", update paper count.

---

## Output Discipline (MANDATORY)

Chatbot agents have finite context windows. Token overflow kills sessions. Follow these rules:

### Minimize Printing
- **Never dump full file contents** unless explicitly asked. Summarize instead.
- **`lake build` output:** Print only errors. Suppress the "Building ..." and "Compiling ..." lines. Use `lake build 2>&1 | grep -E "error|sorry|warning"` or equivalent.
- **`#print axioms` output:** Print only the theorem name and its custom axioms. Omit `propext`, `Classical.choice`, `Quot.sound` — these are universal infrastructure.
- **LaTeX compilation:** Print only errors/warnings. Not the full log.
- **Python CAS output:** Print only the emitted Lean definitions. Not intermediate symbolic computation steps.
- **Git output:** `git status --short`. Not `git diff` of entire files.
- **File reads:** State what you found. Don't echo 200 lines back.

### When Computation Takes Too Long
If a Lean build, CAS computation, or tactic search exceeds **5 minutes wall-clock time**, STOP and:
1. Report what specifically is slow (e.g., "Mathlib import", "ring on degree-12 polynomial", "native_decide on 10⁶ cases").
2. **Ask the user whether to consult Math AI** (e.g., Gemini, GPT-o3) for an algorithmic shortcut — a smaller witness, a different tactic, a factorization that avoids intermediate expression swell.
3. Do NOT spin indefinitely. The user's context window is burning.

Common shortcuts Math AI can provide:
- Gröbner basis reduction before passing to `ring`
- Factored forms that avoid expression swell in `norm_num`
- Alternative proof strategies (e.g., `field_simp` before `ring`, or splitting a polynomial identity into smaller pieces)
- Explicit witnesses for existential goals (avoids `decide` on large search spaces)

---

## Python CAS Workflow

Several papers use **asymmetric offloading**: Python (SymPy/SageMath) computes exact algebra; Lean verifies the emitted identities via `ring`/`norm_num`/`native_decide`.

### Papers Using Python CAS
- Paper 77: `solve_hodge_e4.py` → Hodge decomposition data
- Paper 80: `solve_gauss_manin.py` → Griffiths pole reduction, PF operator coefficients
- Paper 84–89, 92: Various CAS scripts → trace vanishing identities, Zariski grid data
- Paper 94: CAS computation → Walcher recurrence coefficients
- Paper 95: `solve_bsd_37a1.py` → Hecke eigenvalues, Silverman constants
- Paper 96: `solve_11a1.py` → Point counts, modular symbol ratio, Tamagawa numbers for 11a1

### CAS Conventions
1. Python script lives in the paper directory: `paper N/solve_*.py`
2. Script emits a `.lean` file (or definitions to paste) with exact rational constants
3. Lean file imports the emitted data and verifies by `ring`/`norm_num`
4. **Never commit `.lake/` or CAS intermediate files** — source only
5. If CAS computation exceeds available memory or time, use Zariski Grid Specialization (Paper 92 pattern): evaluate at concrete integer points, verify by `norm_num`, invoke Schwartz-Zippel

---

## Lean 4 Conventions
- `_hN` prefix for unused hypotheses
- `field_simp; ring` for division/cast goals
- `fin_cases i <;> fin_cases j <;> simp [...]` for exhaustive matrix proofs
- `_root_.` prefix when local definitions shadow Mathlib lemmas
- ALL theorems over ℝ show `Classical.choice` in `#print axioms` — this is infrastructure, not classical content
- Constructive stratification: established by proof content (explicit witnesses vs principle-as-hypothesis), not axiom checker output
