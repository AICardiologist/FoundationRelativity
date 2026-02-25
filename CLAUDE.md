# Constructive Reverse Mathematics Series — Agent Instructions

## Identity
- **Author:** Paul Chun-Kit Lee (NYU, interventional cardiologist, Brooklyn)
- **Repo:** `AICardiologist/FoundationRelativity` on GitHub
- **Programme:** 75-paper CRM series (73 active, 2 withdrawn, 2 retired). ~89,150+ lines Lean 4.
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
- Toolchain: `leanprover/lean4:v4.28.0-rc1`
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
- `master folder/CRM_Series_Booklet.tex` — all 69 abstracts

### Logical Hierarchy
```
BISH ⊂ BISH+MP ⊂ BISH+LLPO ⊂ BISH+WLPO ⊂ BISH+LPO ⊂ CLASS
```
- FT (Fan Theorem): independent, physically dispensable
- DC (Dependent Choice): independent, physically dispensable
- Ceiling: BISH + LPO for all empirical physics

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

## Current Status (2026-02-25)

### Complete — Programme Closed
- Papers 1–75: All written, compiled, Lean verified where applicable. 71 active DOIs, 0 pending.
- Papers 66–70: Editorial sweep complete (acknowledgments, format-guide, Paper 67 synthesis revision covering Papers 45–75).
- Papers 72–75: DOIs assigned (72: 18765393, 73: 18765700, 74: 18773827, 75: 18773831).
- Zenodo zips built for Papers 66–70 and 72–75. Awaiting user upload.

### Remaining Administrative
- Zenodo uploads: 5 new versions (Papers 66–70) + 4 first uploads (Papers 72–75). User must do manually.
- `git push origin main` — multiple unpushed commits.
- Format guide DOI: still "(DOI pending)" in Papers 72–75 metadata.

### Future Direction: CRMLint
- Automated logical cost analyzer for Mathlib (~150k declarations).
- Four layers: dependency tracer → pattern classifier → concentration analysis → AI audit.
- Full design in `CRM_PROGRAMME_ROADMAP.md` §7.
- The 75-paper programme serves as calibration dataset (14 Lean bundles = ground truth).
- Goal: proof technique atlas — classify techniques as scaffolding vs structural, predict conservation gaps, discover patterns invisible at manual scale.

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

## Lean 4 Conventions
- `_hN` prefix for unused hypotheses
- `field_simp; ring` for division/cast goals
- `fin_cases i <;> fin_cases j <;> simp [...]` for exhaustive matrix proofs
- `_root_.` prefix when local definitions shadow Mathlib lemmas
- ALL theorems over ℝ show `Classical.choice` in `#print axioms` — this is infrastructure, not classical content
- Constructive stratification: established by proof content (explicit witnesses vs principle-as-hypothesis), not axiom checker output
