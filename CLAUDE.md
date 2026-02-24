# Constructive Reverse Mathematics Series — Agent Instructions

## Identity
- **Author:** Paul Chun-Kit Lee (NYU, interventional cardiologist, Brooklyn)
- **Repo:** `AICardiologist/FoundationRelativity` on GitHub
- **Programme:** 70-paper CRM series (69 active, 2 withdrawn, 2 retired). ~88,000 lines Lean 4.
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
- Located in `paper {N}/` directories (note: space in path — always quote)
- Also `Papers/P{N}_{Name}/` for formalized bundles

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

## Current Status (2026-02-24)

### Complete
- Papers 1–65, 68–71: Published with DOIs

### Needs Work
- **Paper 66:** 5 fixes needed (form-class resolution)
- **Paper 67:** 3 blanks to fill (synthesis monograph)
- **Paper 69 editorial:** 8 edit items (CRITICAL: expand Remark 3.3 on algebraic-vs-transcendental boundary)
- **Paper 70 editorial:** Brouwer inoculation, trim Discussion, two TikZ figures
- **Paper 68 Lean:** `Paper68_Final.lean` must be regenerated from `PAPER68_LEAN_WORK_ORDER.md`

---

## Lean 4 Conventions
- `_hN` prefix for unused hypotheses
- `field_simp; ring` for division/cast goals
- `fin_cases i <;> fin_cases j <;> simp [...]` for exhaustive matrix proofs
- `_root_.` prefix when local definitions shadow Mathlib lemmas
- ALL theorems over ℝ show `Classical.choice` in `#print axioms` — this is infrastructure, not classical content
- Constructive stratification: established by proof content (explicit witnesses vs principle-as-hypothesis), not axiom checker output
