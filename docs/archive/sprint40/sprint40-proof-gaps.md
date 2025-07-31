# Sprint 40: Sorry Analysis and Resolution Plan

## Overview

During Sprint 40 implementation (Foundation 2-category skeleton), we discovered several pre-existing proof gaps from the main branch that were exposed during the SpectralGap → AnalyticPathologies namespace migration.

## Impact Analysis

| File | Count | Kind of gap | Impact today | When it must be closed |
|------|-------|-------------|--------------|------------------------|
| CategoryTheory/Found.lean | 3 | Infrastructure – coherence proofs for identity/composition of 2-cells | None for compiling & importing; these lemmas are never used yet | Sprint 41 (Found-Core) – scheduled Day 2 after the bicategory refactor |
| CategoryTheory/Obstruction.lean | 1 | Theoretical – proof of the general 2-monadic obstruction lemma | Only the statement is referenced; no downstream file relies on its proof | Sprint 41 (Found-Core) – Day 4 (same milestone as Found coherence) |
| AnalyticPathologies/Rho4.lean | 2 | Math – rho4_selfAdjoint, rho4_bounded | These theorems are cited only in AnalyticPathologies.Proofs, which currently uses by admit placeholders. So nothing incorrect propagates, but we have no verified statements yet | Sprint 41 (Math-AI) – Day 1-2. (They are short linear-algebra lemmas; estimate ≤ 60 LoC) |
| AnalyticPathologies/Cheeger.lean | 1 | Math – cheeger_selfAdjoint | Same story: the higher-level spectral-gap theorem is still a stub, so no false results are exported | Sprint 41 (Math-AI) – Day 2 |
| **Total** | **7** | – | Build passes, but we are not ρ = 4 "zero-sorry clean" | All closed by the end of Sprint 41 so Sprint 42 artifact-evaluation can run |

## Why We Tolerate Them for Sprint 40

- Goal of Sprint 40 was to land the bicategory skeleton, axiom centralisation, and rename without breaking CI
- The gaps in Cheeger/Rho4 were pre-existing (they used to hide inside the old SpectralGap/ tree). We merely surfaced them by moving the files
- Accepting the placeholders kept the diff small and unblocked downstream work (GitHub Projects, documentation, etc.)
- But they **absolutely must be paid off** before we claim "ρ = 4 zero-sorry" again

## Resolution Plan for Sprint 41

| Task | Owner | Est. LoC | Time budget | Notes |
|------|-------|----------|-------------|-------|
| Fill Found coherence proofs (assoc, leftUnit, rightUnit) | SWE-AI | ~40 | D1-2, S41 | Mostly by aesop_cat |
| Complete Obstruction.lean proof | SWE-AI | ~30 | D4, S41 | Use Street–Kennedy lifting lemma; outlines already in comments |
| Prove rho4_selfAdjoint, rho4_bounded | Math-AI | ~50 | D1, S41 | Direct from ContinuousLinearMap.adjoint properties and ‖·‖ |
| Prove cheeger_selfAdjoint | Math-AI | ~20 | D2, S41 | Literally by simpa using diagonal_isSelfAdjoint |

All four Math lemmas are trivial once HilbertSetup helpers are imported; they were left blank only because the old SpectralGap PR had them by sorry for speed.

## CI Enforcement

- `SORRY_ALLOWLIST.txt` will list exactly these seven lines with a "Sprint 41" tag
- `scripts/check-no-axioms.sh` remains zero
- Any new sorry outside the allow-list will fail the workflow

## Bottom Line

- They do not invalidate today's build – no false theorem can be exported because the theorems are presently unused
- They do block artifact evaluation and the "zero-sorry" KPI – hence they're scheduled for the very next sprint
- Tracking is explicit: allow-list + linked GitHub issues auto-opened by the TODO(S41-math) / TODO(S41-core) markers

**Decision**: Merge the current PR and treat Sprint 41 as a clean-up plus bicategory-coherence sprint.

---
*Sprint 40 Day 3*  
*Manager approval received*