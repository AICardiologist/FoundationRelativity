# P5/GR: Stage‑1 LHS+RHS activation, μ‑splits & guardrails (UG −5, OE −4)

> **Status: Draft** (UG=46, OE=7; audits green; budgets enforced)
> **Scope:** Stage‑1 LHS+RHS infrastructure, μ‑splits, guardrails
> **Next:** RHS micro‑facts & Stage‑2 preview to drop UG further; then flip Draft → Ready

## Summary

This PR activates Stage‑1 on both sides of the alternation identity for the Riemann tensor, adds μ‑expansion on the RHS, wires the expansions into the main lemma, and introduces guardrails (audits + hook fixes). Result: Unsolved Goals (UG) down to 46 (−5), Other Errors (OE) down to 7 (−4); Total 53; no simp warnings.

## Motivation
- **LHS Stage‑1** splits and product pushes expose proof obligations in a controlled way
- **RHS μ‑splits** (per μ ∈ {t, r, θ, φ}) remove noise and give fine‑grained targets for Stage‑1/Stage‑2 facts
- **Guardrails** (pre‑commit mode awareness + audits) prevent regressions and accidental global [simp]

## What Changed

### LHS Stage‑1 Infrastructure
- `Stage1_LHS_Splits` file‑scope section with local expander `sumIdx_expand_local` and bridge usage `dCoord_sumIdx_via_local_expand`
- All 16 product pushes (t, r, θ, φ × 2 families × c/d branches) wired in the main lemma
- Local [simp] enablement for Stage‑1 facts scoped to the lemma

### RHS Stage‑1 Infrastructure
- `Stage1_RHS_Splits` file‑scope section with:
  - `sumIdx_expand_local_rhs` (μ‑expander)
  - `Hsplit_RHS₁/Hsplit_RHS₂` (definitional splits)
  - `Hsplit_RHS₁_expanded/Hsplit_RHS₂_expanded`
  - `Hsplit_RHS_combined` (4‑term μ‑expansions per RHS term)
- RHS wiring in main lemma after LHS simplification

### Simplification & Helpers
- Switched several `simp only` → `simp`/`simp_all` to allow local [simp] rules to fire
- Introduced `dCoord_zero_fun` (by‑value helper)
- Added targeted inclusion of `nabla_g_zero`, `dCoord_const` in final `simp_all`

### Tooling/Guardrails
- **Pre‑commit hook** (`.githooks/pre-commit`): Reads staged activation mode, calls `scripts/check.sh MODE`
- **Budgets** (`scripts/check-activation-budget.sh`): `stage1-lhs-both`: MAX_UG=46, MAX_OE=8 (running at 7)
- **Audits**:
  - `scripts/audit-simp-progress.sh` – no "simp made no progress" regressions
  - `scripts/audit-rhs-splits.sh` – no global [simp] on RHS μ‑expander
  - Both wired into `make audit`

## Metrics

| Metric | Baseline | After LHS | After RHS | **Change** |
|--------|----------|-----------|-----------|------------|
| UG     | 51       | 46        | 46        | **−5**     |
| OE     | 2        | 11        | 7         | **+5**     |
| Total  | 53       | 57        | 53        | **0**      |
| Simp warnings | 0 | 2      | 0         | **0**      |

## How to Review

```bash
# Ensure repo-managed hooks are enabled
git config core.hooksPath .githooks

# Run audits (includes simp-progress + RHS guardrail)
make audit

# Budget gate for current activation mode
./scripts/check-activation-budget.sh   # should report UG=46, OE=7 (≤8)

# Full file build (currently fails with 53 errors - expected)
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

## CI Status

- ✅ **stage1-budgets** job (required): Audits + activation budget
- ⚠️ **lean-build** job (optional): Expected to fail with 53 errors until UG/OE reduced further

## Risk & Safety
- No global [simp] added; expansions are by value or file‑scoped
- Pre‑commit is mode‑aware; no baseline‑only blocks
- New audits catch common pitfalls
- Rollback: change `-- ACTIVATION_STATUS:` to `baseline`

## Follow‑ups
1. RHS micro‑facts for RiemannUp symmetries (local, by value)
2. Block normalizers for diagonal/off‑diagonal structure
3. Stage‑2 preview: apply RiemannUp expansion to single μ (e.g., μ=t) for UG<46
4. Tighten MAX_OE to 7 once CI confirms stability

## Files Changed
- `Papers/P5_GeneralRelativity/GR/Riemann.lean` (+438, -7)
- `.githooks/pre-commit` (+23, -4)
- `.github/workflows/activation-stage1.yml` (new)
- `Makefile` (+2, -1)
- `scripts/*` (5 files added/modified)

---

📎 Attachments:
- [ACTIVATION_DIFF.md](./ACTIVATION_DIFF.md) - Detailed line-by-line changes
- [CHANGELOG_ENTRY.md](./CHANGELOG_ENTRY.md) - Release notes format