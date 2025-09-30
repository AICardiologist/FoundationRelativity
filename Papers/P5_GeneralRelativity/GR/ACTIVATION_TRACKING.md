# Riemann Tensor Activation Tracking

**See also:** [ACTIVATION_QUICKREF.md](./ACTIVATION_QUICKREF.md) | [ROADMAP_Schwarzschild_Vacuum.md](./ROADMAP_Schwarzschild_Vacuum.md)

## Current Status
- **Baseline:** 51 errors (all intentional placeholders)
- **Activation Status:** `baseline`
- **Infrastructure:** Complete and activation-ready

## Status Matrix

| Item                         | Choice / Mode                         | Status                                  | Verified on (commit) |
|-----------------------------|----------------------------------------|-----------------------------------------|----------------------|
| `sumIdx_expand` strategy    | ☐ Option A (definitional) / ☐ Option B | ☐ undecided / ☐ chosen                   |                      |
| `gInv` domain strategy      | ☐ A: hypothesis-gated / ☐ B: chart     | ☐ undecided / ☐ chosen                   |                      |
| Activation mode             | baseline / stage1-lhs-first / **stage1-lhs-both** / stage1-full | **baseline**                |                      |
| Stage-1 LHS (first family)  | `Hc_one`, `Hd_one`                     | **proven (top-level)**                   |                      |
| Stage-1 LHS (second family) | `Hc2_one`, `Hd2_one`                   | **proven (top-level)**                   |                      |
| RHS Stage-1                 | needs `gInv`                           | ☐ blocked / ☐ ready                      |                      |
| Alternation scaffold        | in place                               | **ready**                                |                      |
| Baseline check              | `./scripts/check-baseline.sh`          | **51 errors**                            |                      |

## Decision Points (Open Issues)

### Issue A - Choose sumIdx_expand Strategy
- [ ] **Option A:** Definitional (`sumIdx f` is definitionally `f t + f r + f θ + f φ`)
- [ ] **Option B:** Finite type (requires `[DecidableEq Idx] [Fintype Idx]`)
- **Location:** Lines 1231-1242 in Riemann.lean
- **Decision:** _TBD_

### Issue B - Choose gInv Domain Strategy
- [ ] **Option A:** Local hypothesis-gated lemmas (`hr : r ≠ 0`, `hs : Real.sin θ ≠ 0`)
- [ ] **Option B:** Chart-restricted sections
- **Location:** Lines 274-284 in Riemann.lean
- **Decision:** _TBD_

### Issue C - Activation Mode & Branch Discipline
- [ ] First PR: `stage1-lhs-both` (LHS only)
- [ ] Include RHS if gInv ready: `stage1-full`
- **Branch naming:** `feat/p5-activate-lhs-splits`, `feat/p5-enable-gInv-and-rhs`
- **Decision:** _TBD_

## Activation Checklist

### PR 1: LHS Activation (`feat/p5-activate-lhs-splits`)
- [ ] Bump marker to `stage1-lhs-both`
- [ ] Add `sumIdx_expand_local` to each split section
- [ ] Mark as `local attribute [simp]` only
- [ ] Apply pattern for each family:
  ```lean
  have hsum := dCoord_add4_flat μ A B C D r θ
  have hpush := by simpa using dCoord_mul μ ... r θ
  have H := hsum; rw [hpush] at H; simpa [...] using H
  ```
- [ ] Verify: `./scripts/check-activation.sh stage1-lhs-both`
- [ ] Verify: `./scripts/check-baseline.sh` (still 51)
- [ ] Pre-commit passes

### PR 2: RHS Activation (`feat/p5-enable-gInv-and-rhs`)
- [ ] Uncomment `gInv` definition
- [ ] Add local `[simp]` facts (gInv_offdiag, etc.) in RHS sections only
- [ ] Apply RHS micro-pattern (lines 1528-1539)
- [ ] Verify: `./scripts/check-activation.sh stage1-full`
- [ ] Verify: `./scripts/check-baseline.sh` (still 51)
- [ ] Pre-commit passes

### PR 3+: Baseline Reduction (optional)
- [ ] Complete `dCoord_sumIdx` proof (reduces error count)
- [ ] Update `scripts/check-baseline.sh` with new count
- [ ] Complete `alternation_dC_eq_Riem` using staged facts

## Verification Commands
```bash
# Before any PR
make check

# After LHS activation
./scripts/check-activation.sh stage1-lhs-both
./scripts/check-baseline.sh  # Should still be 51

# After RHS activation
./scripts/check-activation.sh stage1-full
./scripts/check-baseline.sh  # Should still be 51
```

## Key Files & Line Numbers
- **Stage-1 LHS lemmas:** Lines 708-926 (proven, compact)
- **sumIdx_expand options:** Lines 1228-1247
- **Local enumerator template:** Lines 1249-1262
- **gInv definition:** Lines 291-298
- **gInv domain note:** Lines 274-284
- **RHS micro-pattern:** Lines 1528-1539
- **RHS skeleton:** Lines 1542-1570
- **Split sections:** Lines 1280-1350 (ready to uncomment)

## Guards in Place
- ✅ Pre-commit: Blocks global `[simp] sumIdx_expand`
- ✅ Pre-commit: Blocks RHS without `gInv`
- ✅ Scripts: `check-activation.sh` + `check-baseline.sh`
- ✅ PR template: Mechanical checklist for Paper 5

## Triage Commands
```bash
# Verify activation mode:
./scripts/check-activation.sh stage1-lhs-both   # or 'baseline', 'stage1-full'

# Verify baseline:
./scripts/check-baseline.sh                     # expects 51

# Quick audit: ensure no global [simp] for sumIdx_expand
rg -n 'attribute\s*\[simp\].*sumIdx_expand' Papers | grep -v '^\s*--'

# Audit: RHS not accidentally enabled without gInv
rg -n 'section\s+Stage1_RHS' Papers

# Locate activation markers / anchors
rg -n 'ACTIVATION_STATUS|STAGE1-READY|RHS-READY|sumIdx_expand_local' Papers
```

## Definition of Done (DoD)

### PR-A: LHS activation (stage1-lhs-both)
- [ ] Marker bumped to `stage1-lhs-both`
- [ ] `sumIdx_expand_local` pasted inside each split section and marked `local [simp]`
- [ ] 4-term expansions via `dCoord_add4_flat`; product rules via `dCoord_mul`
- [ ] No global `[simp]`; pre-commit hook passes
- [ ] `./scripts/check-activation.sh stage1-lhs-both` passes
- [ ] `./scripts/check-baseline.sh` still shows 51
- [ ] PR template (Paper 5 section) boxes checked

### PR-B: RHS activation (after gInv)
- [ ] `gInv` uncommented per chosen domain strategy (noted in PR)
- [ ] Any `[simp]` for `gInv` kept local to RHS sections
- [ ] 4-term expansions via `dCoord_add4_flat`; product rules via `dCoord_mul`
- [ ] Baseline still 51; activation script passes for chosen mode (e.g., `stage1-full`)
- [ ] PR template boxes checked

## Rollback Recipe
```bash
# If a single activation commit needs to be reverted:
git revert <commit-sha>

# If a merged PR was a merge-commit:
git revert -m 1 <merge-commit-sha>

# Restore marker to 'baseline' and re-run gates:
./scripts/check-activation.sh baseline
./scripts/check-baseline.sh
```

## Known Pitfalls
- Don't enable Stage-1 sections inside the main proof (keeps goals isolated)
- Keep `sumIdx_expand` local `[simp]`; pre-commit enforces this
- Don't enable RHS before `gInv` (pre-commit enforces this)
- If you intentionally reduce the baseline (e.g., proving a global lemma), update `scripts/check-baseline.sh`

## Reviewer Cheatsheet (paste into PR description)
```markdown
**Reviewer checklist (Paper 5 / Riemann)**

- [ ] Activation marker mode is correct
- [ ] Only local `[simp]` attributes added (no globals)
- [ ] Stage-1 facts remain outside main proof
- [ ] 4-term linearity uses `dCoord_add4_flat`; product rules use `dCoord_mul`
- [ ] Scripts:
  - [ ] `./scripts/check-activation.sh <mode>` ✅
  - [ ] `./scripts/check-baseline.sh` ✅ (51)
- [ ] Rollback section in PR describes how to revert
```