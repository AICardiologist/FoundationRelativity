# Riemann Activation Quick Reference

**See also:** [ACTIVATION_TRACKING.md](./ACTIVATION_TRACKING.md) | [ROADMAP_Schwarzschild_Vacuum.md](./ROADMAP_Schwarzschild_Vacuum.md)

## Current State ✅
- **Baseline:** 51 errors (stable)
- **Mode:** `baseline`
- **LHS Stage-1:** Proven (4 lemmas ready)
- **RHS Stage-1:** Blocked on `gInv`

## Pre-Flight Checklist
- [ ] Issue A resolved: sumIdx_expand strategy chosen
- [ ] Issue B resolved: gInv domain strategy chosen
- [ ] Branch created: `feat/p5-activate-lhs-splits`

## Activation Commands (in order)

### 1. Set Mode
```bash
./scripts/set-activation.sh stage1-lhs-both
```

### 2. Add Local Enumerator (paste in each split section)
```lean
local lemma sumIdx_expand_local (f : Idx → ℝ) :
  sumIdx f = f Idx.t + f Idx.r + f Idx.θ + f Idx.φ := by
  -- Use chosen option A or B
  sorry
local attribute [simp] sumIdx_expand_local
```

### 3. Apply Pattern (for each family)
```lean
-- Binary split
have h_add := dCoord_add c first_family second_family r θ
-- 4-term linearity
have h_linP := dCoord_add4_flat c P_t P_r P_θ P_φ r θ
-- Product rule (t-summand only)
have h_push := by simpa using dCoord_mul c ... r θ
-- Chain
have H := hsum; rw [h_push] at H
simpa [add_comm, add_left_comm, add_assoc] using H
```

### 4. Verify
```bash
make audit                                    # Quick sanity
./scripts/check-activation.sh stage1-lhs-both # Mode check
./scripts/check-baseline.sh                   # Still 51
git diff --word-diff-regex='[[:alnum:]_]+|.'  # Review diff
```

## Commit Message Templates

### PR-A: LHS Activation
```
feat(P5/Riemann): Activate Stage-1 LHS splits

- ACTIVATION_STATUS: baseline → stage1-lhs-both
- sumIdx_expand: Option [A/B] (local only)
- Enabled: Stage1_LHS split sections
- Pattern: dCoord_add4_flat + dCoord_mul
- Baseline: 51 (unchanged)

Verification:
✅ make audit
✅ ./scripts/check-activation.sh stage1-lhs-both
✅ ./scripts/check-baseline.sh (51)
```

### PR-B: RHS Activation (after gInv)
```
feat(P5/Riemann): Enable gInv and RHS Stage-1

- gInv: Strategy [A/B] ([hypothesis-gated/chart-restricted])
- ACTIVATION_STATUS: stage1-lhs-both → stage1-full
- Enabled: RHS Stage-1 sections
- Pattern: Same as LHS with gInv replacing g
- Baseline: 51 (unchanged)

Verification:
✅ make audit
✅ ./scripts/check-activation.sh stage1-full
✅ ./scripts/check-baseline.sh (51)
```

## Rollback (if needed)
```bash
git revert HEAD                        # Revert last commit
./scripts/set-activation.sh baseline   # Reset marker
make baseline                          # Verify
```

## Key Files
- **Activation marker:** Line 97 in Riemann.lean
- **Stage-1 lemmas:** Lines 708-950
- **sumIdx templates:** Lines 1228-1262
- **gInv stub:** Lines 291-298
- **Split sections:** Lines 1280-1350

## Don't Forget
- ✅ All `[simp]` attrs must be local
- ✅ Stage-1 facts stay outside main proof
- ✅ Update PR template checkboxes
- ✅ Tag reviewers from ACTIVATION_TRACKING.md

---

**Next action:** Decide Issue A (sumIdx_expand) → run `./scripts/set-activation.sh stage1-lhs-both` → follow PR-A DoD