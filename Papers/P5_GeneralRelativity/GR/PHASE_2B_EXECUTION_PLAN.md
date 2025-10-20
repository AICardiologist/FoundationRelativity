# Phase 2B Execution Plan: Remove Temporary Axiom
## Date: October 18, 2025
## Strategy: Option 4 - Hybrid Approach (Move Earlier)

---

## Executive Summary

**Goal**: Remove `dCoord_g_via_compat_ext_temp` axiom at line 1781 by moving the actual proof infrastructure earlier in the file.

**Strategy**: Move compatibility infrastructure (lines 2040-2530) before line 1781, then remove axiom and update usage.

**Estimated Time**: 1-2 hours

**Risk**: Low (all proofs complete, just reordering)

---

## Current State Analysis

### The Forward Reference Problem

```
Line 270:  dCoord definition ✅ (already early in file)
Line 1781: axiom dCoord_g_via_compat_ext_temp ⚠️ TEMPORARY
Line 1871: Riemann_via_Γ₁ proof uses axiom ⚠️
Line 2040: nabla_g definition ✅ COMPLETE
Lines 2050-2530: Compatibility helper lemmas ✅ COMPLETE
Line 2477: dCoord_g_via_compat_ext actual proof ✅ COMPLETE
```

**Gap**: 600+ lines between usage (1871) and proof (2477)

---

## Detailed Line Number Mapping

### Infrastructure to Move

| Component | Current Line | What It Does | Dependencies |
|-----------|-------------|--------------|--------------|
| `nabla_g` | 2040 | Covariant derivative of metric | dCoord (270), g, Γtot, sumIdx |
| Helper lemmas | ~2050-2476 | 9 specific compat cases | nabla_g, g, Γtot, Exterior |
| `dCoord_g_via_compat_ext` | 2477-2530 | Main proof (64 cases) | All 9 helper lemmas |

### The 9 Helper Lemmas

Based on the proof at line 2477, these are the 9 specific compatibility lemmas:

1. **Line ~2350**: `compat_r_tt_ext` - ∂_r g_{tt} case (diagonal)
2. **Line ~????**: `compat_r_rr_ext` - ∂_r g_{rr} case (diagonal)
3. **Line ~????**: `compat_r_θθ_ext` - ∂_r g_{θθ} case (diagonal)
4. **Line ~????**: `compat_r_φφ_ext` - ∂_r g_{φφ} case (diagonal)
5. **Line ~????**: `compat_θ_φφ_ext` - ∂_θ g_{φφ} case (diagonal)
6. **Line ~????**: `compat_t_tr_ext` - Off-diagonal cancellation
7. **Line ~????**: `compat_θ_rθ_ext` - Off-diagonal cancellation
8. **Line ~????**: `compat_φ_rφ_ext` - Off-diagonal cancellation
9. **Line ~????**: `compat_φ_θφ_ext` - Off-diagonal cancellation

**Note**: Need to find exact line numbers for all 9 lemmas

### Additional Helper Lemmas

From grep results, there are also:
- Line 2530: `compat_refold_r_kb`
- Line 2548: `compat_refold_θ_kb`
- Line 2567: `compat_refold_r_ak`
- Line 2584: `compat_refold_θ_ak`

These may be used by the main proof or the 9 specific cases.

---

## Dependency Check

### What nabla_g needs (all available early):
✅ `dCoord` - line 270
✅ `g` - Schwarzschild (imported)
✅ `Γtot` - Schwarzschild (imported)
✅ `sumIdx` - Schwarzschild (imported)
✅ `Idx` - Schwarzschild (imported)

### What compat helpers need (checking...):
✅ `nabla_g` - will be moved with them
✅ `g`, `Γtot`, `sumIdx`, `Idx` - Schwarzschild (imported)
✅ `Exterior` - line 27 (already early)
✅ `dCoord` - line 270
⚠️ **May need**: Specific derivative lemmas (need to check)
⚠️ **May need**: Field simplification lemmas (need to check)

### What dCoord_g_via_compat_ext needs:
✅ All 9 helper lemmas - will be moved together
✅ `Exterior.r_ne_zero`, `Exterior.f_ne_zero` - already defined
✅ `g`, `Γtot`, `sumIdx` - Schwarzschild (imported)

---

## Execution Steps

### Step 0: Create Backup

```bash
# Current state
git status

# Commit current work
git add -A
git commit -m "chore: backup before Phase 2B modularization (Option 4)"

# Tag for easy recovery
git tag phase-2b-start
```

### Step 1: Identify Exact Range to Move

**Action**: Find all compatibility infrastructure lines

```bash
# Find nabla_g and all compat lemmas
grep -n "^noncomputable def nabla_g\|^lemma compat_\|^@\[simp\] lemma compat_" \
  Papers/P5_GeneralRelativity/GR/Riemann.lean > /tmp/compat_lines.txt

# Check what's between line 2040 and 2530
```

**Expected range**: Approximately lines 2040-2530 (490 lines)

**Target location**: Before line 1781 (before axiom)

### Step 2: Check for Hidden Dependencies

**Action**: Search for any lemmas used by compat infrastructure that are defined later

```bash
# Check if any lemmas after line 2530 are used by compat proofs
# (Manual inspection required)
```

**Verification**:
- Read compat_r_tt_ext proof (line ~2350)
- Check what lemmas it uses
- Verify those lemmas are defined before line 1781

### Step 3: Move Compatibility Infrastructure

**Method**: Manual cut-and-paste in editor (safer than sed for this size)

1. Open Riemann.lean in editor
2. Select lines 2040-2530 (approx range)
3. Cut to clipboard
4. Navigate to line 1780 (just before axiom)
5. Paste
6. Save

**New structure**:
```
Line 270:   dCoord ✅
Line ~500:  Phase 2A Master Lemmas ✅
Line ~1780: nabla_g (MOVED)
Line ~1790: compat helper lemmas (MOVED)
Line ~2250: dCoord_g_via_compat_ext proof (MOVED)
Line ~2270: [old axiom location - will delete]
Line ~2360: Riemann_via_Γ₁ proof (uses dCoord_g_via_compat_ext)
```

### Step 4: Remove Temporary Axiom

**Action**: Delete axiom declaration

1. Find line with `axiom dCoord_g_via_compat_ext_temp`
2. Delete entire axiom declaration (should be 4-5 lines)
3. Save

### Step 5: Update Main Proof Usage

**Action**: Change from `_temp` to actual lemma

1. Find line 1871 (in Riemann_via_Γ₁ proof)
2. Change `dCoord_g_via_compat_ext_temp` to `dCoord_g_via_compat_ext`
3. Save

**Current**:
```lean
simp_rw [dCoord_g_via_compat_ext_temp M r θ h_ext]
```

**After**:
```lean
simp_rw [dCoord_g_via_compat_ext M r θ h_ext]
```

### Step 6: Test Build

**Action**: Verify Lean build succeeds

```bash
cd /Users/quantmann/FoundationRelativity

# Build just Riemann.lean to test
lake build Papers.P5_GeneralRelativity.GR.Riemann

# If successful, build everything
lake build Papers.P5_GeneralRelativity
```

**Expected**: 0 errors, ~3078 jobs

**If errors occur**:
- Check error messages for missing dependencies
- May need to move additional helper lemmas
- Use git to review changes: `git diff Riemann.lean`

### Step 7: Verify No Axioms Remain

**Action**: Search for any remaining axioms

```bash
grep -n "^axiom" Papers/P5_GeneralRelativity/GR/Riemann.lean
```

**Expected**: No output (0 axioms)

### Step 8: Verify Sorry Count Unchanged

**Action**: Count sorries before and after

```bash
# Should still be 22 sorries (none in Phase 2A or Phase 3)
grep -c "sorry" Papers/P5_GeneralRelativity/GR/Riemann.lean
```

### Step 9: Commit Success

**Action**: Commit the changes

```bash
git add Papers/P5_GeneralRelativity/GR/Riemann.lean
git commit -m "feat: complete Phase 2B - remove temporary axiom

- Moved compatibility infrastructure (nabla_g + helpers) earlier in file
- Removed axiom dCoord_g_via_compat_ext_temp (line 1781)
- Updated Riemann_via_Γ₁ proof to use actual lemma dCoord_g_via_compat_ext
- All compatibility proofs complete (0 sorries, 0 axioms)
- Phase 2A: 100% complete (6 differentiability sorries discharged)
- Phase 3: 100% complete (Riemann_via_Γ₁ fully proven)
- Build: ✅ 3078 jobs, 0 errors"
```

### Step 10: Update Status Report

**Action**: Document Phase 2B completion

- Update STATUS_REPORT_OCT18_PHASES_2A_3_COMPLETE.md
- Note Phase 2B completion date
- Update remaining work count

---

## Rollback Plan (If Something Goes Wrong)

### Option 1: Git Revert
```bash
git reset --hard phase-2b-start
```

### Option 2: Selective Undo
```bash
# If some changes are good, selectively revert file
git checkout phase-2b-start -- Papers/P5_GeneralRelativity/GR/Riemann.lean
```

### Option 3: Manual Comparison
```bash
# Compare current vs backup
git diff phase-2b-start Papers/P5_GeneralRelativity/GR/Riemann.lean
```

---

## Alternative: If Moving Earlier Fails

### Fallback: Extract to Module (Option 3 - Lite)

If moving earlier encounters unexpected dependency issues, fall back to:

**Create**: `MetricCompatibility.lean`

```lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild

namespace Papers.P5_GeneralRelativity
namespace Schwarzschild

-- Copy dCoord definition from Riemann.lean line 270
@[simp] noncomputable def dCoord (μ : Idx) (F : ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ :=
  match μ with
  | Idx.r => deriv (fun s => F s θ) r
  | Idx.θ => deriv (fun t => F r t) θ
  | _     => 0

-- Copy Exterior structure from Riemann.lean line 27
structure Exterior (M r θ : ℝ) : Prop where
  hM : 0 < M
  hr_ex : 2 * M < r

-- Copy nabla_g (line 2040)
-- Copy all compat helpers (lines 2050-2530)
-- Copy dCoord_g_via_compat_ext (line 2477)

end Schwarzschild
end Papers.P5_GeneralRelativity
```

**Then** update Riemann.lean:
```lean
import Papers.P5_GeneralRelativity.GR.MetricCompatibility

-- Remove dCoord definition (use from MetricCompatibility)
-- Remove Exterior (use from MetricCompatibility)
-- Remove nabla_g and compat helpers (in module)
-- Use dCoord_g_via_compat_ext from module
```

**Estimated time if needed**: 2-3 hours

---

## Success Criteria

✅ **Phase 2B Complete** when:
1. Axiom `dCoord_g_via_compat_ext_temp` removed from Riemann.lean
2. Main proof `Riemann_via_Γ₁` uses actual lemma `dCoord_g_via_compat_ext`
3. Build succeeds: `lake build Papers.P5_GeneralRelativity` → 0 errors
4. No axioms in Riemann.lean: `grep "^axiom" Riemann.lean` → no results
5. Sorry count unchanged: Still 22 sorries (none in Phase 2A, 2B, or 3)
6. Git commit created documenting Phase 2B completion

---

## Timeline

| Step | Description | Estimated Time | Risk |
|------|-------------|----------------|------|
| 0 | Create backup | 5 min | None |
| 1 | Identify exact range | 10 min | Low |
| 2 | Check dependencies | 15 min | Low |
| 3 | Move infrastructure | 15 min | Medium |
| 4 | Remove axiom | 2 min | None |
| 5 | Update usage | 2 min | None |
| 6 | Test build | 10 min | N/A |
| 7 | Verify no axioms | 2 min | None |
| 8 | Verify sorry count | 2 min | None |
| 9 | Commit success | 5 min | None |
| 10 | Update status report | 10 min | None |
| **Total** | | **78 min** | **Low-Medium** |

**Buffer**: +30 min for unexpected issues = **~2 hours total**

---

## Post-Completion

### Immediate:
- ✅ Phase 2A: 100% complete (6 sorries discharged)
- ✅ Phase 2B: 100% complete (axiom removed)
- ✅ Phase 3: 100% complete (Riemann_via_Γ₁ proven)
- ✅ Combined: **Fully formal verification, 0 axioms in core proof**

### Next Steps (from STATUS_REPORT):
1. **Priority 1**: Phase 4 - Ricci Identity Infrastructure (axioms at lines 4001, 4038)
2. **Priority 2**: Symmetry Infrastructure (axioms at lines 4047, 4062)
3. **Priority 3**: Remaining 22 sorries in auxiliary lemmas
4. **Optional**: File modularization cleanup (Phase 2B.2)

---

**Prepared by**: Research Team (Claude Code)
**Date**: October 18, 2025
**Status**: Ready to execute
**Estimated completion**: 1-2 hours
**Risk assessment**: Low-Medium (all proofs complete, just reorganization)
