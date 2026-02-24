# Comprehensive Fix Plan: All 33 Remaining Errors (October 27, 2025)

**Status**: 📋 Tactical Plan - Ready for execution
**Baseline**: 33 errors after recursion elimination (ca01ea2)
**Goal**: Complete file compilation (0 errors)
**Estimated Total Time**: 5-6 hours
**Prepared by**: Claude Code (Sonnet 4.5)

---

## Overview

This plan provides step-by-step tactical approach to eliminate all remaining errors. Errors are grouped by type and ordered by priority (blocking issues first).

### Error Breakdown by Category

| Priority | Category | Count | Blocking? | Est. Time |
|----------|----------|-------|-----------|-----------|
| 🔴 P1 | Unicode parser errors | 2 | YES | 5 min |
| 🟡 P2 | Missing lemma | 2 | YES | 15 min |
| 🟡 P3 | Quartet splitter signatures | 6 | PARTIAL | 1-2 hours |
| 🟡 P4 | Branches sum unsolved goals | 11 | PARTIAL | 2-3 hours |
| 🟢 P5 | Type mismatches | 7 | NO | 1-2 hours |
| 🟢 P6 | Rewrite failures | 2 | NO | 30 min |
| 🟢 P7 | Simp no progress | 4 | NO | 30 min |

---

## Phase 1: BLOCKING ERRORS (P1-P2) - Must fix first

### Step 1.1: Fix Unicode Parser Errors (5 minutes)

**Lines affected**: 7136, 7453
**Issue**: Unicode subscripts `₊` and `₋` breaking Lean 4 parser
**Impact**: These break parsing, creating cascading failures

**Action**:
```bash
cd /Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR
sed -i.bak_unicode_fix 's/reduce₊/reduce_plus/g; s/reduce₋/reduce_minus/g' Riemann.lean
```

**Verification**:
```bash
grep -n "reduce_plus\|reduce_minus" Riemann.lean | head -10
```

**Expected**: Should see ASCII `reduce_plus` and `reduce_minus` at lines ~7136, ~7200, ~7453, ~7520

**Build test**: `lake build 2>&1 | grep "unexpected token" | wc -l` should return `0`

---

### Step 1.2: Add sumIdx_pick_one Lemma (15 minutes)

**Lines affected**: 7959, 8089
**Issue**: Helper lemma undefined
**Purpose**: Convert scalar `f(k)` to sum form `Σᵢ f(i)·δᵢₖ`

**Location**: Add after `sumIdx_reduce_by_diagonality_right` (around line 2010)

**Implementation**:
```lean
/-- Convert scalar to sum with Kronecker delta.

    This is the "selection" or "picking" lemma: a single term equals
    a sum where all terms vanish except the chosen index.

    Mathematically: f(k) = Σᵢ f(i)·δᵢₖ where δᵢₖ = 1 if i=k, 0 otherwise.
-/
lemma sumIdx_pick_one {f : Idx → ℝ} (k : Idx) :
  f k = sumIdx (fun i => f i * (if i = k then 1 else 0)) := by
  classical
  simp only [sumIdx_expand]
  -- Expand sum: f(t)·δₜₖ + f(r)·δᵣₖ + f(θ)·δθₖ + f(φ)·δφₖ
  -- Exactly one term is f(k)·1, rest are f(i)·0
  cases k
  · -- k = t
    simp only [ite_true, ite_false]
    ring
  · -- k = r
    simp only [ite_true, ite_false]
    ring
  · -- k = θ
    simp only [ite_true, ite_false]
    ring
  · -- k = φ
    simp only [ite_true, ite_false]
    ring
```

**Alternative (more compact)**:
```lean
lemma sumIdx_pick_one {f : Idx → ℝ} (k : Idx) :
  f k = sumIdx (fun i => f i * (if i = k then 1 else 0)) := by
  classical
  simp only [sumIdx_expand]
  cases k <;> simp [mul_one, mul_zero, add_zero, zero_add]
```

**Verification**:
```bash
lake build 2>&1 | grep "sumIdx_pick_one" | grep "Unknown identifier" | wc -l
```
Should return `0`.

**Build test after Phase 1**:
```bash
lake build 2>&1 | grep "^error:" | wc -l
```
Expected: ~27-29 errors (down from 33)

---

## Phase 2: QUARTET SPLITTER SIGNATURES (P3) - 1-2 hours

### Context

The `first_block` and `second_block` replacements are mathematically correct but may produce goal states that don't perfectly match the surrounding proof structure. We need to add adapter layers.

### Step 2.1: Examine Goal State Mismatches (15 min)

**Diagnostic approach**:

For each unsolved goal, insert `sorry` and examine what Lean expects vs. what we produced:

```lean
-- Line 7123 example
have step₁ := ...
  simpa [this, sumIdx_map_sub]
  sorry  -- DIAGNOSTIC: Check goal state here
```

Use Lean's interactive mode or `--server` to see:
- Expected type
- Produced type
- Unification failure reason

**Lines to check**: 7095, 7105, 7123, 7411, 7422, 7440

---

### Step 2.2: Add Wrapper Steps (30-60 min)

**Strategy**: Add explicit `show` or intermediate `have` to guide Lean.

**Pattern A: Type annotation wrapper**
```lean
-- If Lean complains about implicit argument mismatch
have step₁ : (∀ ρ : Idx, ...) := by
  intro ρ
  show ...  -- explicit type
  simpa [this, sumIdx_map_sub]
```

**Pattern B: Explicit intermediate goal**
```lean
have step₁ := by
  have intermediate : P := by ...
  have final : Q := by
    rw [intermediate]
    simpa [...]
  exact final
```

**Pattern C: Eta-expansion fix**
```lean
-- If issue is eta-contraction mismatch
(sumIdx_reduce_by_diagonality M r θ b (fun e => K e))
-- vs
(sumIdx_reduce_by_diagonality M r θ b K)
```

---

### Step 2.3: Fix Step₁ Proofs (30 min)

**Lines**: 7123, 7440

**Current code**:
```lean
simpa [this, sumIdx_map_sub]
```

**If failing**, try:
```lean
-- Option A: Make simp set explicit
simp only [this, sumIdx_map_sub, sumIdx_expand]

-- Option B: Split into explicit rewrites
rw [this]
rw [sumIdx_map_sub]
rfl

-- Option C: Use calc to show each step
calc
  sumIdx ... = sumIdx ... := by rw [this]
  _ = ... := by rw [sumIdx_map_sub]
```

---

### Step 2.4: Fix First_block Signatures (30 min)

**Lines**: 7105, 7422

**Issue**: The `first_block` lemma produces a goal but the calling context expects slightly different form.

**Fix approach**:
```lean
have first_block :
  sumIdx ... = g M b b r θ * (...) := by
  [existing proof]

-- Add adapter if needed
have first_block' :
  sumIdx ... = [expected form] := by
  calc
    sumIdx ... = g M b b r θ * (...) := first_block
    _ = [expected form] := by ring  -- or other tactic
```

---

### Step 2.5: Fix Goal Statements (30 min)

**Lines**: 7095, 7411

**Issue**: The overall lemma goal statement might need adjustment.

**Current pattern**:
```lean
lemma ΓΓ_quartet_split_b ... :
  ... = (bb_core) + (ρρ_core) := by
  classical
  have first_block := ...
  have second_block := ...
  [assemble]
```

**If assembly fails**, add explicit calc:
```lean
  calc
    LHS = ... := by [reshape using first_block]
    _ = ... := by [reshape using second_block]
    _ = bb_core + ρρ_core := by ring
```

---

## Phase 3: BRANCHES SUM PROOFS (P4) - 2-3 hours

### Context

The `branches_sum` proof has 11 unsolved goals in long calc chains. These need intermediate steps or explicit rewrites.

### Step 3.1: Fix hb_pack Goal (Line 7892) - 30 min

**Current code** (lines 7888-7892):
```lean
have hb_pack :
    (sumIdx B_b)
    - sumIdx (fun ρ => (Γtot M r θ ρ μ a) * (nabla_g M r θ ν ρ b))
    + sumIdx (fun ρ => (Γtot M r θ ρ ν a) * (nabla_g M r θ μ ρ b))
  =
    - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ) := by
```

**The proof has 4 steps below this**. If step 4 (calc assembly) fails:

**Fix**: Break the calc into smaller pieces:
```lean
have hb_pack :
    (sumIdx B_b) - ... + ... = - sumIdx (...) := by
    classical
    -- Step 1: payload cancellation (already done)
    have payload_cancel := ...

    -- Step 2: ΓΓ block reshape (already done)
    have ΓΓ_block := ...

    -- Step 3: scalar packaging (already done)
    have scalar_finish_bb := ...
    have core_as_sum_b := ...
    have scalar_finish := ...

    -- Step 4: Assembly (SPLIT INTO SUBSTEPS)
    have step4a : (sumIdx B_b) - ... + ... = sumIdx (fun ρ => ...) := by
      simp only [nabla_g, RiemannUp, sub_eq_add_neg]
      rw [payload_cancel]
      -- More explicit steps
      sorry  -- DIAGNOSTIC

    have step4b : sumIdx (fun ρ => ...) = - sumIdx (...) + rho_core_b := by
      sorry  -- DIAGNOSTIC

    calc
      LHS = ... := step4a
      _ = ... := step4b
```

---

### Step 3.2: Fix Scalar Package Goals (Lines 7940, 7974) - 30 min

**Current code** (line 7940):
```lean
have scalar_finish_bb :
    ( -(dCoord μ ...) * g M b b r θ
      +  (dCoord ν ...) * g M b b r θ )
    +  ( g M b b r θ * (...) )
    =
      - ( (...) * g M b b r θ ) := by
  ring
```

**If `ring` fails**:

**Diagnosis**: Ring might not see the goal due to definitional unfolding issues.

**Fix**:
```lean
have scalar_finish_bb :
    ... = ... := by
  show (A * g + B * g + g * C) = -(D * g)  -- explicit show
  ring

-- Or expand manually:
have scalar_finish_bb : ... = ... := by
  have h1 : A * g + B * g = (A + B) * g := by ring
  have h2 : g * C = C * g := by ring
  have h3 : (A + B) * g + C * g = (A + B + C) * g := by ring
  have h4 : (A + B + C) * g = -(D * g) := by
    -- Show A + B + C = -D
    sorry  -- May need explicit calculation
  exact ...
```

---

### Step 3.3: Fix Core Sum Rewrites (Lines 7994, 8124) - 30 min

**Current code** (line 7994):
```lean
_   = - sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    + rho_core_b := by
  simp only [h_rho_core_b]
  rw [← core_as_sum_b, ← sumIdx_add_distrib]
  apply sumIdx_congr; intro ρ
  ...
```

**If `rw [← core_as_sum_b]` fails**:

**Diagnosis**: The current goal shape doesn't match `core_as_sum_b`'s LHS.

**Fix**:
```lean
-- Option A: Show goal matches pattern first
_   = ... := by
  simp only [h_rho_core_b]
  have goal_shape : [current_goal] = [core_as_sum_b_LHS_pattern] := by
    ring  -- or unfold/simp
  rw [goal_shape]
  rw [← core_as_sum_b, ← sumIdx_add_distrib]
  ...

-- Option B: Use conv to reshape in place
_   = ... := by
  simp only [h_rho_core_b]
  conv_lhs =>
    -- navigate to where core_as_sum_b should apply
    rw [← core_as_sum_b]
  rw [← sumIdx_add_distrib]
  ...
```

---

### Step 3.4: Fix Remaining Branches Sum Goals (1-1.5 hours)

**Lines**: 8023, 8070, 8104, 8165, 8212, 8521, 8608

**General strategy for each**:
1. Add `sorry` to identify exact goal
2. Check if intermediate `have` statements are being used correctly
3. Add explicit `show` for complex goals
4. Break calc chains into smaller pieces
5. Use `conv` for surgical rewrites

**Template**:
```lean
-- For each unsolved goal at line N:
-- 1. Isolate the failing step
have problem_step : A = B := by
  -- 2. Add diagnostic
  trace "Goal: {goal}"
  trace "Context: {localContext}"
  -- 3. Try explicit rewrite chain
  calc
    A = ... := by rw [lemma1]
    _ = ... := by simp only [lemma2, lemma3]
    _ = B   := by ring
  sorry  -- Keep until pattern clear

-- 4. Once pattern clear, implement fix
-- 5. Remove sorry
```

---

## Phase 4: TYPE MISMATCHES (P5) - 1-2 hours

### Context

These are `simpa` failures where the simplified result doesn't match expected type.

### Step 4.1: Fix sumIdx_reduce_by_diagonality_right (Line 1998) - 15 min

**Current code**:
```lean
lemma sumIdx_reduce_by_diagonality_right
    (M r θ : ℝ) (b : Idx) (K : Idx → ℝ) :
  sumIdx (fun e => g M e b r θ * K e) = g M b b r θ * K b := by
  simpa [g_symm_JP] using
    (sumIdx_reduce_by_diagonality M r θ b (fun e => K e))
```

**Fix**:
```lean
lemma sumIdx_reduce_by_diagonality_right
    (M r θ : ℝ) (b : Idx) (K : Idx → ℝ) :
  sumIdx (fun e => g M e b r θ * K e) = g M b b r θ * K b := by
  have h := sumIdx_reduce_by_diagonality M r θ b (fun e => K e)
  -- h : sumIdx (fun e => g M b e r θ * K e) = g M b b r θ * K b
  have swap : ∀ e, g M e b r θ = g M b e r θ := fun e => g_symm_JP M r θ e b
  calc
    sumIdx (fun e => g M e b r θ * K e)
        = sumIdx (fun e => g M b e r θ * K e) := by
          apply sumIdx_congr; intro e; rw [swap e]
    _ = g M b b r θ * K b := h
```

---

### Step 4.2: Fix Branches Sum Type Mismatches (Lines 7925, 7990, 8055, 8120) - 1 hour

**Pattern**: These appear in:
```lean
have ΓΓ_block : ... = bb_core + rho_core_b := by
  classical
  simpa [h_bb_core, h_rho_core_b]
    using ΓΓ_quartet_split_b M r θ μ ν a b
```

**Issue**: The quartet splitter returns one type, `simpa` produces another.

**Fix pattern**:
```lean
have ΓΓ_block : ... = bb_core + rho_core_b := by
  classical
  have q := ΓΓ_quartet_split_b M r θ μ ν a b
  -- q : [actual type from quartet_split_b]
  simp only [h_bb_core, h_rho_core_b] at q
  -- Now q should match goal
  exact q

-- Or use calc for explicit transformation:
have ΓΓ_block : ... = bb_core + rho_core_b := by
  classical
  have q := ΓΓ_quartet_split_b M r θ μ ν a b
  calc
    LHS = [quartet_split_b_RHS] := q
    _ = bb_core + rho_core_b := by
        simp only [h_bb_core, h_rho_core_b]
```

---

### Step 4.3: Fix Ricci Identity Type Mismatch (Line 8570) - 15 min

**Current code**:
```lean
have def_rθ : nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
            = dCoord Idx.r (fun r θ => nabla_g M r θ Idx.θ a b) r θ := rfl
```

**If this doesn't typecheck**:

**Fix**: Add explicit `show`:
```lean
have def_rθ : nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
            = dCoord Idx.r (fun r θ => nabla_g M r θ Idx.θ a b) r θ := by
  show dCoord Idx.r (fun r θ => nabla_g M r θ Idx.θ a b) r θ
     = dCoord Idx.r (fun r θ => nabla_g M r θ Idx.θ a b) r θ
  rfl
```

---

## Phase 5: REWRITE FAILURES & SIMP NO PROGRESS (P6-P7) - 1 hour

### Step 5.1: Fix Core Rewrite Failures (Lines 7994, 8124) - 30 min

**Covered in Phase 3, Step 3.3** - these are actually part of branches_sum.

---

### Step 5.2: Fix Simp No Progress (Lines 8542, 8550, 8622, 8630) - 30 min

**Current pattern**:
```lean
have hμν :
  Gamma_mu_nabla_nu M r θ Idx.r Idx.θ a b = 0 := by
  have hza1 := nabla_g_zero_ext M r θ h_ext Idx.θ a b
  have hza2 := nabla_g_zero_ext M r θ h_ext Idx.θ b a
  unfold Gamma_mu_nabla_nu
  simp only [hza1, hza2]
  ring
```

**Issue**: `simp only [hza1, hza2]` makes no progress because:
- `Gamma_mu_nabla_nu` definition hasn't been fully expanded
- Or the nabla_g terms are nested and simp doesn't reach them

**Fix**:
```lean
have hμν :
  Gamma_mu_nabla_nu M r θ Idx.r Idx.θ a b = 0 := by
  have hza1 := nabla_g_zero_ext M r θ h_ext Idx.θ a b
  have hza2 := nabla_g_zero_ext M r θ h_ext Idx.θ b a
  unfold Gamma_mu_nabla_nu
  -- Explicitly rewrite instead of simp
  rw [hza1, hza2]
  ring

-- Or fully expand first:
have hμν :
  Gamma_mu_nabla_nu M r θ Idx.r Idx.θ a b = 0 := by
  have hza1 := nabla_g_zero_ext M r θ h_ext Idx.θ a b
  have hza2 := nabla_g_zero_ext M r θ h_ext Idx.θ b a
  show sumIdx (fun ρ => ... * nabla_g ... + ... * nabla_g ...) = 0
  simp only [hza1, hza2, mul_zero]
  exact sumIdx_zero
```

---

## Phase 6: VERIFICATION & CLEANUP

### Step 6.1: Build Verification

After each phase, run:
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | tee build_phase_N.txt
grep "^error:" build_phase_N.txt | wc -l
```

Expected progression:
- **After Phase 1**: ~27-29 errors
- **After Phase 2**: ~21-23 errors
- **After Phase 3**: ~10-12 errors
- **After Phase 4**: ~3-6 errors
- **After Phase 5**: 0 errors ✅

---

### Step 6.2: Remove Diagnostic Comments

Search for and remove:
```bash
grep -n "sorry\|DIAGNOSTIC\|FIXME\|TODO" Riemann.lean
```

---

### Step 6.3: Final Build & Commit

```bash
# Clean build
lake clean
lake build Papers.P5_GeneralRelativity.GR.Riemann

# If successful:
git add Riemann.lean
git commit -m "fix: eliminate all 33 remaining errors after recursion fixes

Applied systematic fixes across 6 categories:
- Unicode parser errors (ASCII conversion)
- Missing sumIdx_pick_one lemma implementation
- Quartet splitter signature adapters
- Branches sum intermediate calc steps
- Type mismatch explicit rewrites
- Simp-to-rewrite conversions

File now compiles successfully with 0 errors.

Fixes complete the recursion elimination work from ca01ea2.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>"
```

---

## Appendix A: Diagnostic Commands

### Check Error Distribution
```bash
lake build 2>&1 | grep "^error:" | awk -F: '{print $3}' | sort | uniq -c
```

### Find Specific Error Types
```bash
# Unsolved goals
lake build 2>&1 | grep "unsolved goals" | wc -l

# Type mismatches
lake build 2>&1 | grep "Type mismatch" | wc -l

# Missing identifiers
lake build 2>&1 | grep "Unknown identifier" | wc -l
```

### Track Progress
```bash
# Create progress log
echo "$(date): $(lake build 2>&1 | grep '^error:' | wc -l) errors" >> progress.log
```

---

## Appendix B: Common Tactics Reference

### When `simpa` Fails
1. **Split it**: `have h := lemma; simp only [...] at h; exact h`
2. **Explicit calc**: Replace with calc chain
3. **Add show**: `show [explicit_type]; simpa [...]`

### When `ring` Fails
1. **Expand defs**: `unfold X Y; ring`
2. **Manual steps**: Break into smaller `have` statements
3. **Field_simp first**: `field_simp; ring`

### When `rw` Fails
1. **Check direction**: Try `rw [← lemma]` or `rw [lemma]`
2. **Pattern not found**: Add intermediate rewrites to match pattern
3. **Use conv**: `conv_lhs => rw [lemma]` for surgical rewrite
4. **Generalize first**: `generalize hx : X = x; rw [lemma]; exact ...`

### When Goal Unclear
1. **Add sorry**: See expected type
2. **Add trace**: `trace "{goal}"` in tactic
3. **Check context**: `trace "{localContext}"`

---

## Appendix C: Estimated Timeline

**Conservative estimate (first-time implementation)**:
- Phase 1 (Blocking): 20 min
- Phase 2 (Quartet): 2 hours
- Phase 3 (Branches): 3 hours
- Phase 4 (Types): 1.5 hours
- Phase 5 (Misc): 1 hour
- Phase 6 (Verify): 30 min
**Total: ~8 hours**

**Optimistic estimate (if patterns clear)**:
- Phase 1: 15 min
- Phase 2: 1 hour
- Phase 3: 2 hours
- Phase 4: 1 hour
- Phase 5: 30 min
- Phase 6: 30 min
**Total: ~5 hours**

**Most likely**: 6-7 hours of focused work, spread over 1-2 days.

---

**Prepared by**: Claude Code (Sonnet 4.5)
**Date**: October 27, 2025
**Status**: Ready for execution
**Next step**: Begin Phase 1 (blocking errors)

---

**END OF FIX PLAN**
