# Report to Junior Tactics Professor - October 7, 2025

## Subject: Simp Recursion Depth Issues in Component Lemma Proofs

Dear Junior Professor,

I encountered critical tactical issues while implementing the 7 surgical fixes you provided for the Riemann component lemmas. This report documents the problems and seeks your guidance.

---

## Summary

**Status**: All 7 component lemmas reverted to `sorry` (build compiles successfully)
**Root Cause**: Maximum recursion depth errors when multiple component lemmas have full proofs
**Key Issue**: Simp tactics that work in isolation fail when all 7 lemmas are proven simultaneously

---

## The 7 Target Lemmas

```lean
1. RiemannUp_r_trt_ext  : R^r_{trt} = -2M·f(r)/r³
2. RiemannUp_t_θtθ_ext  : R^t_{θtθ} = -M/r
3. RiemannUp_r_θrθ_ext  : R^r_{θrθ} = -M/r
4. RiemannUp_φ_θφθ_ext  : R^φ_{θφθ} = 2M/r
5. RiemannUp_t_φtφ_ext  : R^t_{φtφ} = -M·sin²θ/r
6. RiemannUp_r_φrφ_ext  : R^r_{φrφ} = -M·sin²θ/r
7. RiemannUp_θ_φθφ_ext  : R^θ_{φθφ} = 2M·sin²θ/r
```

---

## Timeline of Tactical Attempts

### Initial Success (Lemmas in Isolation)

When testing **one lemma at a time** with remaining 6 at `sorry`, your surgical fixes worked:

**Fix 1 Pattern (RiemannUp_r_trt_ext)**:
```lean
have hder' : deriv (fun s => Γ_r_tt M s) r = -(2*M)*(r-3*M)/r^4 := by
  simpa [Γ_r_tt, div_eq_mul_inv] using deriv_Γ_r_tt_at M r hr
have hrel : Γ_r_rr M r = -Γ_t_tr M r := by simp [Γ_r_rr, Γ_t_tr]; ring
simp [hder', hrel]
simp only [f]
field_simp [hr, pow_two]
ring
```
✅ **Result**: Compiled successfully when Fix 1 alone was proven

**Fix 2/3 Pattern (θθ diagonal cases)**:
```lean
have hflip : 2 * M - r = -(r - 2 * M) := by ring
simp [hflip]
simp only [f]
field_simp [hr, hsub, pow_two]
ring
```
✅ **Result**: Each compiled successfully in isolation

**Fix 5/6 Pattern (φφ diagonal cases)**:
```lean
have hneg2 : -(M * 2) + r = r - 2 * M := by ring
simp [hneg2]
simp only [f]
field_simp [hr, hsub, pow_two]
ring
```
✅ **Result**: Each compiled successfully in isolation

---

### Catastrophic Failure (All 7 Lemmas Proven)

When all 7 lemmas had full proofs, the build failed with:

#### Error Type 1: Maximum Recursion Depth

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2038:2:
Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
```

**Locations**: Lines 2038, 2077, 2095 (all using `simp [hflip]` or `simp [hneg2]`)

#### Error Type 2: Pattern Not Found (when using `rw` instead)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2077:2:
Tactic `rewrite` failed: Did not find an occurrence of the pattern
  2 * M - r
in the target expression
```

**Attempted fix**: Changed `simp [hflip]` → `rw [hflip]`
**Result**: Pattern matching failed

#### Error Type 3: Unsolved Goals (when using `simp only`)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2024:73: unsolved goals
M r θ : ℝ
h_ext : Exterior M r θ
hr : r ≠ 0
hder' : deriv (fun s => Γ_r_tt M s) r = -(2 * M) * (r - 3 * M) / r ^ 4
hrel : Γ_r_rr M r = -Γ_t_tr M r
⊢ ... (complex algebraic goal)
```

**Attempted fix**: Changed `simp [hder', hrel]` → `simp only [hder', hrel, f]`
**Result**: Goal did not close

---

## Root Cause Analysis

### Hypothesis: Simp Lemma Interference

When multiple component lemmas are proven, Lean's `simp` mechanism may be:

1. **Auto-applying proven lemmas**: The proven `RiemannUp_*_ext` lemmas might be getting applied during simplification in other lemmas' proofs
2. **Creating circular dependencies**: Simp tries to use lemma A while proving lemma B, which tries to use lemma B while proving lemma A
3. **Exponential search space**: With 7 similar lemmas available, simp explores too many rewrite paths

### Evidence

**Working Cases**:
- Lemmas `RiemannUp_θ_tθt_ext` and `RiemannUp_φ_tφt_ext` (lines 2043-2061) work perfectly with simple pattern:
  ```lean
  unfold RiemannUp
  simp [dCoord, sumIdx_expand, Γtot, Γ_θ_rθ, Γ_r_tt, Γ_t_tr, Γ_r_rr]
  field_simp [hr, f]
  ```
- These lemmas were already proven before attempting the 7 surgical fixes
- They don't use helper lemmas like `hflip` or `hneg2`

**Failing Pattern**:
- All 7 target lemmas use local helper lemmas (`hflip`, `hneg2`, `hder'`, `hrel`)
- All 7 use pattern: `simp [helper_lemma]` followed by `simp only [f]`
- This two-stage simp approach seems to trigger recursion

---

## Specific Technical Issues

### Issue 1: `simp [hflip]` Recursion

**Location**: Lines 2077, 2095
**Code**:
```lean
have hflip : 2 * M - r = -(r - 2 * M) := by ring
simp [hflip]  -- ← RECURSION DEPTH ERROR
```

**Observation**: This exact pattern works when lemma is solo, fails when all 7 are proven

### Issue 2: `rw [hflip]` Pattern Not Found

**Attempted Fix**:
```lean
have hflip : 2 * M - r = -(r - 2 * M) := by ring
rw [hflip]  -- ← PATTERN NOT FOUND
```

**Error**: The goal has `2*M - r` in some algebraic context, but `rw` can't match it
**Reason**: After `simp [dCoord, sumIdx_expand, Γtot, ...]`, the goal is heavily simplified and `2*M - r` may be nested or transformed

### Issue 3: `simp only [hflip, f]` Unsolved Goals

**Attempted Fix**:
```lean
have hflip : 2 * M - r = -(r - 2 * M) := by ring
simp only [hflip, f]  -- ← GOAL DOESN'T CLOSE
field_simp [hr, hsub, pow_two]
ring
```

**Error**: Unsolved algebraic goals remain after `simp only`
**Reason**: `simp only` is too restrictive, doesn't apply necessary algebraic simplifications that `simp` would

---

## Questions for Junior Professor

### Q1: Simp Discipline Strategy

When building a library of similar component lemmas, what's the recommended approach?

**Option A**: Prove lemmas sequentially, each building on previous?
**Option B**: Use `@[simp]` attributes selectively to control auto-application?
**Option C**: Avoid `simp` entirely in proofs, use only `rw`/`field_simp`/`ring`?
**Option D**: Something else?

### Q2: Local Helper Lemmas

The pattern:
```lean
have hflip : 2 * M - r = -(r - 2 * M) := by ring
simp [hflip]
```

Should this be:
```lean
conv_lhs => arg ...; rw [hflip]  -- Target specific subterm?
```
or:
```lean
rw [show 2*M - r = -(r-2*M) by ring]  -- Inline helper?
```
or:
```lean
-- Just accept the simp recursion and increase maxRecDepth?
set_option maxRecDepth 10000
```

### Q3: Two-Stage Simp Pattern

Your fixes use:
```lean
simp [dCoord, sumIdx_expand, Γtot, ...]  -- Stage 1: Structural
simp [hflip]                               -- Stage 2: Normalize algebra
simp only [f]                              -- Stage 3: Expand f
field_simp [hr, hsub, pow_two]            -- Stage 4: Clear denominators
ring                                       -- Stage 5: Close
```

Is there a way to combine stages to avoid intermediate simp states that might trigger lemma application?

For example:
```lean
simp only [dCoord, sumIdx_expand, Γtot, ..., hflip, f]  -- All at once?
field_simp [hr, hsub, pow_two]
ring
```

### Q4: The `simpa` vs `simp; tactic` Distinction

In Fix 1, you used:
```lean
have hder' : ... := by
  simpa [Γ_r_tt, div_eq_mul_inv] using deriv_Γ_r_tt_at M r hr
```

I had to change this from `simpa` to `simp [...]; ring` due to `assumption` tactic failure. Is there a tactical principle here about when `simpa` vs `simp; tactic` should be used?

---

## Current Workaround

All 7 lemmas set to `sorry`:
```lean
lemma RiemannUp_r_trt_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.r Idx.t Idx.r Idx.t = -(2*M)*(f M r)/r^3 := by
  sorry
```

**Build Status**: ✅ 0 errors, 7 sorries

---

## Request for Guidance

Could you provide:

1. **Tactical Strategy**: How to sequence these 7 proofs to avoid simp recursion?
2. **Revised Patterns**: Alternative proof patterns that avoid the `simp [helper]` recursion issue?
3. **Simp Configuration**: Any `set_option` or `attribute` settings needed?
4. **Proof Order**: Should these be proven in a specific order (e.g., Fix 1 → Fix 2 → ... → Fix 7)?

I'm happy to implement any revised approach you recommend. The mathematical content of the fixes is sound (each works in isolation), but the tactical interaction when all 7 are present needs expert guidance.

---

## Technical Environment

- **Lean Version**: 4.x (using `lake build`)
- **File**: `GR/Riemann.lean` (3,427 lines)
- **Context**: ~2000 lines of infrastructure before these lemmas
- **Existing Simp Lemmas**: ~150 `@[simp]` lemmas already in scope

---

## Appendix: Full Code Snapshot

**Working Lemma (for comparison)**:
```lean
/-- R^θ_{tθt} = M·f(r)/r³ for Schwarzschild exterior region -/
lemma RiemannUp_θ_tθt_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.θ Idx.t Idx.θ Idx.t = M * f M r / r^3 := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  unfold RiemannUp
  simp [dCoord, sumIdx_expand, Γtot, Γ_θ_rθ, Γ_r_tt, Γ_t_tr, Γ_r_rr]
  field_simp [hr, f]
```
✅ **This works and has been working since earlier sessions**

**Failed Lemma (Fix 2 example)**:
```lean
/-- R^t_{θtθ} = -M/r for Schwarzschild exterior region -/
lemma RiemannUp_t_θtθ_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.t Idx.θ Idx.t Idx.θ = -M/r := by
  classical
  have hr   : r ≠ 0     := Exterior.r_ne_zero h_ext
  have hsub : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]

  unfold RiemannUp
  simp [dCoord, sumIdx_expand, Γtot, Γ_t_tr, Γ_r_θθ]

  have hflip : 2 * M - r = -(r - 2 * M) := by ring
  simp [hflip]  -- ← RECURSION DEPTH ERROR when all 7 proven

  simp only [f]
  field_simp [hr, hsub, pow_two]
  ring
```
❌ **Recursion depth error (but only when all 7 lemmas have proofs)**

---

Thank you for your expertise. I await your tactical guidance.

Best regards,
Claude Code Assistant

**Date**: October 7, 2025
**Session**: Continuation from Oct 6 handoff
**Commit**: Currently uncommitted (all at `sorry`)
