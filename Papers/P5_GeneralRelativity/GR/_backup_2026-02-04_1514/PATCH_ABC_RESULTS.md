# Patch A+B+C Implementation Report

**Date:** October 4, 2025
**To:** Junior Professor
**Re:** Compilation Timeout Investigation - Patches A, B, C Applied

---

## Executive Summary

All three surgical patches (A, B, C) have been successfully applied to `Riemann.lean`, but **the compilation still times out after 2+ minutes**. Critical discovery: The `dCoord_g_via_compat_ext` fallback is **NOT the bottleneck** - even replacing it with `sorry` still causes a timeout. The expensive operation is occurring elsewhere in the file.

---

## Patches Applied

### ✅ Patch A: Remove Global @[simp] from Γ-Projection Lemmas

**Status:** Successfully applied
**Method:** Used `sed` to remove `@[simp]` attribute from 45 Γtot adapter lemmas
**Verification:**
```bash
$ grep "^@\[simp\] lemma Γtot" GR/Riemann.lean | wc -l
0
```

**Lines affected:** 138-182 (approximately)

**Before:**
```lean
@[simp] lemma Γtot_t_tt (M r θ : ℝ) : Γtot M r θ Idx.t Idx.t Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_tr (M r θ : ℝ) : Γtot M r θ Idx.t Idx.t Idx.r = 0 := by simp [Γtot]
... (43 more lemmas)
```

**After:**
```lean
lemma Γtot_t_tt (M r θ : ℝ) : Γtot M r θ Idx.t Idx.t Idx.t = 0 := by simp [Γtot]
lemma Γtot_t_tr (M r θ : ℝ) : Γtot M r θ Idx.t Idx.t Idx.r = 0 := by simp [Γtot]
... (43 more lemmas)
```

**Impact:** Reduced global simp saturation, but build still times out.

---

### ✅ Patch B: Demote Heavy Helper Lemmas from Global @[simp]

**Status:** Successfully applied
**Method:** Used `sed` to remove `@[simp]` from 4 heavy helper lemmas
**Lemmas affected:**
1. `dCoord_sumIdx` (line ~832)
2. `sumIdx_Γ_g_left` (line ~1329)
3. `sumIdx_Γ_g_right` (line ~1338)
4. `nabla_g_shape` (line ~1365)

**Verification:**
```bash
$ grep -n "^@\[simp\] lemma dCoord_sumIdx\|^@\[simp\] lemma sumIdx_Γ_g_left\|^@\[simp\] lemma sumIdx_Γ_g_right\|^@\[simp\] lemma nabla_g_shape" GR/Riemann.lean
(no output - all removed)
```

**Impact:** Further reduced simp saturation, but build still times out.

---

### ⚠️ Patch C: Optimize dCoord_g_via_compat_ext Fallback

**Status:** Applied multiple variants - **NONE resolved the timeout**
**Location:** Lines 1635-1643 in `dCoord_g_via_compat_ext`

#### Variant 1: Original State (before Route A)
```lean
| { dsimp only [g]; simp [dCoord_t, dCoord_φ, sumIdx_expand, Γtot] }
```
**Result:** Build times out after 2+ minutes
**Profiler:** `simp 14.8s` (cumulative across file)

#### Variant 2: Added ring normalization
```lean
| {
    dsimp only [g]
    simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, deriv_const]
    simp only [sumIdx_expand, g]
    simp only [Γtot, Γ_t_tr, Γ_r_tt, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ, f]
    ring
  }
```
**Result:** Build times out after 2+ minutes
**Profiler:** `simp 12.1s, ring 747ms`
**Errors:** 45 unsolved goals (arithmetic not closed)

#### Variant 3: Minimal simp + ring
```lean
| { dsimp only [g]; simp [dCoord_t, dCoord_φ, sumIdx_expand, Γtot]; ring }
```
**Result:** Build times out after 2+ minutes
**Profiler:** `simp 13s, ring 667ms`

#### Variant 4: Only dsimp + ring (no simp)
```lean
| {
    dsimp only [g, dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, sumIdx_expand, Γtot,
                Γ_t_tr, Γ_r_tt, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ, f, deriv_const]
    ring
  }
```
**Result:** Build times out after 2+ minutes
**Profiler:** `simp 10.6s, ring 1.04s`
**Errors:** Unsolved goals (dsimp doesn't unfold deriv_const lemma)

#### Variant 5: Complete removal (sorry)
```lean
| sorry
```
**Result:** **BUILD STILL TIMES OUT AFTER 2+ MINUTES!**
**Profiler:** Not captured (timed out)

---

## Critical Discovery

**The fallback in `dCoord_g_via_compat_ext` is NOT the bottleneck.**

Even with the entire fallback replaced by `sorry`, the compilation still hangs for 2+ minutes before timing out. This proves that:

1. The expensive operation is **not** in the fallback block
2. The 9 explicit `compat_*_ext` lemmas (lines 1624-1633) are not the issue either
3. The bottleneck must be **downstream** - in code that USES `dCoord_g_via_compat_ext`

---

## Triage with #exit

Tested compilation up to line 1640 (right after `dCoord_g_via_compat_ext`):

```lean
#exit  -- TRIAGE: Does dCoord_g_via_compat_ext hang?
```

**Result with original fallback:** Compiled in **~10 seconds** with warnings but no timeout
**Result with sorry fallback:** Compiled in **~10 seconds** with warnings but no timeout

**Conclusion:** The lemma `dCoord_g_via_compat_ext` itself is fast. The timeout occurs when compiling code AFTER line 1640.

---

## Profiler Analysis

Cumulative profiling times (from run with #exit at line 1640):

```
simp                     14.8s  ← Still expensive globally
tactic execution         4.16s
typeclass inference      2.96s
ring                     224ms
linting                  956ms
type checking            755ms
```

**Key observation:** `simp` takes 14.8 seconds cumulatively across the file, even though we removed ~50 global `@[simp]` lemmas. This suggests:
- Other simp-heavy proofs exist elsewhere in the file
- Simp is being called on large expressions repeatedly
- The global simp set may still contain expensive lemmas we haven't identified

---

## Hypothesis: Downstream Usage

Lemmas that likely USE `dCoord_g_via_compat_ext`:

1. **`nabla_g_zero_ext`** (line ~1642):
   ```lean
   lemma nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (c a b : Idx) :
     nabla_g M r θ c a b = 0 := by
     simp only [nabla_g]
     rw [dCoord_g_via_compat_ext M r θ h_ext]
     abel
   ```
   This lemma rewrites using `dCoord_g_via_compat_ext`, then uses `abel`.

2. **`dCoord_nabla_g_zero_ext`** (line ~1654):
   Uses `nabla_g_zero_ext`, which transitively depends on `dCoord_g_via_compat_ext`.

3. **Chart-based versions** (lines ~1750+):
   `dCoord_g_via_compat_chart`, `nabla_g_zero_chart`, etc. - similar structure

4. **Riemann tensor computation** (lines 2000+):
   May use the nabla_g lemmas extensively

---

## Questions for Junior Professor

### Q1: Is there a known expensive lemma downstream?

Are there specific lemmas after line 1640 that are known to be slow? The profiler shows `simp` is expensive globally, but we haven't isolated which specific lemma causes the hang.

### Q2: Should we add local simp sections?

Your Patch A suggestion mentioned:
> "If proofs downstream break, add a local `attribute [simp]` section just for those proofs."

Should we:
1. Create a `section LocalΓSimp` around specific proofs that need the Γ lemmas?
2. If so, which proofs need them?

### Q3: Are the compat_*_ext lemmas themselves expensive?

The 9 explicit compat lemmas (lines 1624-1633):
- `compat_r_tt_ext`
- `compat_r_rr_ext`
- `compat_r_θθ_ext`
- `compat_r_φφ_ext`
- `compat_θ_φφ_ext`
- `compat_t_tr_ext`
- `compat_θ_rθ_ext`
- `compat_φ_rφ_ext`
- `compat_φ_θφ_ext`

Do any of these use expensive tactics (like `field_simp`)? Should we check their definitions?

### Q4: Route A vs git HEAD

Current situation:
- **Route A with Patches A+B+C:** Times out (2+ minutes)
- **git HEAD:** Has 14 compilation errors but might give us clues

Should we:
1. Revert to git HEAD and fix the 14 errors one by one?
2. Continue debugging Route A by binary searching for the bottleneck?
3. Check if the Chart-based versions (line 1750+) are causing issues?

---

## Binary Search Strategy

If you'd like me to continue investigating, I can:

1. **Add #exit at line 1700** to see if it compiles quickly
2. **Move #exit progressively** to isolate the exact lemma causing the hang
3. **Profile individual lemmas** with `set_option profiler true in` to find the culprit

---

## File State

**Current backups:**
- `Riemann.lean.modular_backup` - State before any patches
- `Riemann.lean.before_patch_a` - Before Patch A (sed)
- `Riemann.lean.route_a_full` - Full Route A with expensive field_simp fallback

**Current Riemann.lean state:**
- Patches A, B applied ✅
- Fallback = `sorry` (for testing)
- Lines: 5929
- Status: TIMEOUT after 2+ minutes

**Git status:**
```
M GR/Riemann.lean
```

---

## Request

Please advise on next steps:
1. Which direction should we investigate?
2. Are there specific lemmas to check after line 1640?
3. Should we revert Route A and take a different approach?

Thank you for your guidance!

---

**Attachments:**
- Profiler output (available via bash background jobs)
- Backup files in GR/ directory
