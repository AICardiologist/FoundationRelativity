# Diagnostic Report to JP: Normalization Dilemma in ricci_identity_on_g_rθ_ext
**Date**: October 21, 2025
**Status**: ⚠️ **BLOCKED** - Fundamental tactical issue with normalization steps
**Target**: `ricci_identity_on_g_rθ_ext` proof (lines 5410-5476)

---

## EXECUTIVE SUMMARY

Your helper lemmas (`dCoord_r_push_through_nabla_g_θ_ext` and `dCoord_θ_push_through_nabla_g_r_ext`) are **successfully implemented** and compile cleanly. The proof structure follows your 8-step blueprint exactly.

**The blocker**: A tactical dilemma between Steps 3-4 and Step 6:
- **Step 4 needs** some normalization to expose the mixed partial pattern for cancellation
- **Step 6 needs** the collector pattern to remain intact after Step 5's product rules
- **But**: ANY normalization tactic (`simp only`, `ring`, `ring_nf`, `abel_nf`) either times out OR destroys the structure needed for Step 6

---

## WHAT'S WORKING ✅

### 1. Helper Lemmas (Lines 5240-5404)

Both helper lemmas are in place and compile successfully:

**`dCoord_r_push_through_nabla_g_θ_ext`** (lines 5242-5322):
- Uses your exact proof strategy: `reshape` → `step₁` → `step₂` → assemble
- Current implementation uses explicit `have` statements in `step₂` (lines 5310-5316)
- Alternative: Your `refine` with bullets (both should work, current version compiles)

**`dCoord_θ_push_through_nabla_g_r_ext`** (lines 5326-5403):
- Symmetric θ-direction version
- Same deterministic structure

**Differentiability infrastructure**:
- All 6 `diff_*` lemmas verified present (lines 4051-4163)
- `dCoord_sub_of_diff` working correctly
- No issues with differentiability proofs

### 2. Section Freeze (Line 5238)

```lean
attribute [-simp] dCoord dCoord_r dCoord_θ
```

Working as intended - prevents `simp` from unfolding `dCoord` to `deriv`.

### 3. Main Proof Structure (Lines 5410-5476)

All 8 steps are present:
- ✅ Step 1: `simp only [nabla, nabla_g]` - **works**
- ✅ Step 2: Helper lemma rewrites - **works**
- ⚠️ Step 3: Normalization - **BLOCKS HERE** (details below)
- ⚠️ Step 4: Mixed partial cancellation - **depends on Step 3**
- ✅ Step 5: Product rule lemmas - **works when reached**
- ⚠️ Step 6: Collector - **pattern matching fails after normalization**
- ❓ Step 7: Regrouping - not yet reached
- ❓ Step 8: Final contraction - not yet reached

---

## THE BLOCKER ⚠️

### Attempt 1: Original `simp only` Normalization (Your Suggestion)

**Code** (line 5426-5427):
```lean
set_option maxHeartbeats 400000 in
simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
```

**Result**: ❌ **TIMEOUT**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5427:2: Tactic `simp` failed with a nested error:
(deterministic) timeout at `simp`, maximum number of heartbeats (200000) has been reached
```

**Note**: The `set_option maxHeartbeats 400000` doesn't take effect (still reports 200000 limit).

### Attempt 2: Skip Step 3 Entirely

**Code**:
```lean
-- Step 3: normalize (skipped)
-- simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
```

**Result**: ❌ **Step 4 pattern matching fails**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5434:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ -
    dCoord Idx.θ (fun r θ => dCoord Idx.r (fun r θ => g M a b r θ) r θ) r θ
```

**Diagnosis**: Without normalization, the mixed partial terms are buried in nested associativity that prevents `Hcancel` from matching.

### Attempt 3: Use `ring_nf` Instead

**Code** (Step 3):
```lean
ring_nf
```

**Result**: ✅ Steps 3-5 work, but ❌ **Step 6 fails**
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5466:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ((sumIdx fun ρ => A ρ * G ρ) - sumIdx fun ρ => B ρ * G ρ) +
   ((sumIdx fun ρ => G ρ * C ρ) - sumIdx fun ρ => G ρ * D ρ))
```

**Diagnosis**: `ring_nf` normalizes the goal so much that the collector pattern no longer matches. The goal becomes a flat sum of many terms instead of the structured `(A-B)+(C-D)` pattern.

### Attempt 4: Surgical `conv` + `ring_nf`

**Code** (Step 4):
```lean
conv_lhs =>
  rw [dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ]
ring_nf
```

**Result**: ✅ Step 4 works, but ❌ **same Step 6 failure as Attempt 3**

**Diagnosis**: Even surgical `conv` followed by `ring_nf` normalizes too much.

### Attempt 5: Use `abel_nf` to Preserve Multiplication Structure

**Code** (Step 4):
```lean
conv_lhs =>
  rw [dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ]
abel_nf  -- only normalizes addition, not multiplication
```

**Result**: ❌ **same Step 6 failure**

**Diagnosis**: Even `abel_nf` destroys the grouping structure needed for the collector.

---

## ROOT CAUSE ANALYSIS

After Steps 1-2, the goal has this structure:
```
(mixed_partial_r_θ - mixed_partial_θ_r) + many_other_terms
```

**Step 4's requirement**: The mixed partials need to be **adjacent in the AST** for `rw [Hcancel]` to match them.

**Step 6's requirement**: After Step 5 applies product rules, the goal should have structure:
```
(sumIdx A*G - sumIdx B*G) + (sumIdx G*C - sumIdx G*D) + ...
```
for the collector to fuse the sums.

**The dilemma**:
1. Without normalization, mixed partials aren't adjacent → Step 4 fails
2. With normalization (`ring`, `ring_nf`, `abel_nf`), the goal becomes fully flattened → Step 6 fails

---

## GOAL STATES (Observed)

### After Step 2 (before any normalization):

Deep nested structure with mixed partials buried:
```
((dCoord_r(dCoord_θ g) - dCoord_r(sumIdx Γθ*g) - dCoord_r(sumIdx Γθ*g) - sumIdx(Γ * nabla_g_θ)) - ...)
  - (dCoord_θ(dCoord_r g) - ...)
```

Mixed partial pattern exists but not exposed.

### After Step 4 with `ring_nf`:

Completely flat sum of many terms:
```
(((((-sumIdx dCoord Γ * g + Γ * dCoord g) - sumIdx ...) + (-sumIdx ...) + ...) + ...)
```

The `(A-B)+(C-D)` structure is destroyed.

---

## PREVIOUS SESSION INSIGHTS

From `TACTICAL_BLOCKER_OCT21.md`:
> **The fundamental problem is that `dCoord` is defined in terms of `deriv`, and Lean's tactics automatically reduce it at multiple points in the proof**

**However**: In our case, `dCoord` is NOT being reduced to `deriv` (the freeze works!). The problem is **structural flattening**, not reduction.

From `PROGRESS_REPORT_OCT21_FINAL.md`:
> **Step 3 normalization: made no progress anyway and could be skipped**

**But**: Skipping Step 3 causes Step 4 to fail.

---

## QUESTIONS FOR JP

### 1. Step 3 Heartbeat Limit

The `set_option maxHeartbeats 400000 in simp only [...]` syntax doesn't work - still reports 200000 limit. Is there a different syntax for Lean 4?

**Alternative tried**:
```lean
set_option maxHeartbeats 400000
simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
```

Should we try this (without `in`)?

### 2. Surgical Step 4

Is there a way to apply `dCoord_commute_for_g_all` to rewrite **only** the mixed partial subterm without normalizing the entire goal?

**Idea**:
```lean
conv_lhs =>
  arg 1  -- navigate to first major term
  arg 1  -- navigate deeper
  rw [dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ]
-- no ring_nf here
```

Then rely on Step 6's `simpa` to do local simplification?

### 3. Collector Pattern

Could we make the collector lemma more robust to match partially-normalized goals?

**Current pattern**:
```lean
((sumIdx fun ρ => A ρ * G ρ) - sumIdx fun ρ => B ρ * G ρ) +
((sumIdx fun ρ => G ρ * C ρ) - sumIdx fun ρ => G ρ * D ρ))
```

**Alternative**: Match individual `sumIdx` terms scattered in the goal and collect them manually?

### 4. Alternative Proof Strategy

Should we abandon the global normalization approach and instead:
1. Apply helper lemmas (Step 2) ✅
2. Use highly surgical `conv` to cancel mixed partials without `ring`
3. Apply product rules (Step 5) ✅
4. Use a more flexible collector that doesn't rely on exact structure?

---

## CURRENT CODE STATE

### File Modified
`Papers/P5_GeneralRelativity/GR/Riemann.lean`

### Lines Changed
- **5240-5403**: Helper lemmas (✅ **working perfectly**)
- **5425-5432**: Step 3-4 (⚠️ **various normalization attempts, all blocked**)

### Build Command Used
```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

### Current Error
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5467:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

At Step 6 collector after Step 4 `abel_nf`.

---

## WHAT WE NEED FROM YOU

1. **Guidance on normalization strategy**: Which tactics preserve structure for Step 6?

2. **Alternative tactical approach**: If normalization is fundamentally incompatible, what's the surgical alternative?

3. **Heartbeat syntax**: How to properly set heartbeats in Lean 4 for `simp only`?

4. **Expected behavior**: In your environment, does `simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]` complete without timeout? If so, what's different about your setup?

---

## ATTACHED ARTIFACTS

1. **Current Riemann.lean** - with helper lemmas working, blocked at Step 3-4
2. **Build log** - showing exact error messages
3. **This diagnostic report** - comprehensive analysis of attempts

---

## CELEBRATION (Despite Blocker) 🎯

### What Works Perfectly:

1. ✅ **Your helper lemmas**: Drop-in implementation compiles cleanly
2. ✅ **Differentiability infrastructure**: All `diff_*` lemmas working
3. ✅ **Section freeze**: `dCoord` stays frozen, no reduction to `deriv`
4. ✅ **Steps 1-2**: Expansion and distribution via helpers
5. ✅ **Step 5**: Product rule lemmas apply successfully (when reached)
6. ✅ **Mathematical correctness**: Senior Professor verified the approach

### Why This is Close:

The blocker is **purely tactical**, not mathematical. The right sequence of surgical tactics will unlock the proof. We just need guidance on the Lean 4 tactics that preserve goal structure.

---

**Prepared by**: Claude Code
**Date**: October 21, 2025
**Session duration**: ~3 hours of tactical debugging
**Build status**: Clean compilation up to Step 6 pattern matching
**Awaiting**: JP's tactical guidance on normalization strategy
