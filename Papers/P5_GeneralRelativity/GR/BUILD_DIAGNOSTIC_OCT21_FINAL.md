# Build Diagnostic Report: JP's Surgical Approach
**Date**: October 21, 2025
**Status**: ❌ **BUILD FAILED** - Pattern matching issues at Step 6
**Progress**: 70% complete (Steps 1-5.5 working)

---

## EXECUTIVE SUMMARY

JP's surgical approach was implemented as specified, but encounters a fundamental pattern-matching issue. The build fails at Step 6 with multiple different errors depending on the approach attempted.

### ✅ What Works Perfectly:

1. **Flatten helpers** (`flatten₄₁` and `flatten₄₂`) - compile cleanly (lines 296-304)
2. **Steps 1-5** - all execute successfully:
   - Step 1: `simp only [nabla, nabla_g]` ✅
   - Step 2: Helper lemma rewrites ✅
   - Step 5: Product rule distribution ✅
   - Step 5.5: `simp [group_sub_add]` ✅ (line 5463)

### ❌ Current Blocker:

**Step 6** (lines 5468-5474): **ALL** attempted approaches fail with pattern matching errors:

1. **JP's naming approach**: `simp made no progress` (lines 5495-5496)
2. **Direct flat collector**: Pattern not found (line 5482)
3. **Skip to regrouping**: Pattern not found (line 5472)

---

## DETAILED DIAGNOSTIC

### Approach 1: JP's S₁...S₄ Naming Approach

**Code attempted** (lines 5480-5497):
```lean
set S₁ := sumIdx (fun ρ => A ρ * G ρ) with hS₁
set S₂ := sumIdx (fun ρ => B ρ * G ρ) with hS₂
set S₃ := sumIdx (fun ρ => G ρ * C ρ) with hS₃
set S₄ := sumIdx (fun ρ => G ρ * D ρ) with hS₄

have hcollect_flat :
  S₁ - S₂ + S₃ - S₄
    = sumIdx (fun ρ => G ρ * ((A ρ - B ρ) + (C ρ - D ρ))) := by
  simpa [hS₁, hS₂, hS₃, hS₄] using
    (sumIdx_collect_comm_block_flat G A B C D)

simp [hS₁, hS₂, hS₃, hS₄, flatten₄₁, flatten₄₂] at *
simp [hcollect_flat] at *
```

**Results**:
- Line 5495: `error: 'simp' made no progress` (first simp line)
- Line 5496: `error: 'simp' made no progress` (second simp line)

**Variants tried**:
- `simp` without `at *`: Still made no progress
- `simp only [...]`: Still made no progress
- Combined single `simp only`: Still made no progress
- `rw [← hS₁, ← hS₂, ← hS₃, ← hS₄]` after flatten: Pattern not found

### Approach 2: Direct Flat Collector (Original Approach)

**Code attempted** (lines 5480-5482):
```lean
have hcollect := sumIdx_collect_comm_block_flat G A B C D
simp [G, A, B, C, D] at hcollect
rw [hcollect]
```

**Error**:
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (((sumIdx fun ρ => dCoord Idx.r ... * g M ρ b r θ) - ...) + ...) - ...
```

**Root cause**: The goal has `g M ρ b r θ` **expanded** to a match statement:
```lean
(match (motive := Idx → Idx → ℝ → ℝ → ℝ) ρ, b with
  | t, t => fun r _θ => -f M r
  | Idx.r, Idx.r => fun r _θ => (f M r)⁻¹
  | Idx.θ, Idx.θ => fun r _θ => r ^ 2
  | φ, φ => fun r θ => r ^ 2 * sin θ ^ 2
  | x, x_1 => fun x x => 0)
  r θ
```

But the collector lemma has `g M ρ b r θ` in folded form.

**Variant tried**:
```lean
simp only [G, A, B, C, D, g] at hcollect  -- expand g in the lemma
simp only [hcollect]
```

**Result**: `error: 'simp' made no progress` - Even with g expanded, patterns don't match.

### Approach 3: Skip Collector, Go Direct to Regrouping

**Code attempted** (lines 5470-5474):
```lean
have packR := regroup_right_sum_to_RiemannUp M r θ h_ext h_θ a b
have packL := regroup_left_sum_to_RiemannUp  M r θ h_ext h_θ a b
rw [packR, packL]
simp [sumIdx_RiemannUp_mul_g_collapse M r θ a b]
ring
```

**Error**: Line 5472: `error: Tactic 'rewrite' failed: Did not find an occurrence of the pattern`

**Diagnosis**: The regrouping lemmas also can't match the goal structure after `simp [group_sub_add]`.

---

## ROOT CAUSE ANALYSIS

### The Core Issue: `g` Function Expansion

After `simp [group_sub_add]` at line 5463, something (likely simp itself or an earlier step) causes the `g M ρ b r θ` function to **unfold** to its match-statement definition.

**Evidence**:
1. Error message shows expanded match statement in goal
2. Collector lemma has `g M ρ b r θ` in folded form
3. Even after expanding g in the lemma with `simp [g]`, patterns don't match

### Why All Approaches Fail

1. **flatten₄₁/flatten₄₂**: These only handle parenthesization, not term structure. If the goal has fundamentally different terms (expanded g vs folded g), they can't help. `simp made no progress` means the goal doesn't have the pattern `((x₁ - x₂) + x₃) - x₄` at all.

2. **Naming approach (set S₁...)**: The `set` tactic creates **local definitions** but doesn't automatically fold/substitute in the goal. To fold sumIdx terms into S₁ in the goal, we need to rewrite with `← hS₁`, but this also fails to find the pattern (because g is expanded).

3. **Direct collector**: Can't match because g is in different form in goal vs lemma.

4. **Regrouping lemmas**: Also expect specific structure that the expanded goal doesn't have.

### Why `simp [group_sub_add]` Might Expand `g`

The `group_sub_add` lemma is:
```lean
@[simp] lemma group_sub_add (x y z : ℝ) : x - (y + z) = (x - y) - z
```

When simp applies this, it may also apply other simp lemmas transitively, including potentially unfolding `g` if there's a simp lemma about g or if simp decides to reduce definitions.

---

## HYPOTHESES FOR WHY THE GOAL IS MALFORMED

### Hypothesis 1: `group_sub_add` is Too Aggressive

Using `simp [group_sub_add]` (with full simp, not `simp only`) allows simp to apply any simp-tagged lemmas it can find. This might include:
- Auto-simplification of function applications
- Reduction of `g` to its definition
- Other normalization that destroys the structure we need

**Test**: Try `simp only [group_sub_add]` instead of `simp [group_sub_add]`.

### Hypothesis 2: Earlier Steps Already Expanded `g`

Maybe `g` was already expanded before Step 5.5, and `simp [group_sub_add]` just preserved that.

**Test**: Add `sorry` right after Step 5 (before `simp [group_sub_add]`) and check if g is already expanded.

### Hypothesis 3: The Product Rule Lemmas Expand `g`

The product rule lemmas (Step 5) might expand `g` as a side effect.

**Test**: Check if g is expanded after Step 5 but before Step 5.5.

### Hypothesis 4: `g` Needs to Be Frozen

Similar to how we froze `dCoord` with `attribute [-simp]`, maybe `g` also needs to be frozen.

**Test**: Add `attribute [-simp] g` before the proof or in the section.

---

## ATTEMPTED FIXES (All Failed)

### Fix 1: Remove `at *` from simp
**Rationale**: `at *` rewrites in hypotheses too, might cause issues
**Result**: Still `simp made no progress`

### Fix 2: Use `simp only` for determinism
**Rationale**: More predictable than full simp
**Result**: Still `simp made no progress`

### Fix 3: Combine both simp lines into one
**Rationale**: Maybe they need to work together
**Result**: Still `simp made no progress`

### Fix 4: Fold backward with `rw [← hS₁, ...]`
**Rationale**: Explicitly fold sumIdx terms to S₁ notation
**Result**: Pattern not found (can't match expanded g)

### Fix 5: Expand g in the lemma too
**Rationale**: Make both sides have expanded g
**Result**: Still `simp made no progress` (structure still doesn't match)

### Fix 6: Skip collector entirely
**Rationale**: Maybe regrouping can work directly
**Result**: Regrouping patterns also don't match

---

## WHAT WE KNOW WORKS

### Infrastructure (100% Working):

1. ✅ **Flatten helpers** (lines 296-304): Compile cleanly
2. ✅ **Flat collector lemma** (lines 1724-1737): Compiles cleanly
3. ✅ **Helper lemmas** (lines 5240-5403): Working perfectly
4. ✅ **Section freeze** (line 5238): `dCoord` stays frozen
5. ✅ **Steps 1-5.5**: All execute without errors

### Proof Flow (70% Complete):

```
Step 1: simp only [nabla, nabla_g]                          ✅
Step 2: rw [helper lemmas]                                   ✅
Step 5: rw [product rules]                                   ✅
Step 5.5: simp [group_sub_add]                               ✅
  └─> Goal is now in some normalized form...
Step 6: Apply collector                                      ❌ BLOCKER
  ├─> Naming approach: simp made no progress
  ├─> Direct collector: pattern not found (g expanded)
  └─> Skip to regrouping: pattern not found
```

---

## NEXT STEPS FOR JP / USER

To unblock, we need ONE of the following:

### Option A: Interactive Goal Inspection

**What**: Use interactive Lean to inspect the goal state after line 5463 (`simp [group_sub_add]`)

**Questions**:
1. Is `g M ρ b r θ` expanded or folded in the goal?
2. What is the exact parenthesization of the 4-sum block?
3. Are there any mixed partials still present?
4. What is the overall structure?

**Value**: Would immediately show us what pattern to match.

### Option B: Freeze `g` Function

**What**: Add `attribute [-simp] g` to prevent g from being expanded

**Where**: Either in section RicciProof (line 5238) or globally

**Code**:
```lean
section RicciProof
-- Freeze *all* ways simp could unfold dCoord or g
attribute [-simp] dCoord dCoord_r dCoord_θ g
```

**Rationale**: If g expansion is the issue, preventing it should allow pattern matching.

### Option C: Use `simp only [group_sub_add]`

**What**: Change line 5463 from `simp [group_sub_add]` to `simp only [group_sub_add]`

**Rationale**: Prevents simp from applying other lemmas that might expand g.

**Code**:
```lean
-- Step 5.5: Open every -(Σ + Σ) to expose structure
simp only [group_sub_add]
```

### Option D: Manual Collector with `conv`

**What**: Use `conv` to navigate to the exact 4-sum location and apply collector surgically

**Requires**: Knowing the exact conv path (which requires interactive goal inspection)

**Pseudocode**:
```lean
conv_lhs =>
  -- Navigate to where the 4 sumIdx terms are
  arg 1  -- descend into first argument
  arg 1  -- continue descending
  -- ... (exact path depends on goal structure)
  rw [hcollect]  -- apply collector at that location
```

### Option E: Alternative Lemma that Matches Expanded `g`

**What**: Create a variant of the collector that has g expanded in its statement

**Difficulty**: High - would need to prove the lemma with match statements

**Not recommended**: Too complex for tactical fix.

---

## CURRENT CODE STATE

### Files Modified This Session:

**`Riemann.lean:296-304`**: ✅ Added `flatten₄₁` and `flatten₄₂`
**`Riemann.lean:5468-5474`**: ❌ Step 6 - multiple approaches attempted, all failed

### Build Command:
```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

### Current Error (Latest Attempt):
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5472:6: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```
(From attempt to skip collector and go direct to regrouping)

---

## RECOMMENDATIONS

### Immediate Next Steps:

1. **Try Option C first** (easiest): Change `simp [group_sub_add]` to `simp only [group_sub_add]`
2. **If that fails, try Option B**: Add `attribute [-simp] g` to freeze g
3. **If both fail**: Need Option A (interactive goal inspection) to understand what's really happening

### Long-term Solution:

The most robust fix requires understanding the actual goal structure after line 5463. Without interactive Lean, we're guessing at patterns. Once we see the goal:
- We can write the correct collector pattern
- Or adjust the proof strategy to match what we actually have
- Or identify which function needs to be frozen

---

## FILES CREATED THIS SESSION

1. **`BUILD_DIAGNOSTIC_OCT21_FINAL.md`** - This comprehensive diagnostic

All previous diagnostic documents remain valid:
- `DIAGNOSTIC_REPORT_TO_JP_OCT21.md` - Initial normalization dilemma analysis
- `PROGRESS_UPDATE_FOR_JP_OCT21.md` - Detailed error messages from first attempts
- `FINAL_STATUS_JP_OCT21.md` - 75% completion status (before current session)

---

**Prepared by**: Claude Code
**Build status**: Compilation fails at Step 6 (line 5472)
**Completion**: ~70% (Steps 1-5.5 working, Step 6+ blocked)
**Root cause**: Pattern matching failure, likely due to `g` function expansion
**Recommended fix**: Try `simp only [group_sub_add]` or freeze g with `attribute [-simp]`
