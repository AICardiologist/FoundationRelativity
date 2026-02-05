# Diagnostic: File Version Mismatch - November 13, 2024

**Status**: ⚠️ **BLOCKED - Cannot locate target pattern for Paul's calc chain fix**
**For**: Paul and User
**From**: Claude Code

---

## Executive Summary

Successfully added helper lemmas (`g_swap_local` and `insert_delta_right_of_commuted_neg`) to compatibility shim. However, cannot locate the b-branch error pattern Paul described for applying the deterministic calc chain fix.

**Root Issue**: The file structure appears significantly different from Paul's version - the target patterns don't exist in my current file.

---

## What I Successfully Completed ✅

### Helper Lemmas Added (Lines 1817-1827)

```lean
/-! ### Helper lemmas for Paul's surgical fixes (Nov 13) -/

/-- Metric symmetry helper (compact form of g_swap_slots). -/
lemma g_swap_local (M r θ : ℝ) (i j : Idx) :
  g M i j r θ = g M j i r θ := by
  exact g_swap_slots M r θ i j

/-- δ-insertion for right-metric with commuted, negated payload. -/
lemma insert_delta_right_of_commuted_neg
    (M r θ : ℝ) (b : Idx) (F : Idx → ℝ) :
  sumIdx (fun ρ => g M ρ b r θ * (-F ρ))
    =
  sumIdx (fun ρ => g M ρ b r θ * (-F ρ) * (if ρ = b then 1 else 0)) := by
  exact insert_delta_right_diag_neg M r θ b F
```

**Status**: ✅ Lemmas compile correctly, types match Paul's specifications

---

## What I Cannot Locate ❌

### Paul's Target Pattern

**Paul said to look for:**
> "You're looking for the goal whose LHS (after a local set G : Idx → ℝ := …) is syntactically one of:
>     •    sumIdx (fun ρ => -(g M b ρ r θ * G ρ))
>     •    or the equivalent sumIdx (fun ρ => -((g M b ρ r θ) * G ρ))"

**My search results:**
```bash
# Search 1: No `set G` abbreviations found
$ grep -n "set G :" Riemann.lean
# (no output)

# Search 2: No `set.*G.*Idx.*→.*ℝ` pattern found
$ grep -n "set[[:space:]]\+G[[:space:]]*:[[:space:]]*Idx" Riemann.lean
# (no output)

# Search 3: No negated g M b pattern with G found
$ grep -n "-(g M b .* r θ \* G" Riemann.lean
# (no output)
```

**Conclusion**: The pattern Paul described does not exist in my current file version.

---

## What I Actually See in the File

### Current Error Locations (from build_shim_verification_nov11.txt)

**18 total errors**, first few at:
- Line 8986: Type mismatch (in `ha` proof - a-branch)
- Line 9001: unsolved goals
- Line 9044: Tactic `simp` failed
- Line 9071: unsolved goals
- Line 9086: Function expected

### Errors I Found While Searching

**Lines 8807, 8814** (in `hb` proof - b-branch):
```lean
have Hμ : ... := ΓΓ_main_reindex_b_μ   -- Line 8807 - calls missing lemma
have Hν : ... := ΓΓ_main_reindex_b_ν   -- Line 8814 - calls missing lemma
```

**Lines 9021, 9028** (in `ha` proof - a-branch):
```lean
have Hμ : ... := ΓΓ_main_reindex_a_μ   -- Line 9021 - calls missing lemma
have Hν : ... := ΓΓ_main_reindex_a_ν   -- Line 9028 - calls missing lemma
```

**Paul's Note**:
> "Those `ΓΓ_main_reindex_b_μ`, etc. errors belong to the 'B/C+Fubini' group - a different bucket we'll tackle later."

So these are NOT the b-branch errors Paul's calc chain fix is meant to address.

---

## File Structure Analysis

### What Paul Expected to Find

```lean
-- Somewhere in the b-branch proof:
set G : Idx → ℝ := (fun ρ => some_expression)

-- Then later, a goal with:
sumIdx (fun ρ => -(g M b ρ r θ * G ρ)) = something
```

### What Actually Exists at Lines 8880-8916

```lean
-- Line 8880-8892: scalar_finish_bb proof with `let` abbreviations (not `set G`)
let gbb := g M b b r θ
let A := dCoord μ (fun r θ => Γtot M r θ b ν a) r θ
-- etc.

-- Line 8894-8916: h_insert_delta_for_b proof
have h_insert_delta_for_b :
  sumIdx (fun ρ => - ( (dCoord μ ... - dCoord ν ... + sumIdx ... - sumIdx ...) * g M ρ b r θ))
  = ...
```

**Key Difference**: The pattern uses `let` (not `set`), and the structure is:
```lean
sumIdx (fun ρ => - ( BIG_EXPRESSION * g M ρ b r θ))
```

NOT:
```lean
sumIdx (fun ρ => -(g M b ρ r θ * G ρ))
```

---

## Possible Explanations

### Hypothesis 1: File Version Too Old

My file is from commits before Paul's expected structure exists. The `set G` abbreviations and the specific pattern haven't been introduced yet.

**Evidence**:
- Errors call for `ΓΓ_main_reindex_*` lemmas (B/C+Fubini group)
- No `set G` abbreviations present
- Pattern uses `let` instead of `set`

### Hypothesis 2: Pattern Exists But in Different Form

The mathematical pattern is there, but syntactically different (e.g., using `let` instead of `set`, or with metric on the opposite side).

**Evidence**:
- Line 8910 has `insert_delta_right_diag M r θ b (fun ρ => - (...))` which is conceptually similar
- But the metric is `g M ρ b r θ` (correct order) not `g M b ρ r θ` (flipped)

### Hypothesis 3: Fix Applies to Future State

Paul's calc chain fix is meant to be applied AFTER other lemmas (like `ΓΓ_main_reindex_*`) are provided, which will transform the code to have the expected pattern.

**Evidence**:
- Paul mentioned "8 b-branch errors" but I only see B/C+Fubini errors
- The calc chain fix might be for a later stage of fixes

---

## Questions for Paul

### Q1: File Version Confirmation

Is my file version behind your expected state? Should I:
- **Option A**: Wait for you to provide the `ΓΓ_main_reindex_*` lemmas first?
- **Option B**: Check out a different branch/commit?
- **Option C**: The pattern exists but I'm not recognizing it?

### Q2: Alternative Pattern Matching

Could the b-branch error you're referring to be at line 8910-8916?

```lean
-- Line 8910-8916: h_insert_delta_for_b
have := insert_delta_right_diag M r θ b (fun ρ =>
  - ( dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
      - dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
      + sumIdx (fun e => Γtot M r θ ρ μ e * Γtot M r θ e ν a)
      - sumIdx (fun e => Γtot M r θ ρ ν e * Γtot M r θ e μ a) ))
simpa [neg_mul_right₀] using this
```

This has the right structure (δ-insertion with negated payload, metric on right), but:
- Uses `let` abbreviations above (not `set G`)
- The payload is NOT abbreviated as `G ρ`
- Already uses `insert_delta_right_diag` (not the pattern you're fixing)

### Q3: Grep Pattern Adjustment

Should I search for a different pattern? For example:
- `let` instead of `set`?
- Metric in opposite order (`g M ρ b` vs `g M b ρ`)?
- Expanded form without abbreviation?

---

## Current File State

**File**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/Riemann.lean`
**Modified**: Yes (helper lemmas added at lines 1817-1827)
**Compatibility Shim**: Lines 1740-1828 (extended from 1886)
**Error Count**: 18 errors (from most recent build)
**Helper Lemmas**: ✅ `g_swap_local`, `insert_delta_right_of_commuted_neg` present and compiling

---

## Recommendation

**Do NOT proceed with applying Paul's calc chain fix** until:
1. Paul confirms the correct line numbers in MY file version, OR
2. Paul provides the missing `ΓΓ_main_reindex_*` lemmas that may transform the code to the expected state, OR
3. Paul clarifies that my file is outdated and I should sync to a different version

**Reason**: Applying the fix to the wrong location could introduce new errors or break existing (potentially correct) code.

---

## Next Steps

**Waiting for Paul to:**
1. Confirm file version status
2. Provide specific line numbers where the fix should be applied in MY current file
3. OR provide the `ΓΓ_main_reindex_*` lemmas from the B/C+Fubini group first
4. OR clarify which existing code block matches his intended target

**Alternative**: If Paul has access to my exact file version, he could grep for the target pattern himself and provide the exact line numbers.

---

**Report Time**: November 13, 2024
**Status**: Blocked on file version clarification
**Infrastructure**: Ready (helper lemmas added and verified)
**Next Action**: Awaiting Paul's guidance on target location
