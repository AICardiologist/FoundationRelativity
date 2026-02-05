# Session Status: Scoping Issue After Nested Lemma Conversion

**Date**: October 28, 2025 (Evening - Very Late)
**Session focus**: Fix scoping issues after converting nested lemmas to have statements
**Status**: ⚠️ **BLOCKED** - Complex scoping issue discovered

---

## Executive Summary

Successfully converted all 8 nested lemmas to `have` statements per JP's guidance, which **eliminated the structural "unexpected token 'have'" error**. However, uncovered a complex scoping issue where variables defined inside `have ΓΓ_block` proofs are being referenced outside their scope.

### Bottom Line
- ✅ **Structural error fixed**: No more "unexpected token 'have'; expected command"
- ✅ **All 8 nested lemmas converted**: `lemma` → `have` with docstrings removed
- ✅ **With clauses fixed**: Changed short names (`hbb`, `hrho`) to full names (`h_bb_core`, `h_rho_core_b`)
- ❌ **New scoping errors**: Variables `rho_core_b`, `aa_core`, etc. defined inside `have` proofs but used outside

### Error Count
**Many errors** - exact count TBD (build still running)

---

## What Was Fixed ✅

### 1. Converted All 8 Nested Lemmas to `have`
Lines converted:
- Line 7881: `lemma ΓΓ_main_reindex_b_μ` → `have ΓΓ_main_reindex_b_μ :`
- Line 7958: `lemma ΓΓ_main_reindex_b_ν` → `have ΓΓ_main_reindex_b_ν :`
- Line 8032: `lemma ΓΓ_cross_collapse_b_μ` → `have ΓΓ_cross_collapse_b_μ :`
- Line 8049: `lemma ΓΓ_cross_collapse_b_ν` → `have ΓΓ_cross_collapse_b_ν :`
- Line 8066: `lemma ΓΓ_main_reindex_a_μ` → `have ΓΓ_main_reindex_a_μ :`
- Line 8139: `lemma ΓΓ_main_reindex_a_ν` → `have ΓΓ_main_reindex_a_ν :`
- Line 8217: `lemma ΓΓ_cross_collapse_a_μ` → `have ΓΓ_cross_collapse_a_μ :`
- Line 8234: `lemma ΓΓ_cross_collapse_a_ν` → `have ΓΓ_cross_collapse_a_ν :`

All parameter lists removed and all docstrings converted to regular comments.

### 2. Fixed `with` Clause Names
Changed from short names to full names to match code expectations:
- Line 8364: `with hbb` → `with h_bb_core`
- Line 8369: `with hrho` → `with h_rho_core_b`
- Line 8562: `with haa` → `with h_aa_core`
- Line 8567: `with hrho` → `with h_rho_core_a`

Updated corresponding `simpa` calls to use new names.

---

## Current Blocking Issue 🔴

### Scoping Error: Variables Defined Inside `have` Proofs

**Pattern**:
```lean
have ΓΓ_block :
  <goal using let bindings>
  let bb_core := ...
  let rho_core_b := ...
  bb_core + rho_core_b := by
  classical
  ...
  set bb_core := ... with h_bb_core
  set rho_core_b := ... with h_rho_core_b
  simpa [h_bb_core, h_rho_core_b, ...]  -- Proof ends here

-- Now out of scope!
calc
  ...
  _ = ... + rho_core_b := by  -- ❌ ERROR: rho_core_b not in scope
    simp only [h_rho_core_b]  -- ❌ ERROR: h_rho_core_b not in scope
```

**Affected variables**:
- `bb_core` and `h_bb_core` (b-branch)
- `rho_core_b` and `h_rho_core_b` (b-branch)
- `aa_core` and `h_aa_core` (a-branch)
- `rho_core_a` and `h_rho_core_a` (a-branch)

**Error lines**:
- Line 8450: `Unknown identifier 'rho_core_b'`
- Line 8451: `Unknown identifier 'h_rho_core_b'`
- Line 8648: `Unknown identifier 'rho_core_a'`
- Line 8649: `Unknown identifier 'h_rho_core_a'`

---

## Root Cause Analysis 🤔

### The Structure
The code has this hierarchy:
```lean
lemma algebraic_identity ... := by
  classical
  ...
  have (some_sub_theorem) := by
    classical
    ...
    have ΓΓ_block :
      <goal with let bindings> := by
      ...
      set bb_core := ... with h_bb_core
      set rho_core_b := ... with h_rho_core_b
      simpa [h_bb_core, h_rho_core_b, ...]  -- ← Proof ends, variables go out of scope

    have scalar_finish_bb : ... := by ...
    have core_as_sum_b : ... := by ...
    have scalar_finish : ... := by ...

    calc  -- ← Part of (some_sub_theorem) proof
      ...
      _ = ... + rho_core_b := by  -- ❌ ERROR! Out of scope
        simp only [h_rho_core_b]  -- ❌ ERROR! Out of scope
```

### Why This Worked Before
The orphaned `set` statements I deleted (lines 8256-8277 in original file) were defining these variables at the OUTER scope (part of `some_sub_theorem` or `algebraic_identity`). They were at top level (no indentation), which suggested they were misplaced, but they were actually providing the necessary scope.

### Why It Breaks Now
After converting nested `lemma` declarations to `have`, the scoping rules changed. The `set` statements inside `have ΓΓ_block` are now local to that proof, and the calc block can't access them.

---

## Possible Solutions 💡

### Option A: Define Variables at Outer Scope
Add `set` statements at the scope of `some_sub_theorem` (before `have ΓΓ_block`):
```lean
have (some_sub_theorem) := by
  classical
  ...
  set bb_core := ... with h_bb_core
  set rho_core_b := ... with h_rho_core_b
  set aa_core := ... with h_aa_core
  set rho_core_a := ... with h_rho_core_a

  have ΓΓ_block : ... := by
    -- Use bb_core, rho_core_b from outer scope
    ...

  calc
    _ = ... + rho_core_b := by  -- ✅ Now in scope!
```

**Pros**: Clean scoping, matches original intent
**Cons**: Need to carefully identify the right scope level

### Option B: Use `let` in Calc Block
Replace references with direct `let` bindings:
```lean
calc
  ...
  _ = ... + (let rho_core_b := ...; rho_core_b) := by
```

**Pros**: Local, no scope issues
**Cons**: Verbose, duplicates definitions

### Option C: Restructure Proofs
Move the calc block INSIDE the `have ΓΓ_block` proof where variables are in scope.

**Pros**: Logical grouping
**Cons**: Major restructuring, changes proof flow

---

## What I Need 🙏

**From JP**:
1. Confirm Option A is correct approach
2. Identify the exact scope level where `set` statements should be placed
3. Should the `set` statements duplicate the `let` bindings in `ΓΓ_block` goal, or should we restructure?

**Alternative**: If you can provide corrected code for lines 8280-8500 (one representative section), I can apply the pattern to the other sections.

---

## Session Progress

### Changes Made This Session
1. Converted all 8 nested lemmas to `have` (removed parameter lists, converted docstrings)
2. Fixed `with` clause names in all 4 `set` statements
3. Identified scoping issue with `bb_core`, `rho_core_b`, `aa_core`, `rho_core_a`

### Build Status
- **Structural error**: Fixed ✅
- **Scoping errors**: Need JP guidance

### Files Modified
- `Riemann.lean`: Lines 7878-8600+ (nested lemma conversions, with clause fixes)
- Created: `build_all_nested_fixed_oct28.txt`, `build_with_clauses_fixed_oct28.txt`

---

**END OF STATUS REPORT**

**Prepared by**: Claude Code
**Session date**: October 28, 2025 (Evening - Very Late)
**Status**: Awaiting JP guidance on scoping issue OR attempting Option A independently

**Next steps**:
1. Identify exact scope level for `set` statements
2. Add `set` statements at correct scope
3. Verify build succeeds
4. Continue with A3 and collapse + collect pattern
