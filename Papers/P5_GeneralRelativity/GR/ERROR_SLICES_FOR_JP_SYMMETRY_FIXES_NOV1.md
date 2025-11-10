# Error Slices for JP - After Symmetry Fixes - November 1, 2025

**Date**: November 1, 2025
**Build**: `build_jp_symmetry_fixes_nov1.txt`
**Total Errors**: 27 (down from 30)
**Errors Eliminated**: 3

**Patches Applied**:
- ✅ Patch 0: Added `g_symm_indices` at lines 2310-2313
- ✅ Patch 1: Fixed b-branch contraction with symmetry and reversed calc (lines 8722-8753)
- ✅ Patch 2: Fixed a-branch contraction with factor commutation and reversed calc (lines 8967-9006)

---

## Success Metrics

**Progress**: Error count reduced from 30 → 27 (-3 errors)

**What Worked**:
- `g_symm_indices` lemma added successfully
- b-branch and a-branch contraction blocks compile without the original signature mismatches
- The reversed calc chain approach is recognized by Lean

**What Remains**:
- 13 errors still in Block A (lines 8640-9050)
- New calc-related errors introduced
- Some downstream errors from the calc chain changes

---

## Block A Error Slice: Lines 8640-9050

### Errors in b-branch (8722-8817)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8742:18: No goals to be solved
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8745:8: invalid 'calc' step, left-hand side is
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8753:6: invalid 'calc' step, right-hand side is
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8768:33: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8784:8: Type mismatch: After simplification, term
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8788:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8817:65: unsolved goals
```

**Pattern**:
- Line 8742: `hX` (the `ring` proof) says "No goals to be solved"
- Lines 8745, 8753: Invalid calc steps (LHS/RHS mismatch)
- Lines 8768, 8817: Unsolved goals in subsequent steps
- Lines 8784, 8788: Type mismatch and rewrite failures downstream

**Analysis**:
The reversed calc chain is causing issues. The `hX` proof using `simp [X]; ring` appears to close the goal prematurely, leaving nothing for the calc chain to prove.

---

### Errors in a-branch (8967-9041)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8994:18: No goals to be solved
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8998:8: invalid 'calc' step, left-hand side is
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9006:6: invalid 'calc' step, right-hand side is
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9021:33: unsolved goals
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9037:8: Type mismatch: After simplification, term
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:9041:12: Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

**Pattern**: Symmetric to b-branch
- Line 8994: `hX` says "No goals to be solved"
- Lines 8998, 9006: Invalid calc steps
- Lines 9021, 9037, 9041: Downstream errors

---

## C²-lite Error Slice: Lines 6400-6600

```
(No errors in this range - still clean with sorry placeholders)
```

---

## Detailed Error at Line 8742 (b-branch hX)

**Current code** (lines 8735-8742):
```lean
have hX :
  - ( ( dCoord μ (fun r θ => Γtot M r θ b ν a) r θ
      - dCoord ν (fun r θ => Γtot M r θ b μ a) r θ
      + sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
      - sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) ) )
    * g M b b r θ
    = X b * g M b b r θ := by
  simp [X]; ring
```

**Error**: `No goals to be solved` at line 8742:18

**Hypothesis**: The `simp [X]; ring` closes the current subgoal completely, leaving the outer `have` without a goal to bind the result to.

---

## Detailed Error at Line 8745 (b-branch calc)

**Current code** (lines 8744-8753):
```lean
calc
  - ( ( dCoord μ (fun r θ => Γtot M r θ b ν a) r θ
        - dCoord ν (fun r θ => Γtot M r θ b μ a) r θ
        + sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
        - sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) ) )
      * g M b b r θ
    = X b * g M b b r θ := hX
_   = sumIdx (fun ρ => X ρ * g M b ρ r θ) := hcontract.symm
_   = sumIdx (fun ρ => X ρ * g M ρ b r θ) := hsym.symm
_   = sumIdx (fun ρ => X ρ * (if ρ = b then 1 else 0) * g M b b r θ) := hδ_to_g.symm
```

**Error**: `invalid 'calc' step, left-hand side is...`

**Hypothesis**: The calc chain's LHS doesn't match what the proof context expects. The goal state before the calc may be different from what the calc's first step provides.

---

## Questions for JP

### Q1: hX Proof Structure
The `have hX : ... = ... := by simp [X]; ring` produces "No goals to be solved". Should this be structured differently? Perhaps:
- Use `show` instead of `have`?
- Remove the `hX` binding entirely?
- Change the proof tactic?

### Q2: Calc Chain Integration
The reversed calc chain appears to have issues integrating with the overall proof context. Should:
- The calc be the direct proof of `core_as_sum_b` without the `hX` intermediate?
- The direction be flipped back (forward instead of backward)?
- Additional intermediate steps be added?

### Q3: Missing Steps
Are there missing intermediate lemmas between:
- The `hX` equality and the calc chain start?
- The final calc step and the overall goal?

---

## Comparison: Before and After Symmetry Fixes

### Before (30 errors):
- Lines 8725, 8978: Type mismatch in `sumIdx_contract_g_right/left` (FIXED ✅)
- Lines 8735, 8988: No goals (CASCADE - still present)
- Lines 8738, 8742, 8991, 8995: Invalid calc steps (CASCADE - still present)
- Many downstream errors

### After (27 errors):
- ✅ Contraction signature mismatches resolved
- ✅ `g_symm_indices` allows index swapping
- ⏳ Calc chain integration issues remain
- ⏳ Downstream errors from calc issues remain

---

## Key Insight

The symmetry fixes successfully resolved the **contraction signature mismatches** (the core problem JP identified). However, the **reversed calc chain** introduces new issues with goal management in the proof context.

**Hypothesis**: The calc chain may need to be structured as the direct proof rather than using intermediate `hX` bindings, or the proof flow needs adjustment to match Lean's expectations for calc chains in `have` contexts.

---

## Next Steps

Awaiting JP's guidance on:
1. How to structure the `hX` proof to avoid "No goals to be solved"
2. How to integrate the reversed calc chain with the proof context
3. Whether additional intermediate steps are needed

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: November 1, 2025
**Build**: `build_jp_symmetry_fixes_nov1.txt` (27 errors, down from 30)
**Status**: Symmetry fixes applied, calc chain integration issues remain
**Progress**: 3 errors eliminated, 13 Block A errors remaining

---

**End of Report**
