# Error Slices for JP - November 1, 2025

**Date**: November 1, 2025
**Build**: `build_jp_micro_patches_nov1.txt`
**Total Errors**: 30
**Patches Applied**:
- ✅ Patch 0: Added `sumIdx_commute_factors` at lines 2305-2308
- ✅ Patch 1: Replaced b-branch contraction (lines 8699-8746)
- ✅ Patch 2: Replaced a-branch contraction (lines 8952-8999)

---

## Block A Error Slice: Lines 8640-9050

### Critical Error at Line 8725 (b-branch contraction)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8725:8: Type mismatch
  sumIdx_contract_g_right M r θ b X
has type
  (sumIdx fun e => X e * g M b e r θ) = X b * g M b b r θ
but is expected to have type
  (sumIdx fun ρ => g M ρ b r θ * X ρ) = X b * g M b b r θ
```

**Root Cause**: The existing `sumIdx_contract_g_right` lemma in Schwarzschild.lean has signature:
```lean
sumIdx (fun e => X e * g M b e r θ) = X b * g M b b r θ
```

But JP's Patch 1 needs:
```lean
sumIdx (fun ρ => g M ρ b r θ * X ρ) = X b * g M b b r θ
```

**Differences**:
1. Index order: `b e` vs `ρ b`
2. Factor order: `X e * g M b e` vs `g M ρ b * X ρ`

**Context**: Line 8721 establishes:
```lean
have hcomm :
  sumIdx (fun ρ => X ρ * g M ρ b r θ)
    = sumIdx (fun ρ => g M ρ b r θ * X ρ) := by
  simpa using sumIdx_commute_factors X (fun ρ => g M ρ b r θ)
```

Line 8725 attempts to apply the contraction but the signature doesn't match.

---

### Cascade Errors in b-branch

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8735:18: No goals to be solved
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8738:8: invalid 'calc' step, left-hand side is
  sumIdx fun ρ => (X ρ * if ρ = b then 1 else 0) * g M b b r θ : Real
but is expected to be
  -(((dCoord μ (fun r θ => Γtot M r θ b ν a) r θ - dCoord ν (fun r θ => Γtot M r θ b μ a) r θ +
          sumIdx fun e => Γtot M r θ b μ e * Γtot M r θ e ν a) -
        sumIdx fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) *
      g M b b r θ) : Real
```

These are downstream from the type mismatch at 8725.

---

### Similar Error at Line 8978 (a-branch contraction)

```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:8978:8: Type mismatch
  sumIdx_contract_g_left M r θ a X
has type
  (sumIdx fun e => g M a e r θ * X e) = X a * g M a a r θ
but is expected to have type
  (sumIdx fun ρ => g M a ρ r θ * X ρ) = X a * g M a a r θ
```

**Same pattern**: The existing `sumIdx_contract_g_left` expects `a e` indices but we provide `a ρ`.

---

### Additional Block A Errors

**Line 8761**: unsolved goals (downstream from contraction failure)
**Line 8777**: Type mismatch in subsequent steps
**Line 8781**: Rewrite failed - pattern not found
**Line 8810**: unsolved goals

**a-branch symmetric errors**:
- Line 8968: Type mismatch (after simplification)
- Line 8988: No goals to be solved
- Lines 8991, 8995: invalid calc steps
- Line 9014: unsolved goals
- Lines 9030, 9034: Type mismatch and rewrite failed

---

## C²-lite Error Slice: Lines 6400-6600

```
(No errors in this range)
```

**Status**: ✅ Clean - only warnings about 'sorry' declarations as expected:
- Line 6460:14: declaration uses 'sorry'
- Line 6496:6: declaration uses 'sorry'
- Line 6507:6: declaration uses 'sorry'

The C²-lite area is correctly reverted to sorry and causes no build errors.

---

## Analysis

**Working as intended**:
1. `sumIdx_commute_factors` shim added cleanly
2. X definitions now clean (no metric factor inside)
3. hδ_to_g, hcomm steps execute successfully
4. C²-lite area clean

**Blocking issue**:
The existing Schwarzschild contraction lemmas have different signatures than what the patches need:

**Existing** (`sumIdx_contract_g_right`):
```lean
sumIdx (fun e => X e * g M b e r θ) = X b * g M b b r θ
```

**Needed** (from JP's patch):
```lean
sumIdx (fun ρ => g M ρ b r θ * X ρ) = X b * g M b b r θ
```

**Question for JP**: Should we:
1. Use a different existing lemma with the correct signature?
2. Add a new variant of the contraction lemma?
3. Modify the calc chain to match the existing lemma's signature?

---

## Full Error List for Block A (Lines 8640-9050)

| Line | Error Type | Description |
|------|------------|-------------|
| 8725 | Type mismatch | `sumIdx_contract_g_right` signature mismatch (b-branch) |
| 8735 | No goals | Cascade from 8725 |
| 8738 | Invalid calc | LHS doesn't match expected form |
| 8742 | Invalid calc | RHS doesn't match expected form |
| 8761 | Unsolved goals | Subsequent step blocked |
| 8777 | Type mismatch | After simplification |
| 8781 | Rewrite failed | Pattern not found |
| 8810 | Unsolved goals | Later in proof |
| 8968 | Type mismatch | After simplification (a-branch) |
| 8978 | Type mismatch | `sumIdx_contract_g_left` signature mismatch (a-branch) |
| 8988 | No goals | Cascade from 8978 |
| 8991 | Invalid calc | LHS doesn't match |
| 8995 | Invalid calc | RHS doesn't match |
| 9014 | Unsolved goals | Subsequent step blocked |
| 9030 | Type mismatch | After simplification |
| 9034 | Rewrite failed | Pattern not found |

---

## Next Steps

Awaiting JP's next micro-patches to resolve the `sumIdx_contract_g_right` / `sumIdx_contract_g_left` signature mismatches.

**Key Question**: How should we bridge the gap between:
- The contraction result we have: `sumIdx (fun ρ => g M ρ b r θ * X ρ)`
- The lemma signature available: `sumIdx (fun e => X e * g M b e r θ)`

---

**Prepared by**: Claude Code (Lean 4 Assistant)
**Date**: November 1, 2025
**Build**: `build_jp_micro_patches_nov1.txt` (30 errors)
**Status**: Patches 0-2 applied, awaiting next micro-patches from JP
