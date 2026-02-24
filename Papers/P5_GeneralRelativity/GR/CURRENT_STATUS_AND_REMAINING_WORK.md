# Current Status and Remaining Work - Riemann.lean

**Date**: October 6, 2025
**Branch**: `feat/p0.2-invariants` (detached HEAD at 0287f4b)
**Total Errors**: 7

---

## Executive Summary

**Phase 2 Complete**: All 6 Schwarzschild Riemann component lemmas proven (0 sorries) ✅

**Remaining**: 7 compilation errors in older infrastructure code
- 3 pre-existing errors in early infrastructure (lines 1939, 2188, 2323)
- 4 errors in diagonal Ricci cases (lines 5156, 5206, 5245, 5277)

---

## Completed Work

### Phase 2: Riemann Component Lemmas (Lines 4897-5149) ✅

All 6 independent Schwarzschild Riemann tensor components proven with **0 sorries**:

1. **R_trtr = -2M/r³** (lines 4912-4937)
2. **R_tθtθ = M·f(r)/r** (lines 4939-5002)
3. **R_tφtφ = M·f(r)·sin²θ/r** (lines 5004-5026)
4. **R_rθrθ = -M/(r·f(r))** (lines 5028-5051)
5. **R_rφrφ = -M·sin²θ/(r·f(r))** (lines 5053-5076)
6. **R_θφθφ = 2Mr·sin²θ** (lines 5078-5149)
   - Cross-multiplied identity (lines 5078-5107): valid at all angles
   - Component equality (lines 5109-5149): off-axis only (sin θ ≠ 0)

**Key Achievement**: Resolved on-axis coordinate singularity using Junior Professor's two-lemma pattern (cross-multiplication technique).

---

## Remaining Errors (7 Total)

### Category A: Pre-Existing Infrastructure Errors (3 errors)

These errors predate Phase 2 work and are in early file sections:

#### Error 1: Line 1939 - `dCoord_nabla_swap_minus` lemma
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1939:66: unsolved goals
```

**Location**: `lemma dCoord_nabla_swap_minus`

**Context**: Proving derivative distribution over covariant derivative

**Status**: Pre-existing, not related to Phase 2

#### Error 2: Line 2188 - `dCoord_sumIdx_min` lemma
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2188:6: Tactic `apply` failed
```

**Location**: Inside `dCoord_sumIdx_min` proof

**Context**: Derivative of sum over indices

**Status**: Pre-existing, possibly incomplete infrastructure

#### Error 3: Line 2323 - `RiemannUp_antisym_cd` lemma
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2323:2: `simp` made no progress
```

**Location**: `lemma RiemannUp_antisym_cd`

**Context**: Antisymmetry property of Riemann tensor

**Status**: Pre-existing, simp tactic issue

---

### Category B: Diagonal Ricci Case Errors (4 errors)

These errors are in the `Ricci_zero_ext` theorem diagonal cases:

#### Error 4: Line 5156 - case t.t (Ricci_tt = 0)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5156:11: unsolved goals
```

**Formula**: R_tt = R^r_trt + R^θ_tθt + R^φ_tφt = 0

**Approach**: Uses `Riemann_trtr_reduce`, `Riemann_tθtθ_reduce`, `Riemann_tφtφ_reduce` + big simp + field_simp + ring

**Status**: The `field_simp` + `ring` combination doesn't close the goal

#### Error 5: Line 5206 - case r.r (Ricci_rr = 0)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5206:11: unsolved goals
```

**Formula**: R_rr = R^t_rtr + R^θ_rθr + R^φ_rφr = 0

**Status**: Same issue as case t.t

#### Error 6: Line 5245 - case θ.θ (Ricci_θθ = 0)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5245:11: unsolved goals
```

**Formula**: R_θθ = R^t_θtθ + R^r_θrθ + R^φ_θφθ = 0

**Status**: Same issue as case t.t

#### Error 7: Line 5277 - case φ.φ (Ricci_φφ = 0)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5277:11: unsolved goals
```

**Formula**: R_φφ = R^t_φtφ + R^r_φrφ + R^θ_φθφ = 0

**Status**: Same issue as case t.t

---

## Analysis: Why Diagonal Cases Fail

### The Proof Strategy (Patch M)

Each diagonal case follows this pattern:

```lean
case t.t =>
  -- 1. Expand sum and drop R_tttt = 0
  simp only [sumIdx_expand]
  simp only [Riemann_first_equal_zero_ext M r θ h_ext h_sin_nz]

  -- 2. Reorder terms to match reduction lemmas
  have h_rt : Riemann_rtrt = Riemann_trtr := by [symmetry proof]
  have h_th : Riemann_θtθt = Riemann_tθtθ := by [symmetry proof]
  have h_ph : Riemann_φtφt = Riemann_tφtφ := by [symmetry proof]

  -- 3. Apply reduction lemmas
  rw [h_rt, h_th, h_ph,
      Riemann_trtr_reduce, Riemann_tθtθ_reduce, Riemann_tφtφ_reduce]

  -- 4. Expand Christoffel symbols and derivatives
  simp [g, Γ_r_rr, Γ_t_tr, ..., deriv_Γ_t_tr_at, ...]

  -- 5. Algebraic simplification (FAILS HERE)
  field_simp [hr_nz, hf_ne, hθ]; ring
```

### Why the Final Step Fails

After step 4, the goal is a complex polynomial expression in M, r, θ involving:
- Metric components (g_tt, g_rr, g_θθ, g_φφ)
- Christoffel symbols (Γ_r_rr, Γ_t_tr, etc.)
- Derivatives of Christoffel symbols
- Trigonometric functions (sin θ, cos θ)

**Problem**: The `field_simp` + `ring` combination cannot close these goals, suggesting either:
1. Missing simplification lemmas
2. Need for intermediate normalization steps
3. Goals require more sophisticated algebraic manipulation

---

## What's NOT the Problem

### Component Lemmas Don't Interfere ✅

The Phase 2 component lemmas (`Riemann_trtr_eq`, etc.) do **NOT** interfere with the diagonal cases because:
- They're not marked `@[simp]`
- They give closed-form values (e.g., `-2M/r³`)
- The diagonal cases explicitly use `_reduce` lemmas (which give expressions with Γ and derivatives)
- These are two independent sets of lemmas serving different purposes

---

## Next Steps

### Option 1: Fix Diagonal Ricci Cases (Priority: High)

**Goal**: Make the 4 diagonal cases compile

**Approaches to try**:

A. **Add intermediate normalization**:
```lean
-- After simp, before field_simp
simp only [f, pow_two]  -- Expand f = 1 - 2M/r
norm_num  -- Numeric simplifications
```

B. **Factor out common terms**:
```lean
-- Show goal = g_tt * (expr1 + expr2 + expr3) = 0
-- Then prove expr1 + expr2 + expr3 = 0
```

C. **Use polyrith** (if available):
```lean
polyrith  -- Automated polynomial solver
```

D. **Consult Junior Professor**:
- These were claimed to work in commit c173658 but don't actually compile
- May need guidance on the correct proof strategy

### Option 2: Fix Pre-Existing Infrastructure Errors (Priority: Medium)

#### Line 1939: `dCoord_nabla_swap_minus`
- Check what goal remains
- May need additional differentiability lemmas

#### Line 2188: `dCoord_sumIdx_min`
- This lemma name suggests it's a "minimal" version
- Might be incomplete/experimental
- Check if there's a complete version elsewhere

#### Line 2323: `RiemannUp_antisym_cd`
- Simp can't make progress
- May need to expand definitions manually
- Check if there's a missing simp lemma

---

## Sorries Count

```
$ grep -c "sorry" GR/Riemann.lean
0
```

**Result**: No sorries in the file! ✅

All lemmas that are stated are either proven or have compilation errors (but no `sorry` placeholders).

---

## Build Command

```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann
```

**Current result**: 7 errors, 0 sorries

---

## Timeline Estimate

### To Complete Diagonal Ricci Cases (4 errors)

**If straightforward**: 1-2 hours
- Try different simplification tactics
- Add intermediate steps
- May just need the right combination

**If needs consultation**: 3-4 hours
- Document the issue
- Get tactical guidance
- Implement solution

### To Complete Pre-Existing Errors (3 errors)

**Per error**: 30-60 minutes
- Understand what the lemma is proving
- Find missing pieces
- Complete the proof

**Total**: 1.5-3 hours

### Overall Estimate

**Best case**: 2.5-5 hours to 0 errors
**Realistic**: 4-7 hours with consultation

---

## Priority Recommendation

**Focus on diagonal Ricci cases first** because:
1. They're the main goal (Ricci_zero_ext theorem)
2. They're all the same pattern (fix one, apply to all 4)
3. The pre-existing errors might not be essential for the main proof
4. Commit c173658 claimed these worked, so there might be a simple fix

---

## Documentation

Created during this session:
- `PHASE2_COMPLETION_REPORT.md`: How Phase 2 was completed
- `PHASE2_AND_PHASE3_CLARIFICATION.md`: Why Phase 3 isn't needed
- `CURRENT_STATUS_AND_REMAINING_WORK.md`: This document

---

## Conclusion

**Phase 2 is a success**: All component lemmas proven with 0 sorries.

**Remaining work**: 7 compilation errors, of which 4 are in the critical diagonal Ricci cases.

**Next action**: Debug the diagonal Ricci cases to understand why `field_simp` + `ring` doesn't close the goals, then apply fix to all 4 cases.
