# Riemann.lean - Verified Status Report

**Date**: October 6, 2025
**Branch**: `feat/p0.2-invariants` (detached HEAD at 0287f4b)
**File**: Papers/P5_GeneralRelativity/GR/Riemann.lean
**Total Lines**: 5303
**Verification Method**: `lake build` (full compilation, no caching)

---

## Executive Summary

**Sorries**: ✅ **0** (all proofs attempted, no placeholders)
**Compilation Errors**: ❌ **7** (detailed breakdown below)
**Phase 2 Status**: ✅ Component lemmas structurally complete
**Build Verification**: ✅ Full file compilation confirmed (deliberate error at line 5301 was detected)

---

## Verification Methodology

To ensure accurate error counting, the following rigorous verification was performed:

1. **Added deliberate syntax error at line 5301** (near end of file)
2. **Ran `lake build Papers.P5_GeneralRelativity.GR.Riemann`** (NOT `lake env lean`)
3. **Confirmed error at line 5301 was detected** → proves entire file was compiled
4. **Reverted syntax error and re-ran build** to get actual error count
5. **Double-checked sorries** with `grep -c "sorry"`

This methodology addresses previous false negatives from cached builds.

---

## Error Breakdown (7 Total)

### Category A: Pre-Existing Infrastructure Errors (3 errors)

These errors exist in early infrastructure code, predating Phase 2 work:

#### Error 1: Line 1939 - `dCoord_nabla_swap_minus`
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:1939:66: unsolved goals
```

**Location**: `lemma dCoord_nabla_swap_minus`
**Context**: Proving derivative distribution over covariant derivative
**Status**: Incomplete infrastructure, may not be essential for main results

#### Error 2: Line 2188 - `dCoord_sumIdx_min`
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2188:6: Tactic `apply` failed: could not unify the conclusion of `@funext`
```

**Location**: `lemma dCoord_sumIdx_min`
**Context**: Derivative of sum over indices
**Status**: The name suggests this is a "minimal" version, possibly experimental

#### Error 3: Line 2323 - `RiemannUp_antisym_cd`
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:2323:2: `simp` made no progress
```

**Location**: `lemma RiemannUp_antisym_cd`
**Context**: Antisymmetry property of Riemann tensor
**Status**: Simp tactic cannot make progress; may need manual expansion

---

### Category B: Diagonal Ricci Case Errors (4 errors)

These errors occur in the main `Ricci_zero_ext` theorem, in the 4 diagonal cases:

#### Error 4: Line 5156 - Case t.t (R_tt = 0)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5156:11: unsolved goals
```

**Formula**: R_tt = R^r_trt + R^θ_tθt + R^φ_tφt = 0

**Proof strategy** (Patch M):
1. Expand sum, drop R_tttt = 0
2. Apply symmetry lemmas to reorder terms
3. Apply reduction lemmas (`Riemann_trtr_reduce`, etc.)
4. Expand Christoffel symbols and derivatives
5. **Algebraic simplification with `field_simp` + `ring`** ← FAILS HERE

**Issue**: After the big `simp` expansion at line 5193-5203, the goal is a complex polynomial in M, r, θ. The final `field_simp [hr_nz, hf_ne, hθ, pow_two, sq]; ring` at line 5205 cannot close the goal.

#### Error 5: Line 5206 - Case r.r (R_rr = 0)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5206:11: unsolved goals
```

**Formula**: R_rr = R^t_rtr + R^θ_rθr + R^φ_rφr = 0
**Issue**: Same pattern as case t.t

#### Error 6: Line 5245 - Case θ.θ (R_θθ = 0)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5245:11: unsolved goals
```

**Formula**: R_θθ = R^t_θtθ + R^r_θrθ + R^φ_θφθ = 0
**Issue**: Same pattern as case t.t

#### Error 7: Line 5277 - Case φ.φ (R_φφ = 0)
```
error: Papers/P5_GeneralRelativity/GR/Riemann.lean:5277:11: unsolved goals
```

**Formula**: R_φφ = R^t_φtφ + R^r_φrφ + R^θ_φθφ = 0
**Issue**: Same pattern as case t.t

---

## Completed Work (0 Sorries)

### Phase 2: Riemann Component Lemmas (Lines 4897-5149) ✅

All 6 independent Schwarzschild Riemann tensor components have been proven **with 0 sorries**:

1. **R_trtr = -2M/r³** (lines 4912-4937) ✅
2. **R_tθtθ = M·f(r)/r** (lines 4939-5002) ✅
3. **R_tφtφ = M·f(r)·sin²θ/r** (lines 5004-5026) ✅
4. **R_rθrθ = -M/(r·f(r))** (lines 5028-5051) ✅
5. **R_rφrφ = -M·sin²θ/(r·f(r))** (lines 5053-5076) ✅
6. **R_θφθφ = 2Mr·sin²θ** (lines 5078-5149) ✅
   - Uses cross-multiplication technique to handle coordinate singularity at θ=0,π
   - Two-lemma pattern: unconditional cross-multiplied identity + conditional component equality

**Key Achievement**: Successfully resolved on-axis coordinate singularity using Junior Professor's cross-multiplication approach, avoiding direct evaluation of singular Christoffel symbol Γ^φ_θφ = cot θ.

---

## Analysis: Why Do Diagonal Ricci Cases Fail?

### The Proof Pattern (Patch M)

Each diagonal case follows this structure:

```lean
case t.t =>
  classical
  have hf_ne : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  -- 1. Expand sum and drop R_tttt = 0
  simp only [sumIdx_expand]
  simp only [Riemann_first_equal_zero_ext M r θ h_ext h_sin_nz]

  -- 2. Reorder terms using symmetry
  have h_rt : Riemann_rtrt = Riemann_trtr := by [proof]
  have h_th : Riemann_θtθt = Riemann_tθtθ := by [proof]
  have h_ph : Riemann_φtφt = Riemann_tφtφ := by [proof]

  -- 3. Apply reduction lemmas
  rw [h_rt, h_th, h_ph,
      Riemann_trtr_reduce, Riemann_tθtθ_reduce, Riemann_tφtφ_reduce]

  -- 4. Expand everything (Christoffel symbols + derivatives)
  have hθ : Real.sin θ ≠ 0 := h_sin_nz
  simp [ g, Γ_r_rr, Γ_t_tr, Γ_r_φφ, Γ_r_θθ, Γ_θ_rθ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ
       , Γtot, Γtot_t_tr, Γtot_r_rr
       , dCoord_r, dCoord_θ
       , pow_two, sq
       , deriv_Γ_t_tr_at M r hr_nz hf_ne
       , deriv_Γ_r_rr_at M r hr_nz hf_ne
       , deriv_Γ_θ_φφ_at θ
       , deriv_Γ_φ_θφ_at θ hθ
       ]

  -- 5. FAILS: Algebraic simplification
  field_simp [hr_nz, hf_ne, hθ, pow_two, sq]; ring
```

### Why Step 5 Fails

After step 4, the goal is a large polynomial expression involving:
- Metric components (g_tt, g_rr, g_θθ, g_φφ)
- Christoffel symbols (Γ_r_rr, Γ_t_tr, etc.)
- Derivatives of Christoffel symbols
- Trigonometric functions (sin θ, cos θ)
- The Schwarzschild function f(r) = 1 - 2M/r

The tactics `field_simp` followed by `ring` are designed to:
1. Clear denominators and simplify field operations (`field_simp`)
2. Prove polynomial equality (`ring`)

**Problem**: These tactics cannot close the goal, suggesting one of:
1. The expressions don't actually simplify to 0 (math error)
2. Additional intermediate simplification steps are needed
3. Missing simp lemmas for f(r), trigonometric identities, etc.
4. The goal requires more sophisticated algebraic manipulation

---

## What's NOT the Problem

### Component Lemmas Don't Interfere ✅

The Phase 2 component lemmas (`Riemann_trtr_eq`, etc.) do **NOT** interfere with diagonal cases because:
- They're not marked `@[simp]`
- They give closed-form numerical values (e.g., `-2M/r³`)
- The diagonal cases use `_reduce` lemmas (which expand to Christoffel expressions)
- These are two independent lemma families with different purposes:
  - `_eq` lemmas: for computing actual component values
  - `_reduce` lemmas: for proving algebraic identities

---

## Recommended Next Steps

### Priority 1: Debug Diagonal Ricci Cases (High Impact)

All 4 diagonal cases fail at the same step with the same pattern. **Fixing one will likely fix all four.**

**Approach A: Examine the actual goal**
```lean
-- Replace final line with:
sorry
-- field_simp [hr_nz, hf_ne, hθ, pow_two, sq]; ring
```
Then run `lake build` to see what expression needs to equal 0.

**Approach B: Add intermediate normalization**
```lean
-- After big simp, before field_simp:
simp only [f, pow_two]  -- Expand f = 1 - 2M/r
norm_num  -- Numeric simplifications
```

**Approach C: Consult Junior Professor**
These cases were claimed to work in commit c173658 ("Complete Patch M") but fail in actual compilation. Request tactical guidance on the correct proof strategy.

### Priority 2: Fix Pre-Existing Infrastructure (Medium Impact)

These may not block the main results but should be addressed:

**Line 1939**: Check what goal remains; may need differentiability lemmas
**Line 2188**: "min" suggests experimental version; check if there's a complete version
**Line 2323**: Simp can't progress; may need manual definition expansion

---

## Historical Context

### Timeline of Misunderstandings

1. **Before Oct 5**: Error detection bug led to false reports of "0 errors"
2. **Oct 5**: Junior Professor provided cross-multiplication solution for R_θφθφ
3. **Oct 6 (early)**: Incorrect belief that file compiled with 0 errors (cached builds)
4. **Oct 6 (verified)**: Proper `lake build` revealed 7 actual errors

### Lesson Learned

**Always use `lake build` (not `lake env lean`) for verification**, and add a deliberate error near the end of large files to confirm full compilation.

---

## File Statistics

```
Total Lines:              5303
Sorries:                  0
Compilation Errors:       7
  - Infrastructure:       3
  - Diagonal Ricci:       4
Phase 2 Component Lemmas: 6/6 proven ✅
```

---

## Conclusion

**Phase 2 is technically complete** - all component lemmas are proven with 0 sorries. However, **7 compilation errors remain**, including 4 critical errors in the main `Ricci_zero_ext` theorem diagonal cases.

**The diagonal Ricci cases are the most urgent issue** because:
1. They're the main scientific result (proving Ricci = 0 for Schwarzschild)
2. All 4 fail at the same step with the same pattern
3. Fixing one will likely fix all four
4. They were claimed to work in previous commits but don't actually compile

**Recommendation**: Focus on debugging case t.t to understand why the final algebraic simplification fails, then apply the solution to all 4 diagonal cases.
