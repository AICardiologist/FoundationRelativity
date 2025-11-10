# Proof #2 Blocker Report - October 26, 2025

**Date**: October 26, 2025
**Agent**: Claude Code (Sonnet 4.5)
**Status**: ❌ **BLOCKED ON MISSING INFRASTRUCTURE**

---

## TL;DR

**Proof #1**: ✅ **COMPLETE** (line 10942)
**Proof #2**: ❌ **BLOCKED** (line 11043) - requires metric contraction lemma not found in codebase

**Progress**: Successfully reduced Phase 2B-3 sorrys from **2 → 1** (50% completion)

---

## Proof #2: What It Attempts

**Lemma**: `regroup_right_sum_to_Riemann_CORRECT` (Lines 11043-11070)

**Mathematical Statement**:
```lean
∑_k [∂_r(Γ^k_{θa} · g_{kb}) - ∂_θ(Γ^k_{ra} · g_{kb})]
= ∑_k Riemann^k_{arθ} · g_{kb}
```

**Goal**: Connect the derivatives-of-products form (LHS) to the Riemann tensor sum (RHS)

---

## What Works: Step 1 (Proven via Proof #1)

**Applies**: `sum_k_prod_rule_to_Γ₁` (Proof #1, now complete) to simplify LHS:

```lean
∑_k [∂_r(Γ·g) - ∂_θ(Γ·g)]
  = ∂_r(Γ₁_{baθ}) - ∂_θ(Γ₁_{bar})    -- Via Proof #1 ✅
```

**This step is solid** - it's already proven and compiling.

---

## What's Blocked: Step 2 (Connecting to RHS)

**Need to prove**:
```lean
∂_r(Γ₁_{baθ}) - ∂_θ(Γ₁_{bar}) = ∑_k Riemann_{karθ} · g_{kb}
```

**Relationship to `Riemann_via_Γ₁`**:

The lemma `Riemann_via_Γ₁` (line 2516) states:
```lean
Riemann_{βarθ} = ∂_r(Γ₁_{βaθ}) - ∂_θ(Γ₁_{βar}) + [Γ·Γ terms]
```

**Index mismatch**:
- **Have**: `∂_r(Γ₁_{baθ}) - ∂_θ(Γ₁_{bar})` (single component)
- **Need**: `∑_k Riemann_{karθ} · g_{kb}` (sum over first index `k`)

**Connection requires**: Relating single `Riemann_{barθ}` to summed `∑_k Riemann_{karθ} · g_{kb}`

---

## Attempted Strategy: Index Manipulation

I attempted to work backwards from RHS:

```lean
∑_k Riemann_{karθ} · g_{kb}
  = ∑_k (∑_μ g_{kμ} · RiemannUp^μ_{arθ}) · g_{kb}    -- Unfold Riemann
  = ∑_k ∑_μ g_{kμ} · RiemannUp^μ_{arθ} · g_{kb}      -- Distribute
  = ∑_μ ∑_k g_{kμ} · g_{kb} · RiemannUp^μ_{arθ}      -- Swap sums
  = ∑_μ (∑_k g_{kμ} · g_{kb}) · RiemannUp^μ_{arθ}    -- Factor out
```

**Blocker**: Need to simplify `∑_k g_{kμ} · g_{kb}`

---

## Mathematical Gap: Metric Contraction

**What's needed**: A lemma of the form:
```lean
lemma metric_contraction (M r θ : ℝ) (μ b : Idx) :
  sumIdx (fun k => g M k μ r θ * g M k b r θ) = ???
```

**Expected in GR**:
- This should involve the metric inverse `g^{μb}`
- In component form: `g_{kμ} · g^{kb} = δ^μ_b` (Kronecker delta)
- But our setup has lowered metric `g_{kb}`, not raised `g^{kb}`

**Searched for**:
- ❌ `gInv_g_orthonormal`: Found `gInv` lemmas, but they use `gInv` (inverse metric), not products of `g`
- ❌ `sumIdx.*g M.*g M`: Found usage in `raise2_T` context, but not the contraction we need
- ❌ Any lemma connecting `∑_k g_{kμ} · g_{kb}` to metric inverse or Kronecker delta

**Conclusion**: This infrastructure doesn't exist in the codebase.

---

## Alternative Approaches Considered

### Approach 1: Direct `Riemann_via_Γ₁` Application

**Idea**: Apply `Riemann_via_Γ₁` directly with index swapping

**Problem**: `Riemann_via_Γ₁` gives:
```lean
Riemann_{βarθ} = ∂_r(Γ₁_{βaθ}) - ∂_θ(Γ₁_{βar}) + [Γ·Γ terms]
```

Setting `β = b`:
```lean
Riemann_{barθ} = ∂_r(Γ₁_{baθ}) - ∂_θ(Γ₁_{bar}) + [Γ·Γ terms]
```

**Γ·Γ terms vanish on Exterior** (JP's hint: "metric compatibility makes them zero")

So:
```lean
Riemann_{barθ} = ∂_r(Γ₁_{baθ}) - ∂_θ(Γ₁_{bar})  -- on Exterior
```

**But**: Goal is `∑_k Riemann_{karθ} · g_{kb}`, not single `Riemann_{barθ}`

**Gap**: How to relate these two forms?

### Approach 2: Riemann Symmetries

**Idea**: Use Riemann tensor antisymmetry to relate indices

**Problem**: The antisymmetry is in pairs:
- `R_{abcd} = -R_{bacd}` (first-pair antisymmetry)
- `R_{abcd} = -R_{abdc}` (second-pair antisymmetry)

**Our case**: Need to relate `R_{barθ}` to `∑_k R_{karθ} · g_{kb}`

This is not a symmetry operation - it's a **contraction** with the metric.

### Approach 3: Definition Unfolding

**Idea**: Unfold `Riemann` and work with `RiemannUp` directly

**Attempted**: See "Attempted Strategy" above

**Blocker**: Still requires metric contraction lemma

---

## Why JP's Proof Might Be Missing a Piece

JP's drop-in proof states:
```lean
calc
  ∑_k [∂_r(Γ·g) - ∂_θ(Γ·g)]
    _ = ∂_r(Γ₁) - ∂_θ(Γ₁)          := sum_k_prod_rule_to_Γ₁  -- ✅ WORKS
    _ = ∑_k Riemann·g                := ???                    -- ❌ BLOCKED
```

**Possible explanations**:

1. **Missing lemma**: JP assumed a helper lemma exists that connects `∂(Γ₁_{ba·})` to `∑_k R_{ka,rθ}·g_{kb}`

2. **Implicit step**: JP may have skipped a step that's "obvious" to GR experts but requires explicit infrastructure

3. **Different index convention**: The proof might work with a different index arrangement we haven't tried

4. **Metric compatibility magic**: There may be a clever use of `nabla_g = 0` that directly connects these forms

---

## What Infrastructure Would Complete This

### Option A: Metric Contraction Lemma

```lean
lemma metric_double_contraction (M r θ : ℝ) (h_ext : Exterior M r θ) (μ b : Idx) :
  sumIdx (fun k => g M k μ r θ * g M k b r θ) =
    if μ = b then (sum of diagonal terms) else 0
```

**OR** (if codebase uses inverse metric):
```lean
lemma metric_with_inverse (M r θ : ℝ) (h_ext : Exterior M r θ) (μ b : Idx) :
  sumIdx (fun k => g M k μ r θ * gInv M k b r θ) =
    if μ = b then 1 else 0
```

### Option B: Direct Riemann-Gamma Connection

```lean
lemma Riemann_sum_from_Γ₁_derivatives (M r θ : ℝ) (h_ext : Exterior M r θ)
    (h_θ : Real.sin θ ≠ 0) (a b : Idx) :
  dCoord Idx.r (fun r θ => Γ₁ M r θ b a Idx.θ) r θ
- dCoord Idx.θ (fun r θ => Γ₁ M r θ b a Idx.r) r θ
  = sumIdx (fun k => Riemann M r θ k a Idx.r Idx.θ * g M k b r θ)
```

This is **exactly** what Proof #2 tries to prove - so we'd need to prove this from first principles using metric properties.

### Option C: Inverse Riemann_via_Γ₁

If `Riemann_via_Γ₁` can be inverted to solve for `∂(Γ₁)` in terms of `Riemann`, and we can handle the index structure, we might complete the proof.

---

## Current State of Codebase

**File**: `Riemann.lean`

**Line 10942-11034**: `sum_k_prod_rule_to_Γ₁` ✅ **COMPLETE**
- Proves derivative-sum interchange for Christoffel-metric products
- All infrastructure exists (dCoord_sumIdx, differentiableAt lemmas, Γtot_symmetry, g_symm_JP)
- Compiles cleanly, no errors

**Line 11043-11070**: `regroup_right_sum_to_Riemann_CORRECT` ❌ **BLOCKED**
- Step 1 (line 11064-11065): Uses Proof #1 ✅ Works
- Step 2 (line 11066-11070): Missing connection ❌ Blocked
- Currently has `sorry` at line 11070

**Total sorrys**: 9 (down from 10 originally, down from 2 in Phase 2B-3)

---

## Recommendations

### Recommendation 1: Ask JP for Clarification (PREFERRED)

**Questions for JP**:
1. Is there a metric contraction lemma we're missing?
2. Should we use `gInv` (metric inverse) instead of double `g` products?
3. Is there an alternative proof strategy that bypasses index manipulation?
4. Can you provide the missing Step 2 connection or point to existing infrastructure?

### Recommendation 2: Document as Final Technical Debt

**Rationale**:
- ✅ **50% progress** on Phase 2B-3 (1 of 2 proofs complete)
- ✅ **Critical path 100% proven** (Option C, Ricci identity, antisymmetry)
- ✅ **Proof #1 demonstrates** JP's infrastructure exists and works
- ❌ **Proof #2 requires** new mathematical infrastructure

**Action**:
- Update `REMAINING_ISSUES_ANALYSIS_OCT26.md` with Proof #2 blocker
- Note: "Requires metric contraction lemma or alternative proof strategy"

### Recommendation 3: Try Different Index Assignment

**Idea**: Maybe swapping the role of `b` and `β` in `Riemann_via_Γ₁` gives the right form

**Status**: Not yet attempted - would need expert guidance on which assignment to try

---

## Success Metrics

| Metric | Target | Achieved | Notes |
|--------|--------|----------|-------|
| **Proof #1** | Complete | ✅ Yes | Lines 10942-11034 |
| **Proof #2** | Complete | ❌ No | Blocked at line 11070 |
| **Phase 2B-3 sorrys** | 0 | 1 remaining | 50% reduction (2→1) |
| **Critical path** | 100% | ✅ 100% | Option C bypasses |
| **Build status** | Clean | ✅ Clean | 9 sorrys, 0 errors |

---

## Attempt Timeline

**Total time on Proof #2**: ~45 minutes

**Iteration 1** (15 min): Direct application of JP's proof
- Result: Index mismatch identified

**Iteration 2** (15 min): Backwards construction from RHS
- Result: Hit metric contraction blocker

**Iteration 3** (15 min): Search for missing infrastructure
- Result: Confirmed lemma doesn't exist in codebase

---

## Key Insights

1. **JP's Proof #1 was complete** - all infrastructure existed, only tactical adjustments needed

2. **JP's Proof #2 has mathematical gap** - requires lemma not in codebase (or not findable via grep)

3. **The gap is specific**: Metric double contraction `∑_k g_{kμ} · g_{kb}`

4. **Not a tactical issue**: This is a mathematical infrastructure gap, not a tactic selection problem

5. **GR knowledge required**: Completing this likely requires expert knowledge of how Schwarzschild metric properties simplify this contraction

---

## Next Steps

**Immediate**: Wait for user decision:
- **Option A**: Request JP clarification on missing infrastructure
- **Option B**: Document as final technical debt (1 sorry remaining)
- **Option C**: Attempt different index assignment (needs guidance)

**Long-term**: If completed later:
1. Add metric contraction lemma to infrastructure
2. Complete Proof #2 using that lemma
3. Achieve 0 sorrys in Phase 2B-3 (aspirational, not critical)

---

## Files Modified

**Modified**:
- `Riemann.lean` line 11043-11070: Added enhanced sorry comment documenting blocker

**Created**:
- `PROOF2_BLOCKER_REPORT_OCT26.md` (this document)

**To Update**:
- `REMAINING_ISSUES_ANALYSIS_OCT26.md`: Change Phase 2B-3 count from 2 to 1
- `JP_DROPINS_ATTEMPT_OCT26.md`: Add final status of both proofs

---

**Prepared By**: Claude Code (Sonnet 4.5)
**Date**: October 26, 2025
**Status**: ❌ **Proof #2 blocked on missing mathematical infrastructure**

---
