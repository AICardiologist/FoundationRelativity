# Elimination Plan: All Sorries and Axioms in Riemann.lean
**Date**: October 20, 2025
**Current Status**: 11 sorries, 1 axiom
**Goal**: Eliminate all sorries and axioms

---

## EXECUTIVE SUMMARY

**Current State**:
- ✅ **Main theorem proven**: `have final` proof body complete (eliminated 1 sorry)
- ⚠️ **Remaining work**: 11 sorried lemmas + 1 axiom
- 📊 **Build status**: Compiles successfully (3078 jobs)

**Strategy**: Apply proven tactical patterns from `have final` success to remaining lemmas

---

## COMPLETE INVENTORY

### Axioms (1 total)

| Line | Declaration | Type | Difficulty |
|------|-------------|------|------------|
| 1897 | `dCoord_g_via_compat_ext_temp` | Forward reference | **TRIVIAL** |

**Notes**:
- Proof exists at line 2594
- Just needs file reorganization
- **Action**: Move proof before first use

---

### Sorries (11 total)

#### **Category A: Main Riemann Identities (High Priority)**

| Line | Lemma | Description | Difficulty | Estimated Time |
|------|-------|-------------|------------|----------------|
| 3813 | `regroup_right_sum_to_RiemannUp` | Simpler version (no extra terms) | **MEDIUM** | 2-3 hours |
| 7804 | `regroup_right_sum_to_Riemann_CORRECT` | Full Riemann (with extra terms) | **HIGH** | 4-6 hours |
| 7836 | `regroup_right_sum_to_RiemannUp_NEW` | NEW version (right side) | **HIGH** | 4-6 hours |
| 7853 | `regroup_left_sum_to_RiemannUp_NEW` | NEW version (left side) | **HIGH** | 4-6 hours |

**Total Category A**: 4 lemmas, ~14-21 hours

#### **Category B: Ricci Identity and Symmetries (Medium Priority)**

| Line | Lemma | Description | Difficulty | Estimated Time |
|------|-------|-------------|------------|----------------|
| 5098 | `ricci_identity_on_g_rθ_ext` | Ricci identity for g_{rθ} | **MEDIUM** | 3-4 hours |
| 5135 | `ricci_identity_on_g` | General Ricci identity | **MEDIUM** | 2-3 hours |
| 5144 | `Riemann_swap_a_b_ext` | Symmetry: swap indices a,b | **LOW** | 1-2 hours |
| 5159 | `Riemann_swap_a_b` | Symmetry: swap a,b (general) | **LOW** | 1-2 hours |

**Total Category B**: 4 lemmas, ~7-11 hours

#### **Category C: Infrastructure Lemmas (Lower Priority)**

| Line | Lemma | Description | Difficulty | Estimated Time |
|------|-------|-------------|------------|----------------|
| 7678 | `dCoord_r_sumIdx` | Distribute ∂_r over sumIdx | **LOW** | 1-2 hours |
| 7700 | `dCoord_θ_sumIdx` | Distribute ∂_θ over sumIdx | **LOW** | 1-2 hours |
| 7736 | `sum_k_prod_rule_to_Γ₁` | Product rule to Γ₁ form | **MEDIUM** | 2-3 hours |

**Total Category C**: 3 lemmas, ~4-7 hours

---

## DETAILED ANALYSIS

### 🔴 Category A: Main Riemann Identities (CRITICAL PATH)

#### 1. Line 3813: `regroup_right_sum_to_RiemannUp` (SIMPLER VERSION)

**What it needs to prove**:
```lean
lemma regroup_right_sum_to_RiemannUp
    (M r θ : ℝ) (h_ext : Exterior M r θ) (h_θ : Real.sin θ ≠ 0) (a b : Idx) :
  -- LHS: Some expression involving dCoord of sums
  -- RHS: Expression with RiemannUp (no extra Γ·Γ₁ terms)
```

**Why it's simpler**: This is the version WITHOUT the extra (Γ·Γ₁) terms that come from metric compatibility.

**Strategy**:
- ✅ **Similar to `have final`** but WITHOUT Cancel_r/Cancel_θ steps
- Apply prod_rule_backwards_sum
- Use congrArg pattern for rewriting under dCoord
- Pointwise sumIdx_congr for RiemannUp recognition

**Estimated difficulty**: MEDIUM (we have the pattern from `have final`)

**Recommended approach**:
1. Copy structure from `have final` (lines 4598-4804)
2. Remove Cancel_r_expanded/Cancel_θ_expanded steps (simpler!)
3. Keep prod_rule_backwards_sum application
4. Keep congrArg pattern for step0
5. Keep pointwise proof for step4

**JP's role**: Review proof structure, verify mathematical correctness

---

#### 2. Line 7804: `regroup_right_sum_to_Riemann_CORRECT`

**What it needs to prove**:
```lean
lemma regroup_right_sum_to_Riemann_CORRECT
  -- Full Riemann tensor identity with all extra terms
```

**Why it's harder**: This includes ALL the extra (Γ·Γ₁) terms from metric compatibility.

**Strategy**:
- ✅ **Directly applies `have final` pattern**
- Use prod_rule_backwards_sum
- Use Cancel_r_expanded/Cancel_θ_expanded
- Contract to Riemann (not RiemannUp)

**Estimated difficulty**: HIGH (more complex algebra)

**Recommended approach**:
1. Use `have final` as template (lines 4598-4804)
2. Adjust for Riemann vs RiemannUp target
3. Keep all Cancel steps
4. May need additional contraction lemmas

**JP's role**: Verify contraction steps, check sign conventions

---

#### 3. Line 7836: `regroup_right_sum_to_RiemannUp_NEW`

**What it needs to prove**:
```lean
lemma regroup_right_sum_to_RiemannUp_NEW
  -- NEW formulation (right side)
```

**Why NEW**: Likely a refactored version with cleaner assumptions or different form.

**Strategy**:
- Compare with line 3813 version
- Identify what's different in assumptions
- Apply same tactical patterns

**Estimated difficulty**: HIGH (need to understand differences)

**Recommended approach**:
1. Read lemma statement carefully
2. Compare with line 3813 version
3. Adapt proven tactics to NEW form
4. May be able to reuse significant portions

**JP's role**: Explain what makes this "NEW" and why it's needed

---

#### 4. Line 7853: `regroup_left_sum_to_RiemannUp_NEW`

**What it needs to prove**:
```lean
lemma regroup_left_sum_to_RiemannUp_NEW
  -- NEW formulation (left side, mirror of right)
```

**Why left vs right**: Probably swaps indices r ↔ θ or similar.

**Strategy**:
- Mirror of line 7836
- Same tactics but with swapped indices

**Estimated difficulty**: HIGH (but similar to 7836)

**Recommended approach**:
1. Prove 7836 first
2. Mirror the proof with index swaps
3. Verify sign changes are correct

**JP's role**: Verify index permutation conventions

---

### 🟡 Category B: Ricci Identity and Symmetries

#### 5. Line 5098: `ricci_identity_on_g_rθ_ext`

**What it needs to prove**:
```lean
lemma ricci_identity_on_g_rθ_ext
  -- Ricci identity applied to specific metric component g_{rθ}
```

**Strategy**:
- Use main Riemann identity (once proven)
- Contract indices appropriately
- Apply to g_{rθ} specifically

**Estimated difficulty**: MEDIUM (depends on Category A)

**Recommended approach**:
1. Wait for Category A lemmas
2. Apply Ricci identity definition
3. Specialize to r,θ indices
4. Simplify using Schwarzschild symmetries

**JP's role**: Verify contraction indices are correct

---

#### 6. Line 5135: `ricci_identity_on_g`

**What it needs to prove**:
```lean
lemma ricci_identity_on_g
  -- General Ricci identity for metric
```

**Strategy**:
- Generalization of line 5098
- Apply to arbitrary metric components

**Estimated difficulty**: MEDIUM

**Recommended approach**:
1. Prove line 5098 first
2. Generalize to arbitrary indices
3. Use index-free reasoning where possible

**JP's role**: Verify generalization is correct

---

#### 7. Line 5144: `Riemann_swap_a_b_ext`

**What it needs to prove**:
```lean
lemma Riemann_swap_a_b_ext
  -- Riemann symmetry: R_{abcd} = -R_{bacd}
```

**Strategy**:
- Use antisymmetry of Riemann tensor
- This is a standard GR textbook result

**Estimated difficulty**: LOW (well-known symmetry)

**Recommended approach**:
1. Expand Riemann definition
2. Show swapping a,b introduces minus sign
3. Use commutativity/anticommutativity of ∇

**JP's role**: Confirm sign convention matches textbook

---

#### 8. Line 5159: `Riemann_swap_a_b`

**What it needs to prove**:
```lean
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  -- Generalized version without ext assumption
```

**Strategy**:
- Generalization of line 5144
- Remove Exterior assumption if possible

**Estimated difficulty**: LOW

**Recommended approach**:
1. Prove line 5144 first
2. Check if ext assumption can be weakened
3. May just be a wrapper

**JP's role**: Clarify assumption requirements

---

### 🟢 Category C: Infrastructure Lemmas

#### 9. Line 7678: `dCoord_r_sumIdx`

**What it needs to prove**:
```lean
lemma dCoord_r_sumIdx
  -- ∂_r (Σ f) = Σ (∂_r f) under appropriate conditions
```

**Strategy**:
- Differentiation under summation
- Finite sum, so this should be straightforward

**Estimated difficulty**: LOW

**Recommended approach**:
1. Use Finset.sum_comm or similar
2. Apply differentiability of each summand
3. Standard real analysis lemma

**JP's role**: Verify differentiability conditions

---

#### 10. Line 7700: `dCoord_θ_sumIdx`

**What it needs to prove**:
```lean
lemma dCoord_θ_sumIdx
  -- ∂_θ (Σ f) = Σ (∂_θ f)
```

**Strategy**:
- Mirror of line 7678
- Same tactics with θ instead of r

**Estimated difficulty**: LOW

**Recommended approach**:
1. Prove line 7678 first
2. Adapt proof for θ direction
3. Almost identical proof

**JP's role**: None (mechanical adaptation)

---

#### 11. Line 7736: `sum_k_prod_rule_to_Γ₁`

**What it needs to prove**:
```lean
lemma sum_k_prod_rule_to_Γ₁
  -- Product rule application resulting in Γ₁ form
```

**Strategy**:
- Apply product rule
- Recognize Γ₁ = Σ g·Γ pattern

**Estimated difficulty**: MEDIUM

**Recommended approach**:
1. Apply dCoord_mul_of_diff (product rule)
2. Expand and simplify
3. Recognize Γ₁ definition

**JP's role**: Verify Γ₁ recognition is correct

---

### ⚪ Axiom Elimination

#### Line 1897: `dCoord_g_via_compat_ext_temp`

**What it is**:
```lean
axiom dCoord_g_via_compat_ext_temp (M r θ : ℝ) (h_ext : Exterior M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ)
```

**Why it exists**: Forward reference - proof exists at line 2594

**How to eliminate**:
1. Find proof `dCoord_g_via_compat_ext` at line 2594
2. Move proof (and any dependencies) before line 1897
3. Delete axiom declaration
4. Replace all uses of `_temp` with actual lemma

**Estimated difficulty**: TRIVIAL (just file reorganization)

**Estimated time**: 30 minutes

**JP's role**: Review file organization changes

---

## ELIMINATION STRATEGY

### Phase 1: Quick Wins (1-2 days)

**Goal**: Eliminate easiest lemmas to build momentum

**Targets**:
1. ✅ Line 1897: Axiom elimination (30 min)
2. ✅ Line 7678: `dCoord_r_sumIdx` (1-2 hours)
3. ✅ Line 7700: `dCoord_θ_sumIdx` (1-2 hours)
4. ✅ Line 5144: `Riemann_swap_a_b_ext` (1-2 hours)
5. ✅ Line 5159: `Riemann_swap_a_b` (1-2 hours)

**Total Phase 1**: 5 items, ~6-9 hours

**JP's help needed**:
- Review axiom elimination PR
- Verify symmetry lemma sign conventions

---

### Phase 2: Core Infrastructure (3-5 days)

**Goal**: Prove foundational lemmas that others depend on

**Targets**:
1. ✅ Line 7736: `sum_k_prod_rule_to_Γ₁` (2-3 hours)
2. ✅ Line 3813: `regroup_right_sum_to_RiemannUp` (2-3 hours)

**Total Phase 2**: 2 items, ~4-6 hours

**JP's help needed**:
- Review proof structure for line 3813
- Verify Γ₁ recognition in line 7736

---

### Phase 3: Main Identities (1-2 weeks)

**Goal**: Prove the critical Riemann tensor identities

**Targets**:
1. ✅ Line 7804: `regroup_right_sum_to_Riemann_CORRECT` (4-6 hours)
2. ✅ Line 7836: `regroup_right_sum_to_RiemannUp_NEW` (4-6 hours)
3. ✅ Line 7853: `regroup_left_sum_to_RiemannUp_NEW` (4-6 hours)

**Total Phase 3**: 3 items, ~12-18 hours

**JP's help needed**:
- Explain difference between OLD and NEW versions
- Review contraction steps in CORRECT version
- Verify sign conventions throughout

---

### Phase 4: Ricci Identities (3-5 days)

**Goal**: Complete Ricci tensor infrastructure

**Targets**:
1. ✅ Line 5098: `ricci_identity_on_g_rθ_ext` (3-4 hours)
2. ✅ Line 5135: `ricci_identity_on_g` (2-3 hours)

**Total Phase 4**: 2 items, ~5-7 hours

**JP's help needed**:
- Review index contraction for Ricci tensor
- Verify final forms match physics conventions

---

## SUMMARY OF JP HELP NEEDED

### Critical Reviews (Must Have)

1. **Line 3813 proof structure** - First major application of `have final` pattern
2. **OLD vs NEW differences** - Lines 7836/7853 vs earlier versions
3. **Sign conventions** - Throughout all Riemann identities
4. **Index contraction** - Ricci identity lemmas (lines 5098, 5135)

### Nice to Have

1. Symmetry lemma verification (lines 5144, 5159)
2. File reorganization review (axiom elimination)
3. Infrastructure lemma verification (lines 7678, 7700, 7736)

---

## REQUEST TO JUNIOR PROFESSOR

Dear JP,

We've successfully completed the `have final` proof using the tactical fixes you provided! The congrArg pattern and pointwise approach worked perfectly.

**Current Status**:
- ✅ Build: Compiling successfully (3078 jobs)
- ✅ Main proof: `have final` complete
- ⚠️ Remaining: 11 sorries + 1 axiom

**Where We Need Your Help**:

### 1. Understanding OLD vs NEW Versions
- Lines 7836 (`regroup_right_sum_to_RiemannUp_NEW`)
- Line 7853 (`regroup_left_sum_to_RiemannUp_NEW`)

**Questions**:
- What makes these "NEW"?
- How do they differ from line 3813?
- Do we need both versions or can we deprecate OLD?

### 2. Proof Strategy for Line 3813
This is the simpler version of `have final` (without Cancel lemmas).

**Questions**:
- Can we literally copy `have final` and remove Cancel steps?
- Are there any subtle differences we should watch for?
- Should this be proven before or after the NEW versions?

### 3. Sign Conventions
**Questions**:
- Line 7804 mentions "CORRECTED SIGN on ΓΓ commutator terms"
- Can you verify our current sign conventions are correct?
- Are there any other sign issues we should be aware of?

### 4. Dependency Order
**Questions**:
- What's the optimal order to prove these 11 lemmas?
- Which lemmas depend on which others?
- Can any be proven in parallel?

### 5. Ricci Identity Details
Lines 5098 and 5135 need Ricci tensor contractions.

**Questions**:
- What's the exact contraction formula you want?
- Should we contract Riemann first, then apply to g?
- Or apply Riemann to g first, then contract?

---

## ESTIMATED TIMELINE

**With JP's help**:
- Phase 1 (Quick Wins): 1-2 days
- Phase 2 (Infrastructure): 3-5 days
- Phase 3 (Main Identities): 1-2 weeks
- Phase 4 (Ricci): 3-5 days

**Total**: ~3-4 weeks to complete all 11 sorries + 1 axiom

**Without JP's help**:
- Significantly longer due to trial and error on:
  - Understanding NEW vs OLD
  - Verifying sign conventions
  - Determining proof dependencies

---

## NEXT IMMEDIATE STEPS

1. **Wait for JP's guidance** on:
   - OLD vs NEW clarification
   - Proof order recommendation
   - Sign convention verification

2. **Start Phase 1** (can do independently):
   - Axiom elimination (line 1897)
   - `dCoord_r_sumIdx` (line 7678)
   - `dCoord_θ_sumIdx` (line 7700)

3. **Prepare for Phase 2**:
   - Study line 3813 statement
   - Compare with `have final` structure
   - Draft proof outline

---

## FILES FOR JP TO REVIEW

1. **Success report**: `SUCCESS_HAVE_FINAL_PROOF_COMPLETE.md`
   - Shows what works and proven tactics

2. **This file**: `ELIMINATION_PLAN_SORRIES_AND_AXIOMS.md`
   - Complete inventory and strategy

3. **Current code**: `Riemann.lean` lines 4598-4804
   - Working `have final` proof to use as template

---

**Prepared by**: Claude Code
**Date**: October 20, 2025
**Status**: Awaiting JP's guidance on proof strategy
**Build**: ✅ Compiling successfully
**Confidence**: High (have proven tactics, just need direction)

---

## APPENDIX: Proven Tactical Patterns from `have final`

For JP's reference, here are the tactics that worked:

### Pattern 1: Rewriting Under Binders
```lean
-- Promote equality to function equality
have recog_fun :
  (fun r θ => sumIdx (...)) = (fun r θ => Γ₁ ...) := by
  funext r' θ'; simp [Γ₁]

-- Apply congrArg to rewrite inside dCoord
have d_r := congrArg (fun F => dCoord Idx.r F r θ) recog_fun
```

### Pattern 2: Pointwise Sum Recognition
```lean
apply sumIdx_congr
intro ρ
have : f₁ ρ - ... = g M a ρ r θ * (...) := by
  simp [f₁, f₂, f₃, f₄]
  ring
simpa [RiemannUp] using this
```

### Pattern 3: Product Rule Application
```lean
have hA_raw := prod_rule_backwards_sum M r θ h_ext h_θ a Idx.θ Idx.r b
have hA : A = dCoord ... - C := by
  have : Γ₁ ... = sumIdx ... := recog.symm
  simp only [A, C, this]
  exact hA_raw
```

These patterns should transfer directly to the remaining lemmas!
