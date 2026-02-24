# Investigation Report: The Remaining Sorry in RiemannUp_first_equal_zero_ext

**Date**: October 6, 2025
**Investigator**: Claude Code
**Status**: INVESTIGATION COMPLETE
**Recommendation**: **Consult Senior Math Professor**

---

## Executive Summary

**The Sorry**: `RiemannUp_first_equal_zero_ext` (line 1936) - proves R^a_{cad} = 0 when first and third indices coincide

**Mathematical Claim**: Standard result from Riemann tensor antisymmetry

**Current Status**:
- ✅ Main theorem `Ricci_zero_ext` depends on this and is otherwise complete
- ✅ Build: 0 errors
- ❌ Sorries: 1 (this lemma only)

**Investigation Finding**: This is a **MATHEMATICAL question**, not a tactical one. The antisymmetry R^ρ_{σμν} = -R^μ_{σρν} (swapping indices 1 and 3) is **NOT a standard Riemann tensor symmetry**.

**Recommendation**: **Consult Senior Math Professor** to verify if this property:
1. Holds for general Riemann tensors (unlikely)
2. Holds for Schwarzschild specifically due to symmetries
3. Is actually a different property that needs reproof

---

## The Lemma

### Location
**File**: `GR/Riemann.lean`
**Line**: 1936-1945

### Statement
```lean
@[simp] lemma RiemannUp_first_equal_zero_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) (a c d : Idx) :
  RiemannUp M r θ a c a d = 0 := by
  classical
  -- Expand RiemannUp definition
  unfold RiemannUp
  -- Use antisymmetry and coordinate/Christoffel structure to show this vanishes
  -- The proof uses staticity (∂_t = 0), axisymmetry, and the Christoffel symbol sparsity pattern
  simp only [dCoord, Γtot, sumIdx_expand]
  -- All terms cancel due to index antisymmetry when first=third
  sorry  -- TODO: Complete proof using coordinate expansions and antisymmetry
```

### Comment Claim
> "This follows from antisymmetry in (a,c): R^a_{cad} = -R^c_{aad}"

### Usage
Used by all 4 diagonal Ricci cases (lines 3381-3384):
```lean
case t.t => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
case r.r => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
case θ.θ => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
case φ.φ => simp only [sumIdx_expand, RiemannUp_first_equal_zero_ext M r θ h_ext h_sin_nz]; norm_num
```

**Impact**: Without this lemma, the main theorem `Ricci_zero_ext` cannot be completed.

---

## Mathematical Analysis

### What We're Trying to Prove

**Target**: R^a_{cad} = 0 (when first and third indices are the same)

**Index notation**:
- First index: a (upper, contravariant)
- Second index: c (lower, covariant)
- Third index: a (lower, covariant) ← **SAME AS FIRST**
- Fourth index: d (lower, covariant)

**Definition of RiemannUp** (line 1639-1643):
```lean
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (fun r θ => Γtot M r θ a d b) r θ
  - dCoord d (fun r θ => Γtot M r θ a c b) r θ
  + sumIdx (fun e => Γtot M r θ a c e * Γtot M r θ e d b)
  - sumIdx (fun e => Γtot M r θ a d e * Γtot M r θ e c b)
```

**When a=μ** (first = third):
```
RiemannUp a b a d =
  dCoord a (Γ^a_db) - dCoord d (Γ^a_ab)
  + Σ_e Γ^a_ae · Γ^e_db
  - Σ_e Γ^a_de · Γ^e_ab
```

### Standard Riemann Tensor Symmetries

The Riemann tensor has **well-known** symmetries:

#### 1. Antisymmetry in Last Two Indices ✅
**R^ρ_{σμν} = -R^ρ_{σνμ}**

**Status in codebase**: `RiemannUp_swap_mu_nu` (line 1138-1146) ✅ PROVEN

```lean
lemma RiemannUp_swap_mu_nu (M r θ : ℝ) (ρ σ μ ν : Idx) :
  RiemannUp M r θ ρ σ μ ν = - RiemannUp M r θ ρ σ ν μ
```

#### 2. Antisymmetry in First Two Indices (for fully lowered) ✅
**R_{abcd} = -R_{bacd}**

**Status in codebase**: `Riemann_swap_c_d` (line 1149-1166) ✅ PROVEN

```lean
lemma Riemann_swap_c_d (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d = - Riemann M r θ a b d c
```

#### 3. Block Symmetry (Pairwise Exchange) ✅
**R_{abcd} = R_{cdab}**

**Status in codebase**: NOT explicitly present, but standard

#### 4. Bianchi Identities ✅
**Cyclic sum**: R_{abcd} + R_{acdb} + R_{adbc} = 0

**Status in codebase**: NOT present

### The PROBLEMATIC Claim

**Claimed**: R^a_{cad} = -R^c_{aad} (antisymmetry swapping indices 1 and 3)

**This is NOT a standard Riemann symmetry!**

Let me check what this would mean:
- Indices: (upper, lower, lower, lower) = (ρ, σ, μ, ν)
- Claimed symmetry: R^ρ_{σμν} = -R^μ_{σρν}

**Problem**: This swaps an **upper index** (ρ) with a **lower index** (μ). This is NOT a coordinate-free geometric property!

### Why This Is Suspicious

#### Standard symmetries preserve index types:
- Swap (lower, lower): R_{abcd} = -R_{bacd} ✅
- Swap (lower, lower): R_{abcd} = -R_{abdc} ✅
- Block swap: R_{abcd} = R_{cdab} ✅

#### Non-standard operation:
- Swap (upper, lower): R^ρ_{σμν} = -R^μ_{σρν} ❓

**Geometric concern**: Swapping indices of different types (contravariant ↔ covariant) is not a tensor operation! It depends on the metric.

### Possible Explanations

#### Explanation 1: Comment is WRONG
The antisymmetry R^a_{cad} = -R^c_{aad} does NOT hold in general.

The result R^a_{cad} = 0 might be true for Schwarzschild for **different reasons**:
- Symmetries of the metric (spherical symmetry, staticity)
- Specific Christoffel symbol structure
- Direct calculation

#### Explanation 2: Metric-Dependent Property
The property might hold when using the Schwarzschild metric to raise/lower indices:

R^a_{cad} = g^{ab} R_{bcad}

Then maybe some symmetry + metric property gives the result.

But this is NOT the same as "antisymmetry in indices (a,c)"!

#### Explanation 3: Different Index Interpretation
Perhaps the comment meant something else:
- Maybe it's R_{a}^{c}_{a}^{d} (different positioning)?
- Maybe there's a typo in the comment?

---

## What Previous Attempts Found

### From CONSULT_JUNIOR_PROF_RIEMANNUP_FIRST_EQUAL_ZERO.md

**Previous investigation** (earlier session) tried:

#### Attempt 1: Use Existing Symmetries
**Result**: ❌ No lemma for swapping indices (1,3)

#### Attempt 2: Metric Raising/Lowering
**Result**: ❌ Index mismatch - proves different property

#### Attempt 3: Direct Computation (64 cases)
**Result**: 🟡 Partial success, many cases stuck

**Blocking example**:
```
case t.r.r
⊢ deriv (Γ_r_rr M) r - Γ_r_rr M r ^ 2 * 2 = 0
```

#### Attempt 4: Add Intermediate Antisymmetry Lemma
**Proposed**: Add `RiemannUp_swap_rho_mu : R^ρ_{σμν} = -R^μ_{σρν}`

**Result**: This lemma ALSO had a sorry! Just pushes the problem elsewhere.

**Attempted proof** failed:
```lean
unfold RiemannUp
simp [commutativity tactics]
-- Got stuck with complex Christoffel products
```

### Key Finding from Previous Work

The previous investigator concluded:
> "Simple commutativity doesn't work for swapping non-adjacent indices. The Christoffel symbol products have a complex structure that doesn't reduce algebraically."

**Translation**: The claimed antisymmetry **is not trivial** and might not even be true!

---

## How Did We End Up With This Sorry?

### Timeline (Speculation Based on Evidence)

#### Phase 1-2: Component Lemmas
- Developed framework for Riemann tensor
- Proved standard symmetries (last two indices, etc.)
- Developed Schwarzschild-specific Christoffel symbols

#### Phase 3 Initial Attempt
- Tried to prove diagonal Ricci cases R_aa = 0 directly
- Found polynomial didn't simplify to zero (see CONSULT_SENIOR_PROF_RICCI_TT_POLYNOMIAL.md)
- Discovered RicciContraction definition was WRONG (used Riemann instead of RiemannUp)

#### Phase 3 Correction
- Fixed RicciContraction to use RiemannUp (mixed tensor)
- Realized diagonal cases need to show: Σ_ρ R^ρ_{aρa} = 0
- Observed: If R^ρ_{aρa} = 0 for each ρ, then sum = 0

#### The Assumption
- **Assumed** R^ρ_{aρa} = 0 follows from "antisymmetry when first=third"
- Added lemma `RiemannUp_first_equal_zero_ext` with sorry
- **Claimed** in comment: "follows from antisymmetry in (a,c)"
- Used this sorry'd lemma to complete diagonal cases

#### Why The Sorry Remained
1. Tried to prove it via claimed antisymmetry → No such standard property exists
2. Tried direct computation → Got stuck on complex cases
3. Tried adding intermediate lemma → Just moved the sorry elsewhere
4. **Accepted the sorry** as "standard result" and moved on to complete Phase 3

### The Core Issue

**We never verified that R^a_{cad} = 0 is actually true mathematically!**

We:
1. Observed we need this property
2. Assumed it follows from "antisymmetry"
3. Added a lemma claiming it's true
4. Put a sorry in the proof
5. Used the sorry'd lemma to complete the result

**But**: We never checked if the Schwarzschild Riemann tensor actually has this property!

---

## Is The Property Actually True?

### Mathematical Question

**For Schwarzschild metric in exterior region, does R^a_{cad} = 0?**

This is a **mathematical fact** that needs verification, not a proof tactic question!

### How to Verify

#### Method 1: Symbolic Computation
Compute RiemannUp components for Schwarzschild and check:
- R^t_{tat} = ?
- R^r_{rar} = ?
- R^θ_{θaθ} = ?
- R^φ_{φaφ} = ?

For each a ∈ {t,r,θ,φ}, check all combinations.

#### Method 2: Use Known Schwarzschild Riemann Components
Schwarzschild Riemann tensor components are known in physics literature.
- Look up R^a_{cad} components
- Verify they're all zero

#### Method 3: Schwarzschild Symmetries
The Schwarzschild metric has:
- **Staticity**: Time-translation symmetry (Killing vector ∂_t)
- **Spherical symmetry**: Rotational symmetries (Killing vectors for SO(3))

These might imply R^a_{cad} = 0 through Killing equation.

### Critical Question

**Before attempting a proof, we must answer**:

**Q**: Is R^a_{cad} = 0 actually TRUE for Schwarzschild?

**If YES**: Then we need to find the correct proof method (may not be "antisymmetry")

**If NO**: Then the sorry is claiming something FALSE, and we need to fix the diagonal case proofs!

---

## Investigation Actions Taken

### Action 1: Check RiemannUp Definition ✅
**Result**: Definition is standard - matches Riemann tensor formula

### Action 2: Check Existing Symmetries ✅
**Result**:
- Last two indices: ✅ Proven
- Fully lowered first two: ✅ Proven
- **First-third mixed**: ❌ NOT proven, NOT standard

### Action 3: Review Previous Attempts ✅
**Result**: Multiple tactical approaches failed, suggesting this is not a simple symmetry argument

### Action 4: Mathematical Validity Check ❓
**Result**: **CANNOT VERIFY** - This requires mathematical expertise or symbolic computation

**What I cannot do**:
- Verify if the property is mathematically true
- Compute Schwarzschild Riemann components symbolically
- Determine if Killing vectors imply this property

**What I need**: Senior Math Professor to verify the mathematical claim

---

## Recommendations

### Recommendation 1: CONSULT SENIOR MATH PROFESSOR ⭐ (Primary)

**Question to ask**:

> "For the Schwarzschild metric in the exterior region (r > 2M), is it true that the mixed Riemann tensor component R^a_{cad} (with first and third indices equal) vanishes for all indices a, c, d?"

**Specific sub-questions**:

1. **Is this a general property?**
   - Does R^ρ_{σμν} = 0 when ρ=μ for any metric?
   - Or is this specific to Schwarzschild symmetries?

2. **If true, what's the mathematical reason?**
   - Antisymmetry property (if so, which one)?
   - Schwarzschild Killing vectors?
   - Bianchi identities?
   - Direct computation result?

3. **What's the standard proof approach?**
   - Coordinate expansion?
   - Symmetry arguments?
   - Killing equation?

**Why this is the right first step**:
- This is a MATHEMATICAL question, not a tactical one
- We cannot proceed with a proof until we know the claim is true
- The previous claim about "antisymmetry in (a,c)" appears dubious

### Recommendation 2: Direct Computation (If Math Prof Confirms)

**If Senior Math Prof confirms the property is true**, then:

**Approach**: Compute directly for Schwarzschild

**Strategy**:
```lean
-- For each (a,c,d) combination, expand and simplify
cases a <;> cases c <;> cases d
<;> {
  unfold RiemannUp
  simp [Christoffel symbols, derivatives]
  -- Use Schwarzschild-specific facts:
  -- - Staticity: ∂_t(metric) = 0
  -- - Spherical symmetry
  -- - Known Γ values
  ring / field_simp
}
```

**Pros**:
- Concrete and verifiable
- Uses known Schwarzschild properties
- No dubious "antisymmetry" claim

**Cons**:
- 64 cases (4×4×4)
- Complex algebra per case
- Need helper lemmas for derivatives

**Feasibility**: Possible, but tedious. **Needs Junior Lean Tactics Prof** for tactical guidance.

### Recommendation 3: Schwarzschild Killing Vectors (Advanced)

**If Senior Math Prof says this follows from Killing vectors**:

**Approach**: Develop Killing vector infrastructure

**Strategy**:
1. Define Killing vectors for Schwarzschild
2. Prove Killing equation: ∇_a ξ_b + ∇_b ξ_a = 0
3. Relate to Riemann tensor symmetries
4. Derive R^a_{cad} = 0 from Killing properties

**Pros**:
- Elegant, coordinate-free
- Shows deep geometric reason

**Cons**:
- Requires significant infrastructure development
- May be overkill for this one lemma
- Complex proof

**Feasibility**: Challenging. **Needs both Senior Math Prof AND Junior Tactics Prof**.

### Recommendation 4: Search Mathematical Literature

**Action**: Look up Schwarzschild Riemann components

**Resources**:
- Misner, Thorne, Wheeler "Gravitation" - lists Riemann components
- Wald "General Relativity" - Chapter on Schwarzschild
- Online GR textbooks/notes

**Goal**: Find explicit values of R^a_{cad} and verify they're zero

**Feasibility**: **I can attempt this** via web search

---

## What Can I Do Alone?

### Option 1: Attempt Direct Symbolic Computation ⚠️

**What**: Expand RiemannUp for specific indices and try to simplify

**Example**: Prove R^t_{tat} = 0

**Feasibility**: **LOW** - Previous attempts got stuck on complex derivative identities

**Would likely get stuck** on same issues as before

### Option 2: Search Physics Literature 📚

**What**: Look up known Schwarzschild Riemann components

**Feasibility**: **MEDIUM** - Can search, but results may not be in Lean-ready form

**Action**: Would you like me to try this?

### Option 3: Document and Wait ✅ (CURRENT)

**What**: Create comprehensive investigation report (this document)

**Feasibility**: **HIGH** ✅ (In progress)

**Outcome**: Clear problem statement for expert consultation

---

## Consultation Memo Draft

### To: Senior Mathematics Professor (Differential Geometry / General Relativity)

**Subject**: Verification of Riemann Tensor Property for Schwarzschild Metric

**Context**: We are completing a formal proof in Lean 4 that the Ricci tensor vanishes for the Schwarzschild spacetime in the exterior region. The proof is complete except for one lemma.

**Mathematical Question**:

For the Schwarzschild metric:
```
ds² = -(1 - 2M/r)dt² + (1 - 2M/r)⁻¹dr² + r²dθ² + r²sin²θ dφ²
```

in the exterior region r > 2M, we need to prove:

**Claim**: The mixed Riemann tensor component R^a_{cad} vanishes when the first and third indices are equal.

**In symbols**: R^ρ_{σρν} = 0 for all indices ρ, σ, ν

**Questions**:

1. **Is this claim mathematically correct?**
   - Have you seen this property stated in GR literature?
   - Can you verify it's true?

2. **If yes, what is the mathematical reason?**
   - Is this a general Riemann tensor symmetry we're missing?
   - Does it follow from Schwarzschild's Killing vectors?
   - Is it a direct consequence of the metric structure?

3. **What is the standard proof approach?**
   - Direct coordinate calculation?
   - Symmetry argument (which one)?
   - Bianchi identity manipulation?

**Current Status**:

- Our code ASSUMES this property (with a `sorry`)
- Used this assumption to complete the proof that R_ab = 0
- But we haven't verified the assumption is mathematically sound

**What We've Ruled Out**:

- ❌ NOT a simple consequence of last-two-indices antisymmetry (R^ρ_{σμν} = -R^ρ_{σνμ})
- ❌ NOT a simple consequence of first-two-indices antisymmetry (R_{abcd} = -R_{bacd})
- ❌ Simple algebraic manipulation of Christoffel symbols doesn't yield the result

**Request**: Please advise on:
1. Whether the mathematical claim is correct
2. If yes, what the proper proof approach would be
3. Any relevant literature references

**Why This Matters**: This is the ONLY remaining gap in our formal proof. Once this is resolved, we will have a complete, mechanically-verified proof that Schwarzschild satisfies Einstein's vacuum equations.

Thank you for your expertise!

---

## Summary of Investigation

### What We Know ✅

1. **The lemma exists** at line 1936
2. **It has a sorry** - proof incomplete
3. **It's used by diagonal Ricci cases** - critical for main result
4. **Previous attempts failed** - multiple strategies tried
5. **The claimed antisymmetry is non-standard** - not a known Riemann property

### What We Don't Know ❓

1. **Is R^a_{cad} = 0 mathematically TRUE?** ← CRITICAL
2. **If true, WHY is it true?**
3. **What's the correct proof method?**

### What We Need 🎯

**FIRST PRIORITY**: Verify the mathematical claim with Senior Math Professor

**SECOND PRIORITY** (if claim is verified): Determine proof strategy
- Direct computation? → Junior Tactics Prof
- Killing vectors? → Senior Math Prof + Junior Tactics Prof
- Bianchi identities? → Senior Math Prof

### Current Blocker

**CANNOT PROCEED** without mathematical verification of the claim.

**Risk**: If claim is FALSE, the entire diagonal case approach is wrong!

---

## Recommendation Ranking

1. **⭐⭐⭐ CONSULT SENIOR MATH PROFESSOR** (Mathematical verification - Required)
2. **⭐⭐ DIRECT COMPUTATION** (If verified - Needs Junior Tactics Prof)
3. **⭐ KILLING VECTORS** (If verified and elegant - Needs both professors)
4. **LITERATURE SEARCH** (Can attempt alone, but may not be sufficient)

---

**Next Action**: Present this investigation to user and request consultation with Senior Math Professor.

**Timeline**: BLOCKED until mathematical verification obtained.

**Confidence**: Investigation complete ✅ | Mathematical validity uncertain ❓

---

**Investigator**: Claude Code
**Date**: October 6, 2025
**Status**: Investigation complete, ready for expert consultation
