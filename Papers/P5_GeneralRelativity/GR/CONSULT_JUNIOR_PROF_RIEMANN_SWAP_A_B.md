# Consultation Request: Prove Riemann_swap_a_b (First-Pair Antisymmetry)

**To:** Junior Tactics Professor
**From:** Claude Code (AI Agent)
**Date:** October 8, 2025, 11:40 PM
**Priority:** High
**Subject:** Final sorry elimination - Need tactical approach for Riemann tensor first-pair antisymmetry

---

## Executive Summary

We've successfully eliminated the sorry in `Kretschmann_six_blocks` (Invariants.lean) and achieved **zero sorries** in that file! 🎉

However, there's **one remaining sorry** in the entire 6,650-line Paper 5 formalization:

**`Riemann_swap_a_b`** (Riemann.lean:1228-1230) - First-pair antisymmetry of the Riemann tensor

**Request:** We need your tactical expertise to prove this lemma and achieve **complete zero-sorry formalization**.

---

## The Lemma to Prove

### Current State (Riemann.lean:1220-1230)

```lean
/-- First-pair antisymmetry for the (all-lowered) Riemann tensor of the Levi–Civita connection.
    It follows from metric compatibility (`∇g = 0`) and the Ricci identity on `g`:
    0 = [∇_c, ∇_d] g_{ab} = -R_{aecd} g_{eb} - R_{becd} g_{ae} = -R_{abcd} - R_{bacd}
    Hence R_{bacd} = -R_{abcd}.

    TODO: Complete proof by implementing ricci_identity_on_g using the nabla_g_zero
    framework (lines 1229-1710). Computational proof (16 cases) times out.
    Standard textbook result: MTW Box 8.5, Wald Appendix B. -/
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  sorry  -- TODO: Prove via ricci_identity_on_g once that lemma is implemented
```

### Mathematical Background

**What we're proving:** R_{bacd} = -R_{abcd} (antisymmetry in first two indices)

**Why it's true:** This is a fundamental Riemann tensor symmetry that follows from:
1. The Riemann tensor is defined via the covariant derivative commutator
2. Metric compatibility: ∇_μ g_{ab} = 0
3. Ricci identity applied to the metric

**Textbook references:**
- Misner, Thorne, Wheeler "Gravitation" Box 8.5 (page 223)
- Wald "General Relativity" Appendix B

---

## Why This Matters

### Impact on the Formalization

**Upstream dependency:** This lemma is used by:
1. `Riemann_sq_swap_a_b` (Invariants.lean:119-121) - Squares are symmetric under first-pair swap
2. `Kretschmann_block_sq` (Invariants.lean:191-204) - Generic block collapse lemma
3. All 6 Kretschmann block calculations

**Current workaround:** We use the sorry as an axiom, which works for compilation but is not satisfying for a complete formalization.

**Goal:** Replace the sorry with a complete proof to achieve **100% zero-sorry formalization**.

---

## Available Infrastructure

### What We Have in Riemann.lean

#### 1. Riemann Tensor Definition (Lines 1018-1023)

```lean
/-- The (4,0) Riemann curvature tensor with all indices lowered.
    R_{abcd} = g_{ae} R^e_{bcd}
    where R^e_{bcd} = RiemannUp M r θ e b c d. -/
def Riemann (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  sumIdx (fun e => g M a e r θ * RiemannUp M r θ e b c d)
```

#### 2. RiemannUp Definition (Lines 963-968)

```lean
/-- Riemann curvature tensor R^a_{bcd} = ∂_c Γ^a_{bd} - ∂_d Γ^a_{bc} + Γ^a_{ce} Γ^e_{bd} - Γ^a_{de} Γ^e_{bc}.
    This is the (1,3) version with one upper index. -/
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (Γtot M r θ a b) r θ - dCoord d (Γtot M r θ a b) r θ
  + sumIdx (fun e => Γtot M r θ a c e * Γtot M r θ e b d)
  - sumIdx (fun e => Γtot M r θ a d e * Γtot M r θ e b c)
```

#### 3. Last-Pair Antisymmetry (Already Proven - Line 2608)

```lean
/-- Last-pair antisymmetry: R_{abdc} = -R_{abcd}. -/
lemma Riemann_swap_c_d (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b d c = - Riemann M r θ a b c d := by
  unfold Riemann
  simp only [sumIdx_expand]
  congr 1
  · rw [RiemannUp_swap_c_d]; ring
  · rw [RiemannUp_swap_c_d]; ring
  · rw [RiemannUp_swap_c_d]; ring
  · rw [RiemannUp_swap_c_d]; ring
```

**Key insight:** This worked by proving `RiemannUp_swap_c_d` first, then lifting to `Riemann`.

#### 4. Covariant Derivative Framework (Lines 1229-1710)

This extensive section includes:
- `nabla` definition (line 1233): Covariant derivative of a (0,2) tensor
- `nabla_g_zero` (line 1317): Metric compatibility ∇g = 0
- Partial derivatives of g (lines 1342-1710)

**Status:** Framework exists but not yet connected to Riemann symmetries.

---

## Attempted Approaches (That Failed)

### Attempt 1: Direct Computational Proof (16 Cases)

**Strategy:** Since we have 4 indices (t,r,θ,φ), we could prove by cases:
- For each of 4 choices of `a`
- For each of 4 choices of `b`
- Compute both `Riemann b a c d` and `Riemann a b c d` explicitly
- Verify equality using our closed-form component lemmas

**Attempt:**
```lean
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  cases a <;> cases b <;> (unfold Riemann; simp only [sumIdx_expand]; ring)
```

**Result:** ❌ **Timeout** (deterministic timeout at ~200k heartbeats)

**Why it failed:** Even though we only have 16 cases (4×4), each case involves:
- Expanding `sumIdx` (4 terms)
- Expanding `RiemannUp` (4 Christoffel products)
- Expanding each Christoffel symbol (9 formulas)
- Ring normalization of resulting rational expressions

This creates a combinatorial explosion that exceeds the heartbeat limit.

### Attempt 2: Prove RiemannUp_swap_a_b First

**Strategy:** Following the pattern of `Riemann_swap_c_d`, try to prove antisymmetry for `RiemannUp` first.

**Challenge:**
```lean
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (Γtot M r θ a b) r θ - dCoord d (Γtot M r θ a b) r θ + ...
```

The first index `a` appears in `Γtot M r θ **a** b`, not symmetrically with `b`. So swapping a↔b gives:
```lean
  dCoord c (Γtot M r θ **b a**) r θ - ...
```

This is a **different Christoffel symbol** (Γ^b_{ac} vs Γ^a_{bc}), not just a sign flip.

**Conclusion:** Can't prove `RiemannUp_swap_a_b` directly from definition. Need the Ricci identity.

---

## Recommended Approach: Ricci Identity on Metric

### Mathematical Strategy (From User's Earlier Guidance)

The user provided this minimal dependency chain:

#### Step 1: Ricci Identity on Metric

**Lemma to prove:**
```lean
lemma ricci_identity_on_g (M r θ : ℝ) (a b c d : Idx) :
  nabla (nabla g M) M r θ c d a b - nabla (nabla g M) M r θ d c a b
  = - sumIdx (fun e => Riemann M r θ a e c d * g M e b r θ)
    - sumIdx (fun e => Riemann M r θ b e c d * g M a e r θ) := by
  sorry  -- TODO: Expand commutator and match terms
```

**What it says:** [∇_c, ∇_d] g_{ab} = -R_{aecd} g_{eb} - R_{becd} g_{ae}

#### Step 2: Use Metric Compatibility

We already have `nabla_g_zero` (line 1317):
```lean
lemma nabla_g_zero (M r θ : ℝ) (a b c : Idx) :
  nabla (g M) M r θ c a b = 0
```

**Implication:** If ∇_c g_{ab} = 0, then ∇_d (∇_c g_{ab}) = 0 for all d.

#### Step 3: Derive First-Pair Antisymmetry

```lean
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  -- Use ricci_identity_on_g
  have h := ricci_identity_on_g M r θ a b c d

  -- Left side is zero by nabla_g_zero applied twice
  have lhs_zero : nabla (nabla g M) M r θ c d a b = 0 := by
    sorry  -- TODO: Show second derivative of metric is zero
  have lhs_zero' : nabla (nabla g M) M r θ d c a b = 0 := by
    sorry  -- TODO: Same

  -- So the right side equals zero
  rw [lhs_zero, lhs_zero'] at h
  simp at h

  -- This gives: 0 = -R_{abcd} - R_{bacd} (after simplifying sums using diagonal metric)
  -- Therefore: R_{bacd} = -R_{abcd}
  sorry  -- TODO: Extract and manipulate terms
```

---

## Specific Questions for Junior Tactics Professor

### Q1: Proving ricci_identity_on_g

**Challenge:** This requires expanding the covariant derivative commutator and matching terms.

**What we have:**
- `nabla` definition (line 1233)
- Christoffel symbols (lines 570-656)
- Partial derivatives (lines 1342-1710)

**Question:** What's the best tactical approach?
- Should we unfold `nabla` directly and compute both terms?
- Or is there a more abstract way using commutator properties?
- Can we leverage the existing `nabla_g_zero` lemma to simplify?

### Q2: Second Covariant Derivative of Metric

**Challenge:** We need `nabla (nabla g M) M r θ c d a b = 0`.

**What we have:**
- `nabla_g_zero`: First derivative is zero

**Question:**
- Can we use a general lemma: "derivative of zero is zero"?
- Or do we need to expand `nabla (nabla g M)` explicitly?
- Is there a chain rule or product rule for `nabla` we should use?

### Q3: Simplifying the Metric Sums

**Challenge:** After applying Ricci identity, we get:
```lean
0 = - sumIdx (fun e => Riemann M r θ a e c d * g M e b r θ)
    - sumIdx (fun e => Riemann M r θ b e c d * g M a e r θ)
```

For Schwarzschild, `g M e b r θ = 0` when `e ≠ b` (diagonal metric).

**Question:**
- How do we simplify `sumIdx` when the metric is diagonal?
- Should we prove a general lemma: `sumIdx (fun e => f e * g_diag e b) = f b * g_diag b b`?
- Or do case analysis on b and use `g_off_diag_zero` lemmas?

### Q4: Pattern from Riemann_swap_c_d

**Observation:** The proof of `Riemann_swap_c_d` worked by:
1. Proving `RiemannUp_swap_c_d` first (the (1,3) version)
2. Lifting to `Riemann` using `unfold Riemann; simp only [sumIdx_expand]; congr 1; rw [...]; ring`

**Question:**
- Is there an analogous path for first-pair antisymmetry?
- Can we prove something about the *symmetry of second covariant derivatives*?
- Or is the Ricci identity approach fundamentally different?

---

## Available Code Infrastructure

### Relevant Definitions

**From Riemann.lean:**

```lean
-- Line 1233: Covariant derivative (2nd order)
def nabla (T : ℝ → ℝ → ℝ → Idx → Idx → ℝ)
    (M r θ : ℝ) (c a b : Idx) : ℝ :=
  dCoord c (T M r θ a b) r θ
  - sumIdx (fun d => Γtot M r θ d a c * T M r θ d b)
  - sumIdx (fun d => Γtot M r θ d b c * T M r θ a d)

-- Line 1317: Metric compatibility
lemma nabla_g_zero (M r θ : ℝ) (a b c : Idx) :
  nabla (g M) M r θ c a b = 0 := by
  unfold nabla
  simp only [sumIdx_expand]
  unfold dCoord Γtot
  simp only [g_deriv_r, g_deriv_theta]
  cases a <;> cases b <;> cases c <;> simp [Γ_diag_expand]
  all_goals ring

-- Line 1018: Lowered Riemann tensor
def Riemann (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  sumIdx (fun e => g M a e r θ * RiemannUp M r θ e b c d)

-- Line 963: Raised Riemann tensor
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (Γtot M r θ a b) r θ - dCoord d (Γtot M r θ a b) r θ
  + sumIdx (fun e => Γtot M r θ a c e * Γtot M r θ e b d)
  - sumIdx (fun e => Γtot M r θ a d e * Γtot M r θ e b c)
```

### Metric Properties

**From Schwarzschild.lean:**

```lean
-- Diagonal metric
lemma g_off_diag_zero (M : ℝ) (a b : Idx) (r θ : ℝ) (h : a ≠ b) :
  g M a b r θ = 0

-- Inverse metric diagonal
lemma gInv_off_diag_zero (M : ℝ) (a b : Idx) (r θ : ℝ) (h : a ≠ b) :
  gInv M a b r θ = 0
```

---

## Proposed Proof Sketch

Based on the mathematical strategy, here's a sketch:

```lean
-- Helper: Second covariant derivative of metric is zero
lemma nabla_nabla_g_zero (M r θ : ℝ) (a b c d : Idx) :
  nabla (nabla g M) M r θ c d a b = 0 := by
  -- Since ∇_d g_{ab} = 0, taking ∇_c of it gives 0
  sorry  -- TODO: Formalize "derivative of constant zero is zero"

-- Main lemma: Ricci identity applied to metric
lemma ricci_identity_on_g (M r θ : ℝ) (a b c d : Idx) :
  nabla (nabla g M) M r θ c d a b - nabla (nabla g M) M r θ d c a b
  = - sumIdx (fun e => Riemann M r θ a e c d * g M e b r θ)
    - sumIdx (fun e => Riemann M r θ b e c d * g M a e r θ) := by
  -- Expand both sides and match terms
  unfold nabla Riemann RiemannUp
  simp only [sumIdx_expand]
  -- This will be tedious but mechanical
  sorry  -- TODO: Expand and verify term-by-term

-- Final goal: First-pair antisymmetry
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  have h := ricci_identity_on_g M r θ a b c d
  rw [nabla_nabla_g_zero, nabla_nabla_g_zero] at h
  simp at h

  -- For diagonal metric: sumIdx (fun e => f e * g e b) = f b * g b b
  -- So: 0 = -R_{abcd}·g_{bb} - R_{bacd}·g_{aa}
  -- Since g_{aa} ≠ 0 and g_{bb} ≠ 0, we can divide
  -- TODO: Formalize this step carefully
  sorry
```

---

## Urgency and Priority

**Why we can't leave this sorry:**

1. **Completeness:** This is the *last remaining sorry* in 6,650 lines. We're at 99.98% completion!
2. **Mathematical integrity:** While it's a textbook result, having a sorry undermines the formalization's credibility
3. **Dependency:** This lemma is used in the Kretschmann calculation, one of our main results
4. **Satisfaction:** We've come so far - let's finish strong!

**Time estimate:** 4-8 hours of focused work (based on complexity of nabla_g_zero proof)

---

## Deliverables Requested

From the Junior Tactics Professor, we need:

1. **Proof of `ricci_identity_on_g`** - The key commutator identity
2. **Proof of `nabla_nabla_g_zero`** - Second derivative of metric is zero
3. **Completion of `Riemann_swap_a_b`** - Extracting the antisymmetry from the Ricci identity

**Tactical guidance specifically on:**
- Best way to expand nested `nabla` applications
- How to handle `sumIdx` with diagonal metric efficiently
- Pattern for proving "derivative of zero is zero" in our framework

---

## References

**Textbook derivations:**
- MTW "Gravitation" (1973), Box 8.5, pages 222-223
- Wald "General Relativity" (1984), Appendix B, pages 432-433
- Carroll "Spacetime and Geometry" (2004), Section 3.7, pages 133-135

**Existing infrastructure in our code:**
- `Riemann.lean` lines 1220-1710 (covariant derivative framework)
- `Riemann.lean` lines 2608-2615 (successful proof of last-pair antisymmetry)
- `Schwarzschild.lean` lines 127-226 (metric properties, diagonal structure)

---

## Expected Outcome

Once `Riemann_swap_a_b` is proven:

✅ **Zero sorries** in Riemann.lean (4,058 lines)
✅ **Zero sorries** in Schwarzschild.lean (2,284 lines)
✅ **Zero sorries** in Invariants.lean (308 lines)
✅ **Zero axioms** project-wide
✅ **100% complete formalization** of Schwarzschild spacetime curvature

**Physical results fully proven:**
- 9 Christoffel symbols
- 6 Riemann components
- Ricci tensor R_μν = 0 (vacuum Einstein equations)
- Kretschmann invariant K = 48M²/r⁶

This would be a **publication-ready, complete formalization** with no gaps!

---

**Prepared by:** Claude Code (AI Agent)
**Date:** October 8, 2025, 11:40 PM
**Status:** Awaiting tactical guidance for final sorry elimination
**Next step:** Implement proof strategy once Junior Professor provides tactical approach

---

## Appendix: Full Lemma Context

For reference, here's the exact current state of the lemma and surrounding code:

**File:** `GR/Riemann.lean`
**Lines:** 1220-1230

```lean
/-- First-pair antisymmetry for the (all-lowered) Riemann tensor of the Levi–Civita connection.
    It follows from metric compatibility (`∇g = 0`) and the Ricci identity on `g`:
    0 = [∇_c, ∇_d] g_{ab} = -R_{aecd} g_{eb} - R_{becd} g_{ae} = -R_{abcd} - R_{bacd}
    Hence R_{bacd} = -R_{abcd}.

    TODO: Complete proof by implementing ricci_identity_on_g using the nabla_g_zero
    framework (lines 1229-1710). Computational proof (16 cases) times out.
    Standard textbook result: MTW Box 8.5, Wald Appendix B. -/
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  sorry  -- TODO: Prove via ricci_identity_on_g once that lemma is implemented
```

**Used by:**
- `Riemann_sq_swap_a_b` (Invariants.lean:119) → `Kretschmann_block_sq` (Invariants.lean:191) → `Kretschmann_six_blocks` (Invariants.lean:211) → `Kretschmann_exterior_value` (Invariants.lean:256)

**Dependencies available:**
- All Christoffel symbols proven (Schwarzschild.lean:570-656)
- All partial derivatives of metric proven (Riemann.lean:1342-1710)
- `nabla_g_zero` proven (Riemann.lean:1317-1337)
- `Riemann_swap_c_d` proven (Riemann.lean:2608) - similar structure, successful pattern
