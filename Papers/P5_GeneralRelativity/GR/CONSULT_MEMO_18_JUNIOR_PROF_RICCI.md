# Consultation Memo #18: Ricci Implementation - Tactical Guidance Needed

**Date:** 2025-10-02
**To:** Junior Professor (Tactical)
**From:** Implementation Team
**Re:** Implementing Option B for Ricci Vanishing - First=Third Index Blocker

---

## Situation

Senior Professor mandated **Option B (Explicit Component Calculation)** for proving `Ricci_zero_ext`.

I've begun implementation but hit a tactical blocker regarding index symmetries.

**Status:**
- ✅ All prerequisite lemmas audited
- ✅ Proof structure understood
- ⚠️ Blocked on handling first=third index equality

---

## The Blocker: First=Third Index Pattern

### Ricci Contraction Structure

For Ricci tensor R_ab = Σ_ρ R_ρaρb, the sum expands to:

**Off-diagonal example (a=t, b=r):**
```
R_tr = R_tttr + R_rtrr + R_θtθr + R_φtφr
```

**Pattern analysis:**
- R_tttr: indices (t,t,t,r) → **first two equal**
- R_rtrr: indices (r,t,r,r) → **last two equal**
- R_θtθr: indices (θ,t,θ,r) → **first and third equal** ⚠️
- R_φtφr: indices (φ,t,φ,r) → **first and third equal** ⚠️

### Available Symmetry Lemmas

```lean
-- Covers first TWO indices equal
@[simp] lemma Riemann_first_equal_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ)
    (h_sin_nz : Real.sin θ ≠ 0) (a c d : Idx) :
  Riemann M r θ a a c d = 0

-- Covers last TWO indices equal
@[simp] lemma Riemann_last_equal_zero (M r θ : ℝ) (a b c : Idx) :
  Riemann M r θ a b c c = 0
```

### What's Missing

**We need to prove:** R_ρaρb = 0 when indices are (ρ, a, ρ, b) with ρ ≠ a and ρ ≠ b.

This is **first and third indices equal**, not covered by existing lemmas!

---

## Question 1: How to Prove First=Third Equal Cases?

### Option A: Derive from Existing Symmetries?

Can we derive `Riemann M r θ a b a d = 0` from:
- `Riemann_swap_a_b_ext`: R_{abcd} = -R_{bacd}
- `Riemann_swap_c_d`: R_{abcd} = -R_{abdc}
- Pair symmetry (if it exists): R_{abcd} = R_{cdab}?

**Attempted chain:**
```
R_ρaρb
  = R_ρbρa  (swap c,d? but that gives -R_ρbaρ, not helpful)
  = ...?
```

**Question:** Is there a derivation path I'm missing?

### Option B: Use Explicit Zero Component Lemmas?

I found ~60 lemmas like:
- `R_tr_tθ_zero`: Riemann M r θ Idx.t Idx.r Idx.t Idx.θ = 0
- `R_rθ_tφ_zero`: Riemann M r θ Idx.r Idx.θ Idx.t Idx.φ = 0
- etc.

**Checking:** Do lemmas exist for the specific ρaρb patterns?

For R_θtθr (indices θ,t,θ,r):
- Need `R_θt_θr_zero` or equivalent
- Let me search...

**Question:** Should I use these explicit lemmas instead of a general first=third property?

### Option C: Prove New Lemma?

```lean
lemma Riemann_first_third_equal_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ)
    (h_sin_nz : Real.sin θ ≠ 0) (a b d : Idx) :
  Riemann M r θ a b a d = 0 := by
  -- How to prove this?
  sorry
```

**Question:** What's the proof strategy for this? Can it use the alternation identity we just proved?

---

## Question 2: For Diagonal Cases, What's the Algebraic Pattern?

### Example: R_tt

After eliminating R_tttt = 0, we have:
```lean
R_tt = R_rtrt + R_θtθt + R_φtφt
```

Using the reduction formulas:
```lean
Riemann_trtr_reduce:
  R_trtr = g_tt * (- ∂_r Γ^t_{tr} + Γ^t_{tr} Γ^r_{rr} - Γ^t_{tr} Γ^t_{tr})

Riemann_tθtθ_reduce:
  R_tθtθ = g_tt * (- ∂_θ Γ^t_{tθ} + Γ^t_{tr} Γ^r_{θθ})

Riemann_tφtφ_reduce:
  R_tφtφ = g_tt * Γ^t_{tr} Γ^r_{φφ}
```

**Question:** Do these three formulas sum to zero algebraically?

**Approach A:** Factor out g_tt and prove the sum of parenthesized terms = 0?
```lean
R_tt = g_tt * (term1 + term2 + term3)
```

**Approach B:** Expand each fully using Christoffel formulas and metric components, then use field_simp + ring?

**Approach C:** Each component is individually zero (not just their sum)?

**What you need from me:** Which approach should I take? Do I need additional lemmas?

---

## Question 3: Christoffel Symbol Differentiation

If the diagonal cases require proving derivatives like:
```
∂_r Γ^t_{tr} = ...
```

**Do we have lemmas for:**
- `dCoord_r (fun r θ => Γtot M r θ Idx.t Idx.t Idx.r) r θ = ...`?
- Or do I need to prove these using C² infrastructure?

**Context:** We have:
- ✅ `Γtot_differentiable_r/θ` (C¹ smoothness)
- ✅ `dCoord_g_differentiable_r/θ` (C² for metric)
- ✅ `dCoord_ContractionC_expanded` (product rule distribution)

**Question:** Are Christoffel derivatives already computed, or do I compute them on-demand during the proof?

---

## Current Implementation Attempt

```lean
theorem Ricci_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
    ∀ a b, RicciContraction M r θ a b = 0 := by
  intro a b
  unfold RicciContraction

  -- Extract hypotheses
  have hM := h_ext.hM
  have hr_ex := h_ext.hr_ex
  have hr_nz : r ≠ 0 := by linarith [hM, hr_ex]

  -- Case split on 16 Ricci components
  cases a <;> cases b

  all_goals {
    simp only [sumIdx_expand]
  }

  -- Off-diagonal: Example R_tr
  case t.r {
    -- Goal: R_tttr + R_rtrr + R_θtθr + R_φtφr = 0
    -- ✅ R_tttr: first=second → Riemann_first_equal_zero_ext
    -- ✅ R_rtrr: third=fourth → Riemann_last_equal_zero
    -- ❌ R_θtθr: first=third → ???
    -- ❌ R_φtφr: first=third → ???
    sorry -- BLOCKED: Need first=third lemma
  }

  -- ... 11 more off-diagonal cases (same blocker)

  -- Diagonal: Example R_tt
  case t.t {
    -- Goal: R_tttt + R_rtrt + R_θtθt + R_φtφt = 0
    rw [Riemann_first_equal_zero_ext M r θ Idx.t Idx.t h_ext h_sin_nz]
    simp only [zero_add]
    -- Goal: R_rtrt + R_θtθt + R_φtφt = 0
    rw [Riemann_trtr_reduce, Riemann_tθtθ_reduce, Riemann_tφtφ_reduce]
    -- Goal: (formula1) + (formula2) + (formula3) = 0
    sorry -- BLOCKED: Need algebraic cancellation strategy
  }

  -- ... 3 more diagonal cases (same pattern)
```

---

## Specific Tactical Requests

### Request 1: First=Third Lemma

**Please provide ONE of:**

A. **Derivation path** showing how to get R_{aℓad} = 0 from existing symmetries

B. **Explicit lemma names** to use for ρaρb patterns (if they exist)

C. **Proof skeleton** for a new `Riemann_first_third_equal_zero_ext` lemma

### Request 2: Diagonal Cancellation

**Please provide:**

- **Tactical sequence** to prove R_rtrt + R_θtθt + R_φtφt = 0
- Which lemmas to expand?
- What normalization tactics? (field_simp? ring? both?)
- Any intermediate helper lemmas needed?

### Request 3: Code Template

If possible, **a working code skeleton for one complete case** (either off-diagonal or diagonal) showing:
- Exact simp/rw lemmas to use
- Tactical sequence
- Expected intermediate goals

---

## Context: What's Already Complete

**Infrastructure (Zero Sorries):**
- ✅ C³/C² smoothness (lines 357-417, 1660-1704)
- ✅ Product rule distribution (lines 2118-2255)
- ✅ Alternation identity (lines 2228-2256)

**Component Lemmas:**
- ✅ 6 reduction formulas (Riemann_trtr_reduce, etc.)
- ✅ ~60 explicit zero lemmas (R_tr_tθ_zero, etc.)
- ✅ Symmetries (swap_a_b, swap_c_d, first_equal, last_equal)

**File State:**
- Checkpoint: `f6e02be` (working, 1 sorry)
- Current: Restored to checkpoint, ready for implementation

---

## Timeline Estimate

**With your guidance:**
- Off-diagonal cases: 30 minutes (once first=third resolved)
- Diagonal cases: 30-60 minutes (depending on cancellation complexity)
- **Total: 1-2 hours to completion**

**Without guidance:**
- Would need to audit/prove ~48 individual zero lemmas
- Plus figure out diagonal cancellation independently
- **Estimated: 4-6 hours, high error risk**

---

## Summary

I understand the **strategic approach** (Option B, component calculation) and have the **proof structure** ready.

I'm blocked on two **tactical issues**:
1. How to handle first=third index equality in off-diagonals
2. How to prove diagonal formulas cancel to zero

**Ready to implement immediately** upon receiving tactical guidance on these two points.

---

**Awaiting your tactical instructions.**

Thank you for your continued guidance!
