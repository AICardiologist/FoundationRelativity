# Consultation Request: Junior Tactics Professor

**Date**: October 7, 2025
**From**: Formal Verification Team (Lean 4)
**To**: Junior Tactics Professor (Lean Proof Engineering)
**Subject**: Tactical Guidance for Riemann Component Lemmas
**Priority**: HIGH - Blocking Phase 3 Diagonal Reconstruction

---

## Quick Summary

**We need**: Tactical guidance for proving ~16 Riemann tensor component lemmas

**Challenge**: Each lemma requires expanding a complex tensor definition, substituting Christoffel symbols, computing derivatives, and algebraic simplification

**Proof-of-Concept**: We want to start with ONE lemma (R^t_{rtr}) to establish the tactical pattern, then scale to the remaining 15

**Context**: Senior Math Professor verified our previous approach was mathematically wrong. We must rebuild diagonal Ricci cases using explicit component values and algebraic cancellation.

---

## The Problem

### Background (Why We're Here)

Our previous approach assumed R^a_{cad} = 0 (when first and third indices equal). **This was mathematically FALSE**.

**Senior Math Professor verified**: These components are actually **non-zero**, but they **cancel when summed**.

**Example**:
```
R_rr = R^t_{rtr} + R^r_{rrr} + R^θ_{rθr} + R^φ_{rφr}
     = 2M/(r²(r-2M)) + 0 + (-M/(r²(r-2M))) + (-M/(r²(r-2M)))
     = 0  [by cancellation]
```

We must now prove explicit values for each non-zero component.

### What We're Proving

**~16 component lemmas** of the form:

```lean
lemma RiemannUp_X_YZW_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.X Idx.Y Idx.Z Idx.W = <explicit value> := by
  sorry
```

Where `<explicit value>` is a concrete expression like `2*M / (r^2 * (r - 2*M))`.

---

## Proof-of-Concept: R^t_{rtr}

Let's focus on **ONE lemma** to establish the tactical pattern.

### The Target Lemma

```lean
lemma RiemannUp_t_rtr_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.t Idx.r Idx.t Idx.r = 2*M / (r^2 * (r - 2*M)) := by
  sorry
```

**Mathematical verification**: Senior Math Professor confirmed this value is correct.

### Step-by-Step Derivation (From Senior Math Prof)

#### Step 1: Expand RiemannUp Definition

**Definition** (line 1639-1643 of Riemann.lean):
```lean
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (fun r θ => Γtot M r θ a d b) r θ
  - dCoord d (fun r θ => Γtot M r θ a c b) r θ
  + sumIdx (fun e => Γtot M r θ a c e * Γtot M r θ e d b)
  - sumIdx (fun e => Γtot M r θ a d e * Γtot M r θ e c b)
```

**For R^t_{rtr}** (a=t, b=r, c=t, d=r):
```
RiemannUp t r t r =
  dCoord t (fun r θ => Γtot M r θ t r r) r θ
  - dCoord r (fun r θ => Γtot M r θ t t r) r θ
  + sumIdx (fun e => Γtot M r θ t t e * Γtot M r θ e r r)
  - sumIdx (fun e => Γtot M r θ t r e * Γtot M r θ e t r)
```

#### Step 2: Substitute Christoffel Symbols

**Known values** (from Schwarzschild.lean):
- `Γtot M r θ Idx.t Idx.r Idx.r` = `Γ_t_rr M` = **0**
- `Γtot M r θ Idx.t Idx.t Idx.r` = `Γ_t_tr M r` = **M/(r*(r-2*M))**
- `Γtot M r θ Idx.r Idx.r Idx.r` = `Γ_r_rr M r` = **-M/(r*(r-2*M))**
- Most others are **0** (sparse structure)

**After substitution**:
```
RiemannUp t r t r =
  dCoord t (fun r θ => 0) r θ
  - dCoord r (fun r θ => Γ_t_tr M r) r θ
  + sumIdx (fun e => Γtot t t e * Γtot e r r)  [most terms zero]
  - sumIdx (fun e => Γtot t r e * Γtot e t r)  [most terms zero]
```

Simplifies to:
```
= 0 - ∂_r(Γ_t_tr)
  + (Γ_t_tr * Γ_r_rr)  [only non-zero product]
  - (Γ_t_tr)²          [only non-zero product]
```

**Using** Γ_r_rr = -Γ_t_tr:
```
= -∂_r(Γ_t_tr) + Γ_t_tr * (-Γ_t_tr) - (Γ_t_tr)²
= -∂_r(Γ_t_tr) - 2*(Γ_t_tr)²
```

#### Step 3: Compute Derivative

**Need**: `deriv (fun r => M/(r*(r-2*M))) r`

**Calculation** (quotient rule):
```
f(r) = M / (r² - 2Mr)

f'(r) = -M * (2r - 2M) / (r² - 2Mr)²
      = -M * 2(r - M) / (r*(r-2M))²
```

#### Step 4: Substitute and Simplify

**Goal becomes**:
```
-(-M*2(r-M)/(r*(r-2M))²) - 2*(M/(r*(r-2M)))²
= M*2(r-M)/(r*(r-2M))² - 2*M²/(r*(r-2M))²
= (2M(r-M) - 2M²) / (r²*(r-2M)²)
= (2Mr - 2M² - 2M²) / (r²*(r-2M)²)
= 2M(r - 2M) / (r²*(r-2M)²)
= 2M / (r²*(r-2M))
```

**This matches the target!** ✓

---

## Our Tactical Questions

### Question 1: Christoffel Symbol Substitution

**How do we efficiently substitute Christoffel symbols?**

**Current infrastructure**:
- We have definitions for each Γ symbol (e.g., `Γ_t_tr`, `Γ_r_rr`)
- We have `Γtot` which dispatches to specific symbols based on indices

**Attempted approach**:
```lean
unfold RiemannUp
simp only [Γtot]
```

**Problem**: `Γtot` is a function that pattern-matches on indices. How do we get Lean to:
1. Recognize that with concrete indices (Idx.t, Idx.r, ...), `Γtot M r θ Idx.t Idx.t Idx.r` simplifies to `Γ_t_tr M r`?
2. Recognize that most Γ values are 0 and eliminate those terms?

**Options we've considered**:
- **Option A**: Prove lemmas like `Γtot M r θ Idx.t Idx.t Idx.r = Γ_t_tr M r`
- **Option B**: Use `cases` on indices to force pattern matching
- **Option C**: Custom simp lemmas for Γtot reduction

**What's the best tactical approach?**

### Question 2: Sum Elimination

**How do we eliminate zero terms from sumIdx?**

**Pattern**:
```lean
sumIdx (fun e => Γtot M r θ t t e * Γtot M r θ e r r)
```

**Most terms are zero** because Christoffel symbols are sparse. Only certain index combinations are non-zero.

**Need**: Tactic to:
1. Expand `sumIdx` to explicit sum over {t, r, θ, φ}
2. Substitute Γtot values for each e
3. Eliminate terms where either factor is 0
4. Collect the 1-2 non-zero terms

**Attempted**:
```lean
simp only [sumIdx_expand]  -- Expands to 4 terms
-- Then what? How to substitute and eliminate zeros?
```

**Should we**:
- Create simp lemmas for each Γtot value being 0 or non-zero?
- Use `split_ifs` on the Γtot definition?
- Something else?

### Question 3: Derivative Computation

**How do we compute derivatives of Christoffel symbols?**

**Example need**:
```lean
deriv (fun r => M / (r * (r - 2*M))) r = -M * 2 * (r - M) / (r * (r - 2*M))^2
```

**Questions**:
- Do we have derivative lemmas for quotients like `M/(r²-2Mr)`?
- Should we prove this as a separate helper lemma?
- What tactics work best for derivative calculations in Lean 4?
  - `simp [deriv_div, deriv_mul, ...]`?
  - `rw` with standard derivative rules?
  - Something else?

**Our derivative infrastructure** (from Schwarzschild.lean):
- We have `dCoord` which wraps `deriv` for coordinate derivatives
- We have proven some specific derivative lemmas (e.g., for metric components)
- Not sure if we have general quotient rule lemmas

**Should we**:
- Prove the derivative as a separate lemma first?
- Compute it inline in the main proof?
- Use a tactic that automates derivative calculation?

### Question 4: Algebraic Simplification

**How do we simplify the final algebraic expression?**

**Goal** (after derivative substitution):
```
M*2(r-M)/(r*(r-2M))² - 2*M²/(r*(r-2M))²
```

**Target**:
```
2M/(r²*(r-2M))
```

**Attempted tactics**:
- `field_simp [h_ext.r_pos, h_ext.r_ne_2M]` (clear denominators)
- `ring` (simplify numerator)

**Questions**:
- Is this the right tactical sequence?
- Do we need additional hypotheses (e.g., `r > 0`, `r ≠ 2M`)?
- What if `ring` doesn't close the goal? (`polyrith`? `nlinarith`?)

**Context we have**:
- `h_ext : Exterior M r θ` which includes:
  - `h_ext.r_pos : 0 < r`
  - `h_ext.r_ne_2M : r ≠ 2*M` (implicitly from `2*M < r`)

### Question 5: Proof Structure

**What's the best overall proof structure?**

**Option A: Inline everything**
```lean
lemma RiemannUp_t_rtr_ext ... := by
  unfold RiemannUp
  -- [massive proof with all steps inline]
  sorry
```

**Option B: Helper lemmas**
```lean
lemma deriv_Γ_t_tr (M r : ℝ) (hr : r > 2*M) :
  deriv (fun r => M/(r*(r-2*M))) r = ... := by sorry

lemma RiemannUp_t_rtr_ext ... := by
  unfold RiemannUp
  simp only [Γtot, sumIdx_expand]
  rw [deriv_Γ_t_tr M r h_ext.r_gt_2M]
  field_simp [h_ext.r_pos, h_ext.r_ne_2M]
  ring
```

**Option C: Computation tactics**
```lean
lemma RiemannUp_t_rtr_ext ... := by
  compute_riemann_component
  -- [hypothetical custom tactic that does all the work]
```

**What do you recommend for**:
- Readability?
- Maintainability?
- Ease of debugging when stuck?

---

## What We Have (Infrastructure)

### Christoffel Symbol Definitions

**File**: `GR/Schwarzschild.lean`

**Key definitions**:
```lean
def Γ_t_tr (M r : ℝ) : ℝ := M / (r * (r - 2*M))
def Γ_r_tt (M r : ℝ) : ℝ := M * (r - 2*M) / r^3
def Γ_r_rr (M r : ℝ) : ℝ := -M / (r * (r - 2*M))
def Γ_r_θθ (M r : ℝ) : ℝ := -(r - 2*M)
def Γ_r_φφ (M r θ : ℝ) : ℝ := -(r - 2*M) * Real.sin θ ^ 2
def Γ_θ_rθ (r : ℝ) : ℝ := 1 / r
def Γ_θ_φφ (θ : ℝ) : ℝ := -Real.sin θ * Real.cos θ
def Γ_φ_rφ (r : ℝ) : ℝ := 1 / r
def Γ_φ_θφ (θ : ℝ) : ℝ := Real.cos θ / Real.sin θ
```

**All others are zero** (sparse structure).

### Γtot Dispatcher

```lean
def Γtot (M r θ : ℝ) : Idx → Idx → Idx → ℝ := fun a b c =>
  classical
  if a = Idx.t ∧ b = Idx.t ∧ c = Idx.r then Γ_t_tr M r
  else if a = Idx.t ∧ b = Idx.r ∧ c = Idx.t then Γ_t_tr M r
  else if ... [many more cases]
  else 0
```

### RiemannUp Definition

```lean
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (fun r θ => Γtot M r θ a d b) r θ
  - dCoord d (fun r θ => Γtot M r θ a c b) r θ
  + sumIdx (fun e => Γtot M r θ a c e * Γtot M r θ e d b)
  - sumIdx (fun e => Γtot M r θ a d e * Γtot M r θ e c b)
```

### Derivative Infrastructure

```lean
-- dCoord wraps deriv for coordinate derivatives
noncomputable def dCoord (x : Idx) (f : ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ :=
  match x with
  | Idx.t => 0  -- ∂_t = 0 (staticity)
  | Idx.r => deriv (fun r => f r θ) r
  | Idx.θ => deriv (fun θ => f r θ) θ
  | Idx.φ => 0  -- ∂_φ = 0 (axisymmetry)
```

### sumIdx Helper

```lean
def sumIdx (f : Idx → ℝ) : ℝ :=
  f Idx.t + f Idx.r + f Idx.θ + f Idx.φ

@[simp] lemma sumIdx_expand (f : Idx → ℝ) :
  sumIdx f = f Idx.t + f Idx.r + f Idx.θ + f Idx.φ := rfl
```

### Exterior Region Hypotheses

```lean
structure Exterior (M r θ : ℝ) : Prop where
  M_pos : 0 < M
  r_gt_2M : 2 * M < r

-- Derived facts:
-- h_ext.r_pos : 0 < r (from 2*M < r and M > 0)
-- h_ext.r_ne_2M : r ≠ 2*M
-- h_ext.r_ne_zero : r ≠ 0
```

---

## Specific Tactical Requests

### Request 1: Proof-of-Concept for R^t_{rtr} ⭐⭐⭐

**Please provide**: A complete proof of `RiemannUp_t_rtr_ext` with annotations explaining each tactic.

**We need to understand**:
- How to unfold and substitute Christoffel symbols
- How to eliminate zero terms from sums
- How to compute the derivative
- How to simplify the algebra

**Deliverable**: Annotated proof we can use as a template for the other 15 components.

### Request 2: Pattern for Zero Components

**Some components are zero by antisymmetry**:
```lean
lemma RiemannUp_r_rrr_ext : RiemannUp M r θ Idx.r Idx.r Idx.r Idx.r = 0 := by
  -- Should follow from R^a_{bcc} = -R^a_{bcb} antisymmetry
  sorry
```

**Question**: Can we prove this using the existing `RiemannUp_swap_mu_nu` lemma?

**Existing lemma** (line 1138):
```lean
lemma RiemannUp_swap_mu_nu (M r θ : ℝ) (ρ σ μ ν : Idx) :
  RiemannUp M r θ ρ σ μ ν = - RiemannUp M r θ ρ σ ν μ
```

**Attempted**:
```lean
have h := RiemannUp_swap_mu_nu M r θ Idx.r Idx.r Idx.r Idx.r
-- h : RiemannUp r r r r = -RiemannUp r r r r
linarith  -- Should prove RiemannUp r r r r = 0
```

**Does this work?** If not, what's the right approach?

### Request 3: Derivative Lemma Template

**We'll need ~4-6 derivative lemmas** for different Christoffel symbols.

**Can you provide a template** for proving derivative lemmas like:
```lean
lemma deriv_Γ_t_tr (M r : ℝ) (hr_pos : 0 < r) (hr_ne_2M : r ≠ 2*M) :
  deriv (fun r => M / (r * (r - 2*M))) r = -M * 2 * (r - M) / (r * (r - 2*M))^2 := by
  sorry
```

**What tactics should we use** for derivative computation?

### Request 4: Generalization Strategy

**Pattern observation**: All component lemmas have similar structure:
1. Unfold RiemannUp
2. Substitute Christoffel symbols
3. Simplify sums (most terms zero)
4. Compute derivatives
5. Algebraic simplification

**Question**: Can we extract a meta-tactic or lemma template to reduce duplication?

**Or**: Is it better to just copy-paste-modify the proof 16 times?

---

## Our Proof Attempt (Incomplete)

Here's what we've tried so far:

```lean
lemma RiemannUp_t_rtr_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.t Idx.r Idx.t Idx.r = 2*M / (r^2 * (r - 2*M)) := by
  classical

  -- Step 1: Unfold definition
  unfold RiemannUp

  -- Step 2: Simplify dCoord (∂_t and ∂_φ are zero)
  simp only [dCoord]

  -- Step 3: Expand sums
  simp only [sumIdx_expand]

  -- Step 4: Substitute Christoffel symbols
  -- STUCK: How to get Γtot to reduce to specific Γ values?
  -- Tried: simp only [Γtot]  -- Doesn't work
  -- Tried: unfold Γtot       -- Creates huge if-then-else tree

  sorry
```

**Where we're stuck**: Getting Γtot to simplify with concrete indices.

---

## Expected Tactical Pattern (Our Guess)

Based on our understanding, the proof might look like:

```lean
lemma RiemannUp_t_rtr_ext ... := by
  classical
  unfold RiemannUp

  -- Simplify dCoord (eliminate ∂_t and ∂_φ)
  simp only [dCoord]

  -- Expand sums
  simp only [sumIdx_expand]

  -- Substitute Γtot values (somehow?)
  <TACTIC TO REDUCE Γtot WITH CONCRETE INDICES>

  -- Most Γ values are 0, eliminate those terms
  <TACTIC TO ELIMINATE ZERO TERMS>

  -- Compute derivative of Γ_t_tr
  rw [<DERIVATIVE LEMMA>]

  -- Algebraic simplification
  field_simp [h_ext.r_pos, h_ext.r_ne_2M]
  ring
```

**Please fill in the missing tactics!**

---

## Success Criteria

### For This Consultation

**Minimum viable**:
- ✅ Complete, working proof of `RiemannUp_t_rtr_ext`
- ✅ Annotations explaining each tactical step
- ✅ Guidance on which parts to reuse vs. customize for other components

**Ideal**:
- ✅ Template for non-zero components
- ✅ Template for zero components (antisymmetry)
- ✅ Template for derivative lemmas
- ✅ Tactical patterns we can reuse across all 16 lemmas

### For Overall Reconstruction

Once we have the pattern:
- Prove all 16 component lemmas (using the pattern)
- Prove 4 cancellation lemmas (pure algebra, should be easy)
- Rewrite 4 diagonal case proofs (trivial, just invoke cancellation lemmas)

**Estimated timeline** (with tactical pattern):
- With pattern: 2-3 days for all 16 component lemmas
- Without pattern: 1-2 weeks (stuck on each proof)

---

## Additional Context

### Why This Is Critical

This is the **ONLY remaining gap** in a complete formal proof that Schwarzschild satisfies Einstein's vacuum equations.

**Current status**:
- ✅ Off-diagonal Ricci cases: All 12 proven
- ❌ Diagonal Ricci cases: Invalid (relied on false lemma)
- ✅ Infrastructure: All Christoffel symbols, metric, derivatives defined

**Once component lemmas are done**: Diagonal cases become trivial, and we have a complete formal proof!

### Constraints

**Must use**:
- Only standard Lean 4 tactics (no external tools)
- Only our existing infrastructure (Christoffel symbols, derivatives, etc.)
- Must be maintainable (we may need to modify later)

**Should avoid**:
- Overly complex proofs that are hard to debug
- Tactics that only work by coincidence (need robust approach)
- Excessive duplication (if we can abstract, we should)

---

## Our Questions Summary

1. **Christoffel substitution**: How to reduce Γtot with concrete indices?
2. **Sum elimination**: How to eliminate zero terms from sumIdx?
3. **Derivative computation**: How to compute derivatives of quotients like M/(r(r-2M))?
4. **Algebraic simplification**: Best tactics for field_simp + ring workflow?
5. **Proof structure**: Inline vs. helper lemmas vs. meta-tactics?
6. **Zero components**: How to use antisymmetry to prove R^a_{bcc} = 0?
7. **Derivative templates**: Pattern for proving derivative lemmas?
8. **Generalization**: Can we extract common tactical patterns?

---

## Files and References

**Main file**: `Papers/P5_GeneralRelativity/GR/Riemann.lean`
- RiemannUp definition: Line 1639-1643
- Target lemma location: ~Line 1950 (after false lemma removal)

**Supporting file**: `Papers/P5_GeneralRelativity/GR/Schwarzschild.lean`
- Christoffel symbol definitions
- Γtot dispatcher
- Exterior structure

**Documentation**:
- `GR/PHASE3_DIAGONAL_RECONSTRUCTION_PLAN.md` (Full reconstruction plan)
- `GR/CONSULT_SENIOR_MATH_PROF_RIEMANN_PROPERTY.md` (Math verification)

**Senior Math Prof's guidance**:
- R^t_{rtr} = 2M/(r²(r-2M)) [verified correct]
- Full derivation provided (see memo)

---

## Request Summary

**Primary request**: Complete proof of `RiemannUp_t_rtr_ext` with tactical annotations

**Secondary requests**:
- Templates for derivative lemmas
- Pattern for zero components via antisymmetry
- Guidance on generalization strategy

**Timeline**: Needed ASAP to unblock Phase 3 reconstruction (3-6 week project)

**Follow-up**: Will likely need additional tactical guidance as we scale to all 16 components

---

Thank you for your tactical expertise!

**Awaiting your guidance**,
Formal Verification Team

---

**P.S.**: If you need any additional context about our infrastructure, Christoffel symbols, or the mathematical derivation, please let us know!
