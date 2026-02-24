# Consultation Request - Lean 4 Tactical Challenge in Tensor Calculus Proof

**TO:** Senior Professor (Mathematics)
**FROM:** Research Team
**DATE:** October 14, 2025
**SUBJECT:** Pattern Matching and AC Normalization Issues in Riemann Tensor Formalization

---

## OVERVIEW

We are formalizing General Relativity in Lean 4, specifically proving identities involving the Riemann curvature tensor in Schwarzschild spacetime. We have encountered persistent tactical challenges that we believe may benefit from your mathematical insight and Lean expertise.

**Context:** We are NOT seeking security-related code review. This is pure mathematics formalization - tensor calculus and differential geometry.

---

## MATHEMATICAL BACKGROUND

### The Setup

We work in Schwarzschild spacetime with coordinates `(t, r, θ, φ)` and metric:
```
ds² = -f dt² + f⁻¹ dr² + r² dθ² + r² sin²θ dφ²
```
where `f = 1 - 2M/r`.

### The Objects

1. **Christoffel symbols** `Γᵃᵦ꜀` - Connection coefficients (non-tensorial)
2. **Metric** `gᵃᵦ` - Schwarzschild metric components
3. **Riemann tensor** `Rᵃᵦ꜀ᵈ` - Curvature tensor defined as:

```
R^a_{bcd} = ∂_c Γ^a_{db} - ∂_d Γ^a_{cb}
            + Σₑ (Γ^a_{ce} Γ^e_{db} - Γ^a_{de} Γ^e_{cb})
```

### The Identity We're Proving

We need to show:
```
Σₖ [∂_r(Γᵏ_θₐ gₖᵦ) - ∂_θ(Γᵏ_rₐ gₖᵦ)] = Σₖ [R^k_{a r θ} gₖᵦ]
```

This is a standard tensor identity in differential geometry, relating derivatives of connection-metric products to contractions of the Riemann tensor.

**Mathematical validity:** Unquestionable - this is a routine calculation in GR textbooks.

**Challenge:** Getting Lean to accept the proof due to tactical/syntactic issues.

---

## SUCCESSFUL LEMMA (For Context)

We recently succeeded in proving a helper lemma that makes Riemann tensor recognition simpler:

### Lemma Statement

```lean
@[simp] lemma RiemannUp_kernel_mul_g
    (M r θ : ℝ) (k a b : Idx) :
  RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ
  =
  ( dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
  + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
  - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a) )
  * g M k b r θ
```

Where:
- `RiemannUp M r θ k a c d` = `R^k_{a c d}` (mixed Riemann tensor)
- `dCoord μ f r θ` = `∂_μ f` (coordinate derivative)
- `sumIdx f` = `Σᵢ∈{t,r,θ,φ} f(i)` (finite sum over 4 indices)
- `Γtot M r θ k a b` = `Γᵏ_ₐᵦ` (Christoffel symbol)

### What Made This Work

**Problem:** The RHS has `sumIdx f - sumIdx g` (two separate sums), but `RiemannUp` definition internally has `sumIdx (fun e => f e - g e)` (one sum with subtraction inside).

**Failed approach:**
```lean
simp only [RiemannUp, sumIdx_map_sub, add_comm, add_left_comm, add_assoc]
-- Timeout! AC explosion.
```

**Successful approach:**
```lean
classical
simp only [RiemannUp]               -- 1. Unfold definition
rw [sumIdx_map_sub]                 -- 2. Explicitly apply sum distribution
simp only [sub_eq_add_neg,          -- 3. Normalize addition
           add_comm, add_left_comm, add_assoc]
```

**Key insight:** Separating the pattern-matching rewrite (`rw`) from AC normalization (`simp only`) avoided timeout.

---

## CURRENT CHALLENGE: The h_fiber Proof

### The Goal

Prove pointwise (for each index `k`):

```lean
have h_fiber : ∀ k : Idx,
  dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
- dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ
=
  ( dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
  + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
  - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a) )
  * g M k b r θ
```

**Mathematical content:**
- LHS: `∂_r(Γᵏ_θₐ gₖᵦ) - ∂_θ(Γᵏ_rₐ gₖᵦ)`
- RHS: `R^k_{a r θ} · gₖᵦ` (written in kernel form)

This should follow from:
1. Product rule: `∂(Γ·g) = ∂Γ·g + Γ·∂g`
2. Metric compatibility: `∂_μ g_αβ = -Σ_ρ (Γ^ρ_{μα} g_ρβ + Γ^ρ_{μβ} g_αρ)`
3. Algebraic cancellation

### Our Implementation (Lines 6174-6228)

```lean
{ intro k
  classical

  -- Step 1: Apply product rule
  have prod_r := dCoord_mul_of_diff Idx.r
    (fun r θ => Γtot M r θ k Idx.θ a)
    (fun r θ => g M k b r θ) r θ
    (Or.inl sorry) -- DifferentiableAt_r Γtot (side condition)
    (Or.inl sorry) -- DifferentiableAt_r g (side condition)
    (Or.inr (by decide : Idx.r ≠ Idx.θ))
    (Or.inr (by decide : Idx.r ≠ Idx.θ))

  have prod_θ := dCoord_mul_of_diff Idx.θ
    (fun r θ => Γtot M r θ k Idx.r a)
    (fun r θ => g M k b r θ) r θ
    (Or.inr (by decide : Idx.θ ≠ Idx.r))
    (Or.inr (by decide : Idx.θ ≠ Idx.r))
    (Or.inl sorry) -- DifferentiableAt_θ Γtot (side condition)
    (Or.inl sorry) -- DifferentiableAt_θ g (side condition)

  rw [prod_r, prod_θ]

  -- After product rule, we have:
  -- ∂Γ·g + Γ·∂g (for both r and θ directions)

  -- Step 2: Expand ∂g using metric compatibility
  rw [dCoord_g_via_compat_ext M r θ h_ext Idx.r k b]
  rw [dCoord_g_via_compat_ext M r θ h_ext Idx.θ k b]

  -- After compat expansion, ∂g becomes:
  -- ∂_r g_kb = -Σ_ρ (Γ^ρ_{rk} g_ρb + Γ^ρ_{rb} g_kρ)

  -- Step 3: Distribute multiplication
  simp only [mul_add, add_mul]

  -- Now we have:
  -- ∂Γ·g + Γ·Σ(term1) + Γ·Σ(term2) - [similar for θ]

  -- Step 4: Apply "refold" lemmas to cancel terms
  try rw [← refold_r_right k]
  try rw [← refold_θ_right k]

  -- The refold lemmas say:
  -- Γ * Σ(Γ*g terms) = Γ * ∂g - Γ * Σ(different Γ*g terms)

  -- Step 5: Final simplification
  sorry  -- STUCK HERE
}
```

### Where It's Stuck

**The Problem:** After steps 1-3 compile successfully, the expression looks like:

```
dCoord Idx.r (Γ k θ a) * g k b r θ
+ Γ k θ a * (sumIdx (fun k_1 => Γ k_1 r k * g k_1 b r θ)
            + sumIdx (fun k_1 => Γ k_1 r b * g k k_1 r θ))
- (dCoord Idx.θ (Γ k r a) * g k b r θ
   + Γ k r a * (sumIdx (fun k_1 => Γ k_1 θ k * g k_1 b r θ)
               + sumIdx (fun k_1 => Γ k_1 θ b * g k k_1 r θ)))
= (RHS in kernel form)
```

**The refold lemmas** have the form:
```lean
have refold_r_right (k : Idx) :
  Γ k θ a * sumIdx (fun lam => Γ lam r b * g k lam r θ)
  =
  Γ k θ a * dCoord Idx.r (fun r θ => g k b r θ) r θ
  - Γ k θ a * sumIdx (fun lam => Γ lam r k * g lam b r θ)
```

**The issue:** Pattern matching fails because:
1. The expanded form has `Γ * (sum1 + sum2)` after distribution
2. The refold expects `Γ * sum` on the LHS
3. We need to somehow isolate the right summand to match the refold pattern

**Attempts that failed:**
- Direct `rw [← refold_r_right k]` - pattern not found
- Using `simp` with multiple lemmas - AC explosion/timeout
- Using `ring` - can't work because non-algebraic structure (`sumIdx`, `dCoord`) remains

---

## SPECIFIC QUESTIONS FOR YOU

### Question 1: Tactical Approach

Given the structure above, what would you recommend?

**Option A:** Write expression-specific intermediate lemmas that match the exact syntactic forms after each step?

**Option B:** Use `conv` mode to target specific subexpressions and apply refolds there?

**Option C:** Abandon the refold approach and manually expand everything, then use a massive `calc` proof?

**Option D:** Something else we haven't considered?

### Question 2: AC Normalization Control

We consistently hit timeout when using `simp` with AC lemmas (`add_comm`, `mul_comm`, etc.) on expressions with multiple nested `sumIdx` and products.

**Why:** Lean tries all permutations of associativity/commutativity on a complex expression tree.

**Workarounds we've tried:**
- Separate `simp only` calls (helped for simple cases)
- Increase heartbeat limit (doesn't scale)
- Use `ring` (only works when all non-algebraic structure is gone)

**Question:** Are there Lean 4 techniques for "AC normalization without explosion" that we should know about?

### Question 3: Pattern Matching with Nested Structure

The refold lemmas work beautifully when the expression is in a simple form. But after compat expansion and distribution, we get nested sums:

```
Γ * (sumIdx f + sumIdx g)
```

And the refold expects:
```
Γ * sumIdx f
```

**Question:** How do you typically handle pattern matching when you need to "target a subterm" within a larger expression? Is there a systematic approach beyond trial-and-error with `conv`?

### Question 4: Differentiability Side Conditions

The product rule lemma requires differentiability hypotheses:

```lean
lemma dCoord_mul_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
    dCoord μ (fun r θ => f r θ * g r θ) r θ =
    dCoord μ f r θ * g r θ + f r θ * dCoord μ g r θ
```

We currently use `Or.inl sorry` for the differentiability hypotheses because:
1. The functions (Christoffel symbols, metric) ARE differentiable in the exterior region
2. We have the hypothesis `h_ext : Exterior M r θ` in context
3. But we haven't proven `DifferentiableAt_r Γtot` or `DifferentiableAt_r g` as separate lemmas

**Question:** In your experience, is it acceptable to factor out such "obvious" differentiability facts as `sorry` placeholders while developing the main proof? Or should we prove these first?

---

## WHAT WE'VE TRIED (Summary)

### Approach 1: Fiberwise Proof (Current)

Prove the identity pointwise for each `k`, then lift to sum.

**Status:** Stuck at algebraic simplification after refold application

### Approach 2: Sum-Level Proof (Previously Attempted)

Apply product rule and compat expansion at the sum level (outer `Σₖ`), avoiding Fubini interchange.

**Status:** Hit same AC explosion issue during RiemannUp recognition

### Approach 3: Working LEFT Regroup (Different Metric Slot)

A similar lemma with metric in the LEFT slot (`g a k` instead of `g k b`) DOES work, using:
- Expression-specific helper lemmas (H₁, H₂ for Fubini swaps)
- Manual `calc` proof with explicit substitutions
- Targeted `rw` instead of broad `simp`

**Difference:** That proof was written with custom lemmas matching exact syntactic forms at each step.

---

## COMPARISON: What Works vs. What Doesn't

### ✅ Works: Direct Equality with Simple Structure

```lean
-- Example: Antisymmetry
lemma RiemannUp_swap_mu_nu :
  RiemannUp M r θ ρ σ μ ν = -RiemannUp M r θ ρ σ ν μ := by
  simp [RiemannUp, sub_eq_add_neg, add_comm, add_left_comm]
```

**Why it works:** The structure is simple, `simp` can normalize directly.

### ✅ Works: Explicit Rewrite Then AC Normalize

```lean
-- Example: Our successful RiemannUp_kernel_mul_g
classical
simp only [RiemannUp]        -- Unfold
rw [sumIdx_map_sub]          -- Pattern match
simp only [add_comm, ...]    -- AC normalize
```

**Why it works:** Separating pattern matching from AC normalization.

### ❌ Doesn't Work: All-in-One Simp with AC

```lean
-- Example: What we tried initially
simp only [RiemannUp, sumIdx_map_sub, add_comm, add_left_comm, add_assoc]
-- TIMEOUT after 200k heartbeats
```

**Why it fails:** Lean tries to pattern match and AC normalize simultaneously on a complex nested structure.

### ❌ Doesn't Work: Refold After Compat Expansion

```lean
-- Example: Current issue
rw [dCoord_g_via_compat_ext M r θ h_ext Idx.r k b]  -- Expands ∂g
simp only [mul_add, add_mul]                         -- Distribute
rw [← refold_r_right k]                              -- PATTERN NOT FOUND
```

**Why it fails:** The expanded form doesn't match the refold's expected LHS pattern.

---

## CODE ARTIFACTS FOR YOUR REVIEW

We will provide you with:

1. **The full Riemann.lean file** - So you can see the complete context
2. **Specific line numbers:**
   - Lines 1261-1278: Successful `RiemannUp_kernel_mul_g` lemma
   - Lines 6117-6162: Refold helper lemmas (these work!)
   - Lines 6165-6228: The stuck `h_fiber` proof
   - Lines 791-810: Product rule lemma definition
   - Lines 1800-1828: Compat refold lemmas

3. **Documentation:**
   - `FINAL_IMPLEMENTATION_REPORT_OCT14.md` - Full technical report
   - `STATUS_IMPLEMENTATION_OCT13_FINAL.md` - Previous investigation

---

## WHAT WE'RE NOT ASKING

- ❌ Review of the mathematical correctness (that's solid)
- ❌ Different proof strategies (the approach is right)
- ❌ Simplification of the statement (it's the identity we need)

## WHAT WE ARE ASKING

- ✅ Tactical wisdom for Lean 4 pattern matching with nested structures
- ✅ Techniques for controlling AC normalization
- ✅ Best practices for "targeting subterms" in complex expressions
- ✅ Experience-based guidance on `conv` mode, `simp` configuration, or other Lean 4 features we may be missing

---

## OUR HYPOTHESIS

We believe the issue is **purely tactical/syntactic**, not mathematical or logical. The proof structure is sound; we just need the right Lean incantation to:

1. Apply the refold lemmas to the correct subterms
2. Manage the AC normalization without explosion
3. Close the goal with algebraic simplification

We suspect that someone with deep Lean 4 experience may recognize this pattern and say, "Oh, you need to use [technique X]" or "Have you tried [configuration Y]?"

---

## CLOSING THOUGHTS

This is a formalization of standard differential geometry. The mathematics is textbook material. But Lean is forcing us to be extremely precise about the syntactic forms, and we've hit a tactical wall.

Your insight would be invaluable. Even if the answer is "you need expression-specific lemmas for your exact forms," that would be helpful confirmation.

Thank you for considering this consultation.

---

**Attachments:**
1. `Riemann.lean` (full file)
2. `FINAL_IMPLEMENTATION_REPORT_OCT14.md`

**Contact:** [Will be provided by user]

---

## APPENDIX: Key Definitions

For your reference, here are the crucial definitions:

```lean
-- Finite index type
inductive Idx | t | r | θ | φ

-- Finite sum over indices
def sumIdx (f : Idx → ℝ) : ℝ :=
  Finset.sum {Idx.t, Idx.r, Idx.θ, Idx.φ} f

-- Sum distribution lemmas
lemma sumIdx_map_sub (A B : Idx → ℝ) :
  sumIdx (fun k => A k - B k) = sumIdx A - sumIdx B

lemma sumIdx_neg (f : Idx → ℝ) :
  sumIdx (fun i => - f i) = - sumIdx f

-- Riemann tensor (mixed form)
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (fun r θ => Γtot M r θ a d b) r θ
  - dCoord d (fun r θ => Γtot M r θ a c b) r θ
  + sumIdx (fun e => Γtot M r θ a c e * Γtot M r θ e d b)
  - sumIdx (fun e => Γtot M r θ a d e * Γtot M r θ e c b)

-- Metric compatibility (in exterior region)
lemma dCoord_g_via_compat_ext :
  dCoord μ (fun r θ => g M k b r θ) r θ =
  -sumIdx (fun lam => Γtot M r θ lam μ k * g M lam b r θ)
  -sumIdx (fun lam => Γtot M r θ lam μ b * g M k lam r θ)
```

**Note:** All definitions are standard; notation matches physics conventions.
