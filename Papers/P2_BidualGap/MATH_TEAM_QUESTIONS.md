# Mathematical Questions for Paper 2 Completion

## Context
We have completed the main WLPO ↔ BidualGapStrong theorem but need to discharge two placeholder axioms to make the proof fully constructive.

## Key Questions

### 1. DualIsBanach Predicate Content
The current `DualIsBanach` structure requires:
```lean
structure DualIsBanach (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop where
  (closed_add : ∀ f g : X →L[ℝ] ℝ, HasOperatorNorm f → HasOperatorNorm g → HasOperatorNorm (f + g))
  (complete_normable_dual : True)   -- Placeholder
```

**Question**: What should `complete_normable_dual` actually assert constructively?
- Should it be about Cauchy sequences of functionals converging?
- Or about existence of limits for bounded increasing sequences?
- How does WLPO provide the constructive content here?

### 2. Isometry Construction Details

For **(c₀ →L[ℝ] ℝ) ≃ₗᵢ ℓ¹**:

**Question A**: The coefficients extraction `f ↦ (f(e₀), f(e₁), ...)`
- We have `signVector` technique from DirectDual.lean showing finite sums bounded by ‖f‖
- How do we prove the infinite sum equals ‖f‖ exactly?
- Need the "≥" direction: construct test vectors approaching the sum

**Question B**: The inverse direction ℓ¹ → (c₀ →L[ℝ] ℝ)
- Given summable sequence a = (a₀, a₁, ...), define f(x) = Σ aᵢxᵢ
- How to show this is well-defined on c₀ (convergence issues)?
- How to verify norm preservation?

### 3. WLPO's Role in Completeness

**Question**: How exactly does WLPO enable completeness of these dual spaces?
- Is it through deciding whether sequences converge?
- Or through locating suprema/infima?
- What fails constructively without WLPO?

### 4. Transport of Properties

**Question**: When we have isometries X ≃ₗᵢ Y:
- How do we formally transport `DualIsBanach X` to `DualIsBanach Y`?
- What properties of `DualIsBanach` need to be preserved?
- Are there subtleties with the constructive content?

### 5. ℓ^∞ Completeness

For **(ℓ¹ →L[ℝ] ℝ) ≃ₗᵢ ℓ^∞**:

**Question**: How do we show ℓ^∞ satisfies `DualIsBanach` constructively?
- ℓ^∞ = bounded sequences with sup norm
- What role does WLPO play in showing completeness?
- How do we handle the supremum operation constructively?

## Technical Implementation Questions

### 6. Mathlib Integration
- Should we use `lp (fun _ : ℕ => ℝ) 1` or define our own ℓ¹?
- How to interface with mathlib's `LinearIsometryEquiv`?
- Any gotchas with universe levels?

### 7. Proof Strategy
Given our existing tools:
- `signVector` construction from DirectDual.lean
- Quotient framework for Boolean operations
- WLPO decidability

**What's the cleanest path to complete the isometries?**

## Priority Order

Based on the roadmap, we should tackle:
1. First complete the isometry proofs (mechanical)
2. Then understand exact `DualIsBanach` requirements
3. Finally show how WLPO provides the constructive content

Please advise on the mathematical details, especially points 1-3 which seem to be the core conceptual challenges.