# Contributing to Paper 5: General Relativity AxCal

## How to Add a New Metric

This guide explains the two-pass simplification pattern used for tensor computations in our GR formalization.

### The Two-Pass Pattern

Our approach ensures CI-stable, deterministic proofs by carefully controlling when symbolic derivatives are evaluated.

#### Pass 1: Structural Expansions
- Expand index sums
- Apply trace definitions
- Unfold metric components
- **DO NOT** evaluate derivatives of Christoffel symbols

#### Pass 2: Safe Derivatives Only
- Apply derivative rules for simple functions
- **PROTECT** problematic derivatives using `set` or local `attribute [-simp]`
- Evaluate after algebraic simplification

### Example: Ricci Tensor Reduction

```lean
section RicciReductions
  -- Protect dangerous symbols from premature evaluation
  attribute [-simp] Γ_r_θθ Γ_r_φφ Γ_φ_θφ Γ_θ_φφ in
  
  @[simp] lemma Ricci_θθ_reduce (M r θ : ℝ) :
    Ricci M r θ Idx.θ Idx.θ = 
      deriv (fun s => Γ_r_θθ M s) r
      - deriv (fun t => Γ_φ_θφ t) θ  
      + trace_term * Γ_r_θθ M r
      - contraction_terms := by
    -- Pass 1: Structural expansions
    simp only [Ricci, sumIdx_expand, trace_equality]
    
    -- Freeze problematic derivatives
    set Δr := deriv (fun s => Γ_r_θθ M s) r with hΔr
    set Δθ := deriv (fun t => Γ_φ_θφ t) θ with hΔθ
    
    -- Pass 2: Safe derivatives only  
    simp (config := { failIfUnchanged := false }) only
      [deriv_const, deriv_linear, /* safe rules */]
    
    -- Final algebraic simplification
    rw [← hΔr, ← hΔθ]
    ring
```

### Key Principles

1. **Symbolic First, Evaluate Late**
   - Keep radial derivatives symbolic as long as possible
   - Only evaluate when algebraically necessary

2. **Trace Freezing**
   - Use `set T := trace_expression` to prevent coefficient drift
   - Unfreeze only for final substitution

3. **Protected Derivatives**
   - Identify "dangerous" derivatives that cause premature evaluation
   - Use local `attribute [-simp]` or explicit `set` bindings

4. **Deterministic Simplification**
   - Use `failIfUnchanged := false` to avoid spurious failures
   - Order simp rules explicitly when needed

### Testing Your Metric

1. **Verify Christoffel Symbols**
   ```lean
   example (M r : ℝ) : Γ_t_tr M r = M / (r^2 * f M r) := by simp
   ```

2. **Check Ricci Vanishing**
   ```lean
   theorem Ricci_vanishing (M r θ : ℝ) (hr : 2*M < r) :
     Ricci M r θ μ ν = 0 := by
     cases μ <;> cases ν <;> simp [Ricci_reduce]
   ```

3. **Add Guardrail Tests**
   ```lean
   -- This should NOT simplify to a constant
   example (M r : ℝ) : 
     deriv (fun s => Γ_r_θθ M s) r = deriv (fun s => Γ_r_θθ M s) r := by
     simp only [] -- Should be trivial reflexivity
   ```

### Common Pitfalls

1. **Premature Derivative Evaluation**
   - Problem: `∂_r Γ^r_{θθ}` evaluating to `-1` breaks algebraic balance
   - Solution: Keep it symbolic with `attribute [-simp] Γ_r_θθ`

2. **Cotangent Derivatives**
   - Problem: `deriv (cot θ)` introduces `sin θ ≠ 0` side conditions
   - Solution: Freeze as `Δθ` and handle algebraically

3. **Missing Factors in Contractions**
   - Problem: Forgetting factor of 2 in symmetric contractions
   - Solution: Review index symmetries carefully

### CI Considerations

- Keep proof times under 5 seconds per lemma
- Avoid global simp attributes on metric-specific symbols
- Add section markers for local attribute changes
- Document why each symbol needs protection

### Getting Help

- Check existing metrics in `GR/Schwarzschild.lean` for patterns
- Run `lake build --verbose` to debug timeout issues
- Use `simp?` to understand which rules are firing
- Ask in PR comments if you hit unexpected behavior

---

*Last Updated: September 2025 (Sprint 3 patterns documented)*