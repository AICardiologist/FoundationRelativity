# What We're Waiting For From The Consultant

## Status
- First question sent: About smooth case IFT approach
- Consultant response: Not yet received
- Second question prepared: About discrete perturbation bounds
- Waiting to send: Until first response received

## The Specific Technical Gap

### What We Have
```lean
-- Original system: neck edges have weight h
-- Spectral gap: λ₁ ≈ h²/4

-- Perturbation: Add ε_k = 1/k to edge e_k at step k  
-- Total: Σε_k = H_n (harmonic sum)
```

### What We Need
A theorem of the form:
```
If we perturb edge weights by {ε_i}, then:
|λ₁(perturbed) - λ₁(original)| ≤ f(ε₁, ε₂, ..., graph structure)
```

### Why It Matters
- If Σε_k < threshold → λ₁ stays above h²/8 → large gap preserved
- If Σε_k > threshold → λ₁ falls below h²/8 → gap destroyed

## Our Best Guesses

### Guess 1: First-Order Bound
```
Δλ₁ ≈ Σ(ε_k × sensitivity_k)
where sensitivity_k = ∂λ₁/∂(weight of edge k)
```
For neck edges: sensitivity ≈ O(1)

### Guess 2: Variational Bound  
```
λ₁(perturbed) ≥ λ₁(original) - max_k(ε_k) × (some constant)
```

### Guess 3: Weyl-Type Bound
```
|λ₁(perturbed) - λ₁(original)| ≤ ||perturbation matrix||
```

## What Would Unblock Us

Any of these would work:
1. "For neck graph, perturbation ε on neck edge shifts λ₁ by at most Cε"
2. "Sum of perturbations Σε_k bounds eigenvalue shift by O(Σε_k)"
3. "Here's a paper/textbook with the bound you need"

## Current Workaround

We've axiomatized:
```lean
axiom perturbation_bound : 
  Σε_k < h²/16 → λ₁ ≥ h²/8
  Σε_k > h²/4 → λ₁ < h²/8
```

This lets us complete the logical structure while waiting for the precise bound.

## Timeline
- Question ready: ✅
- Waiting for: First response before asking second question
- Expected impact: Would complete the proof immediately