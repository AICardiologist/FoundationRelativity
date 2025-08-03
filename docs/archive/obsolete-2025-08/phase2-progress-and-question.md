# Phase 2 Progress and Consultant Question

## What We've Done in Phase 2

### 1. Created Variational Framework (`SpectralTheory.lean`)
- Defined Rayleigh quotient for discrete Laplacian
- Set up variational characterization: λ₁ = min{R(v) : v ⊥ constants}
- Introduced test functions (neck function gives upper bound)

### 2. Started Perturbation Analysis (`PerturbationTheory.lean`)
- Modeled how TM steps accumulate perturbations (harmonic series)
- Sketched key lemmas:
  - Small perturbations (< h²/16) preserve gap
  - Large perturbations (> h²/4) destroy gap
- Connected non-halting to harmonic growth

### 3. Identified Key Technical Gap
We need to prove: **How does adding ε to edge weights quantitatively affect λ₁?**

## Refined Question for Senior Consultant

### Context Summary
- Discrete neck torus graph with Laplacian L = D - A
- TM computation adds 1/k to certain edge weights at step k
- Need to prove: Non-halting (H_N → ∞) makes λ₁ < h²/8

### The Core Question

**For a discrete graph Laplacian, what is the cleanest way to bound the eigenvalue shift when edge weights are perturbed?**

Specifically:
1. Original: Neck edges have weight h, giving λ₁ ≈ h²/4
2. Perturbed: Add ε₁, ε₂, ... to various edges (∑εᵢ = H_N)
3. Goal: Show λ₁(perturbed) < h²/8 when H_N > some threshold

We're considering:
- **Option A**: First-order perturbation theory (∂λ₁/∂εᵢ sensitivity analysis)
- **Option B**: Direct Rayleigh quotient bounds on perturbed operator
- **Option C**: Spectral graph theory techniques we're missing?

### What Would Help Most
1. A concrete inequality relating edge perturbations to eigenvalue shift
2. Whether our "sensitivity ≈ 1 for neck edges" intuition is correct
3. Any simplification for the discrete case vs continuous

### We Can Provide
- Full code/definitions if helpful
- Specific matrix sizes (n×n grid)
- Details on which edges get perturbed

Thank you for your continued guidance!

## While We Wait

We'll continue with:
1. Implementing basic perturbation bounds
2. Connecting to the main spectral_gap_jump theorem
3. Documenting the remaining proof obligations

This way we'll be ready to incorporate your insights when they arrive.