# Questions for Senior Math Consultant - Phase 2

## Context
We've completed Phase 1B of the discrete CPW model with 32% sorry reduction. We're now in Phase 2, trying to connect the Turing machine encoding to actual spectral gap behavior.

## Current Setup
- **Graph**: Discrete neck torus (n×n grid with neck coupling h)
- **Laplacian**: L = D - A (degree matrix - adjacency matrix)
- **Perturbation**: Edge weights modified by TM computation history
- **Goal**: Prove spectral gap jumps from O(h²) to o(h²) based on halting

## Primary Question (Most Important)

**How can we rigorously prove that accumulating perturbations (1/k for k=1 to N) on edge weights causes the spectral gap to transition from h²/4 to below h²/8?**

Specifically:
1. We encode TM step k by adding 1/k to certain edge weights
2. If TM halts at step n, total perturbation ≤ H_n ≈ log(n)
3. If TM doesn't halt by N, total perturbation ≥ H_N → ∞

Our current approach:
- Use variational characterization: λ₁ = min{R(v) : v ⊥ constants}
- Show perturbations affect the Rayleigh quotient of the optimal test function
- Need: Quantitative bound on how H_N perturbation affects λ₁

Is there a clean way to prove this without computing eigenvalues explicitly?

## Secondary Questions

### Q2: Discrete vs Continuous Approximation
For the discrete model, can we use the continuous neck scaling (h²/4 ≤ λ₁ ≤ 5h²) directly, or do we need discrete-specific bounds? The discrete Laplacian on an n×n grid has different normalization than the continuous one.

### Q3: Primitive Recursive Characterization
To show the spectral gap condition is Π₁, we need the map (rational matrix) ↦ (spectral gap > threshold) to be primitive recursive. Since eigenvalues are algebraic numbers (roots of characteristic polynomial), is there a standard way to show this decision problem is primitive recursive?

## What We've Tried
1. **Variational approach**: Define λ₁ via Rayleigh quotient minimization
2. **Test functions**: Neck function (±1 on each side) gives upper bound
3. **Axiomatization**: Currently axiomatized the key bounds to make progress

## What Would Help Most
A concrete strategy for proving how harmonic series perturbations quantitatively affect the spectral gap, preferably without full eigenvalue computation. Even a sketch of the key estimates would be invaluable.

## Additional Context Available
- Full LaTeX paper with smooth case analysis
- Lean 4 formalization (19 remaining sorries)
- Your previous IFT strategy document for smooth case

Thank you for your invaluable guidance on this project!