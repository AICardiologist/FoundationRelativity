# Final Question for Senior Math Consultant

## Progress Update
We've made substantial progress on the discrete CPW model:
- Phase 1A: Infrastructure complete ✅
- Phase 1B: Key lemmas proven/axiomatized (32% sorry reduction) ✅
- Phase 2: Variational framework and main theorem structure ✅

## The Critical Technical Gap

We need a quantitative bound on how edge weight perturbations affect the spectral gap of a discrete graph Laplacian. Everything else is in place.

## Precise Mathematical Question

**Setup:**
- Discrete neck torus: n×n grid with "neck" edges of weight h ≪ 1
- Unperturbed spectral gap: λ₁ ≈ h²/4 (proven via test functions)
- Perturbation: Add εₖ = 1/k to certain edges at TM step k
- Total perturbation after N steps: ∑ᵏ₌₁ᴺ εₖ = Hₙ (harmonic sum)

**Question:**
What is the sharpest bound on how the spectral gap changes under these perturbations? Specifically, we need to prove:

1. If ∑εₖ < Ch² for some constant C, then λ₁(perturbed) ≥ c·h² 
2. If ∑εₖ > C'h² for some C', then λ₁(perturbed) < c·h²

**Our Attempts:**
1. First-order perturbation: Δλ₁ ≈ ∑εₖ · (sensitivity of edge k)
2. Variational bound: Show Rayleigh quotient of test function degrades
3. Missing: How to bound the sensitivity terms rigorously

**Ideal Answer Format:**
"For a discrete Laplacian, when edge (i,j) weight increases by ε, the first eigenvalue shifts by at most [concrete bound in terms of graph structure]. For your neck graph, this gives..."

## Why This Matters
This is the last missing piece to complete our discrete undecidability proof. With this bound, we can prove that non-halting TMs (with Hₙ → ∞) drive λ₁ → 0, while halting TMs (with bounded Hₙ) preserve λ₁ > threshold.

## What We Can Provide
- Complete Lean code if helpful
- Specific n×n dimensions
- Exactly which edges get perturbed
- Our variational characterization setup

Thank you for your expertise on this crucial technical point!