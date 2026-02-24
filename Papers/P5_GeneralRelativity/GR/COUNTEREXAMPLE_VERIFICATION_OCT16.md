# Verification of Senior Professor's Counterexample - October 16, 2025

## Setup: Flat 2D Space in Polar Coordinates

- Metric: ds² = dr² + r² dθ²
- g_rr = 1, g_θθ = r², g_rθ = g_θr = 0
- Christoffel symbols (non-zero):
  - Γ^r_θθ = -r
  - Γ^θ_rθ = Γ^θ_θr = 1/r

## Test Case: a=r, β=θ, k=θ

### h_fiber Identity States:
```
∂_r(Γ^k_θa · g_kb) - ∂_θ(Γ^k_ra · g_kb) = [R^k_arθ] · g_kb
```

With our indices (k=θ, a=r, β=θ):
```
∂_r(Γ^θ_θr · g_θθ) - ∂_θ(Γ^θ_rr · g_θθ) = [R^θ_rrθ] · g_θθ
```

### LHS Computation

**Product rule on first term:**
∂_r(Γ^θ_θr · g_θθ) = (∂_r Γ^θ_θr) · g_θθ + Γ^θ_θr · (∂_r g_θθ)

Let me compute each piece:
- Γ^θ_θr = 1/r
- ∂_r Γ^θ_θr = ∂_r(1/r) = -1/r²
- g_θθ = r²
- ∂_r g_θθ = ∂_r(r²) = 2r

So: ∂_r(Γ^θ_θr · g_θθ) = (-1/r²)(r²) + (1/r)(2r) = -1 + 2 = 1

**Product rule on second term:**
∂_θ(Γ^θ_rr · g_θθ) = (∂_θ Γ^θ_rr) · g_θθ + Γ^θ_rr · (∂_θ g_θθ)

- Γ^θ_rr = 0
- ∂_θ Γ^θ_rr = 0
- ∂_θ g_θθ = ∂_θ(r²) = 0

So: ∂_θ(Γ^θ_rr · g_θθ) = 0 + 0 = 0

**LHS Total:**
LHS = 1 - 0 = 1

### RHS Computation

RHS = [R^θ_rrθ] · g_θθ

where R^θ_rrθ is the RiemannUp tensor:
```
R^θ_rrθ = ∂_r Γ^θ_θr - ∂_θ Γ^θ_rr + Σλ (Γ^θ_rλ Γ^λ_θr - Γ^θ_θλ Γ^λ_rr)
```

Let me compute:
- ∂_r Γ^θ_θr = -1/r² (computed above)
- ∂_θ Γ^θ_rr = 0 (computed above)

For the ΓΓ sum Σλ (Γ^θ_rλ Γ^λ_θr - Γ^θ_θλ Γ^λ_rr):
- λ=r: Γ^θ_rr Γ^r_θr - Γ^θ_θr Γ^r_rr = (0)(0) - (1/r)(0) = 0
- λ=θ: Γ^θ_rθ Γ^θ_θr - Γ^θ_θθ Γ^θ_rr = (1/r)(1/r) - (0)(0) = 1/r²

Sum = 0 + 1/r² = 1/r²

So: R^θ_rrθ = -1/r² - 0 + 1/r² = 0 ✓ (correct for flat space)

**RHS Total:**
RHS = 0 · r² = 0

### Result: LHS = 1, RHS = 0

**The identity is FALSE in this case.**

## WAIT - Let me re-examine the h_fiber statement

Looking back at Riemann.lean line 6257-6264, the actual h_fiber states:

```lean
∂_r(Γ^k_θa · g_kb) - ∂_θ(Γ^k_ra · g_kb)
=
(∂_r Γ^k_θa - ∂_θ Γ^k_ra + Σλ[Γ^k_rλ Γ^λ_θa - Γ^k_θλ Γ^λ_ra]) · g_kb
```

The RHS is **R^k_{a,r,θ} · g_kb** where the indices on RiemannUp are **(k, a, r, θ)** not (θ, r, r, θ).

Let me recompute with correct index ordering...

With k=θ, a=r, the RHS should be:
R^θ_{r,r,θ} where the RiemannUp definition is R^ρ_{σ,μ,ν}

Actually, looking at line 1257-1261:
```lean
RiemannUp (M r θ : ℝ) (ρ σ μ ν : Idx) : ℝ :=
  dCoord μ (fun r θ => Γtot M r θ ρ ν σ) r θ
- dCoord ν (fun r θ => Γtot M r θ ρ μ σ) r θ
+ sumIdx (fun lam =>
    Γtot M r θ ρ μ lam * Γtot M r θ lam ν σ
  - Γtot M r θ ρ ν lam * Γtot M r θ lam μ σ)
```

So R^ρ_{σ,μ,ν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Σλ (Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ})

With (ρ, σ, μ, ν) = (k, a, r, θ):
R^k_{a,r,θ} = ∂_r Γ^k_{θa} - ∂_θ Γ^k_{ra} + Σλ (Γ^k_{rλ} Γ^λ_{θa} - Γ^k_{θλ} Γ^λ_{ra})

This matches the RHS of h_fiber exactly!

So with (k, a) = (θ, r):
R^θ_{r,r,θ} = ∂_r Γ^θ_{θr} - ∂_θ Γ^θ_{rr} + Σλ (Γ^θ_{rλ} Γ^λ_{θr} - Γ^θ_{θλ} Γ^λ_{rr})

This is exactly what I computed: -1/r² - 0 + 1/r² = 0

So RHS = 0 · g_θθ = 0

But I computed LHS = 1.

**The counterexample is VALID. The identity is mathematically FALSE.**

## Critical Error in Our Understanding

The professor is correct. The h_fiber identity claims that:

∂(Γ·g) = (∂Γ + ΓΓ terms) · g

But when we expand ∂(Γ·g) via product rule, we get:
∂(Γ·g) = (∂Γ)·g + Γ·(∂g)

The Γ·(∂g) terms do NOT equal the ΓΓ commutator terms · g in general!

Even with metric compatibility (∂g expressed via Christoffels), the algebra doesn't work out to give the ΓΓ commutator structure of the Riemann tensor.

---

**CONCLUSION: The senior professor is absolutely correct. The h_fiber identity is mathematically FALSE. We must halt this formalization immediately and identify the correct mathematical statement we should be proving.**
