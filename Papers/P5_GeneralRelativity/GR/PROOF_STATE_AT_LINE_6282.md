# Proof State at Line 6282 (h_fiber final step)

**DATE:** October 14, 2025
**CONTEXT:** For JP (no compiler access) - this shows what Lean sees after product rule + compat expansion

---

## Goal Statement (Lines 6230-6238)

We're proving:
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

**Interpretation**:
- **LHS**: `∂_r(Γ^k_{θa} · g_kb) - ∂_θ(Γ^k_{ra} · g_kb)`
- **RHS**: `RiemannUp^k_a_{rθ} · g_kb` (the RiemannUp kernel times metric weight)

---

## Proof Steps Executed

### Step 1: intro k (Line 6239)

Context after intro:
```
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
a b k : Idx
⊢ dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ
  =
  (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
   - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
   + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
   - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a))
  * g M k b r θ
```

### Step 2: Product Rule (Lines 6242-6268)

We proved two lemmas:

**prod_r**:
```lean
dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
=
dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
+ Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
```

**prod_θ**:
```lean
dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ
=
dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ
+ Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ
```

### Step 3: Apply Product Rule (Line 6271)

After `rw [prod_r, prod_θ]`, the goal becomes:
```
⊢ (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
   + Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ)
  - (dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ
     + Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ)
  =
  (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
   - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
   + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
   - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a))
  * g M k b r θ
```

**Mathematical form**:
```
LHS = [∂_r Γ^k_{θa} · g_kb + Γ^k_{θa} · ∂_r g_kb]
      - [∂_θ Γ^k_{ra} · g_kb + Γ^k_{ra} · ∂_θ g_kb]

RHS = [∂_r Γ^k_{θa} - ∂_θ Γ^k_{ra} + Σ_λ Γ^k_{rλ}·Γ^λ_{θa} - Σ_λ Γ^k_{θλ}·Γ^λ_{ra}] · g_kb
```

### Step 4: Compat Expansion (Lines 6272-6273)

We apply `dCoord_g_via_compat_ext` which gives:
```lean
dCoord Idx.r (fun r θ => g M k b r θ) r θ
=
sumIdx (fun k_1 => Γtot M r θ k_1 Idx.r k * g M k_1 b r θ)
+ sumIdx (fun k_1 => Γtot M r θ k_1 Idx.r b * g M k k_1 r θ)
```

And similarly for θ:
```lean
dCoord Idx.θ (fun r θ => g M k b r θ) r θ
=
sumIdx (fun k_1 => Γtot M r θ k_1 Idx.θ k * g M k_1 b r θ)
+ sumIdx (fun k_1 => Γtot M r θ k_1 Idx.θ b * g M k k_1 r θ)
```

---

## Proof State at Line 6282 (After Compat Expansion)

After applying the compat expansion rewrites, the goal is:

```
M r θ : ℝ
h_ext : Exterior M r θ
hθ : sin θ ≠ 0
a b k : Idx
prod_r : dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ =
         dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ +
         Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
prod_θ : dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ =
         dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ +
         Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ
⊢ (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ * g M k b r θ
   + Γtot M r θ k Idx.θ a * (sumIdx (fun k_1 => Γtot M r θ k_1 Idx.r k * g M k_1 b r θ)
                             + sumIdx (fun k_1 => Γtot M r θ k_1 Idx.r b * g M k k_1 r θ)))
  - (dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ * g M k b r θ
     + Γtot M r θ k Idx.r a * (sumIdx (fun k_1 => Γtot M r θ k_1 Idx.θ k * g M k_1 b r θ)
                               + sumIdx (fun k_1 => Γtot M r θ k_1 Idx.θ b * g M k k_1 r θ)))
  =
  (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
   - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
   + sumIdx (fun lam => Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a)
   - sumIdx (fun lam => Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a))
  * g M k b r θ
```

---

## Mathematical Form of the Goal

**LHS** (fully expanded with compat sums):
```
[∂_r Γ^k_{θa} · g_kb + Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ)]
- [∂_θ Γ^k_{ra} · g_kb + Γ^k_{ra} · (Σ_λ Γ^λ_{θk}·g_λb + Σ_λ Γ^λ_{θb}·g_kλ)]
```

**RHS** (RiemannUp kernel distributed):
```
[∂_r Γ^k_{θa} - ∂_θ Γ^k_{ra} + Σ_λ Γ^k_{rλ}·Γ^λ_{θa} - Σ_λ Γ^k_{θλ}·Γ^λ_{ra}] · g_kb
```

Expanding the RHS multiplication:
```
∂_r Γ^k_{θa} · g_kb
- ∂_θ Γ^k_{ra} · g_kb
+ (Σ_λ Γ^k_{rλ}·Γ^λ_{θa}) · g_kb
- (Σ_λ Γ^k_{θλ}·Γ^λ_{ra}) · g_kb
```

---

## The Algebraic Gap

Comparing LHS and RHS term-by-term:

### ∂Γ Terms (Match! ✅)

**LHS**: `∂_r Γ^k_{θa} · g_kb - ∂_θ Γ^k_{ra} · g_kb`
**RHS**: `∂_r Γ^k_{θa} · g_kb - ∂_θ Γ^k_{ra} · g_kb`

These are identical - they'll cancel in the equality.

### Sum Terms (Don't Match! ❌)

**LHS has**:
```
Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ)
- Γ^k_{ra} · (Σ_λ Γ^λ_{θk}·g_λb + Σ_λ Γ^λ_{θb}·g_kλ)
```

**RHS has**:
```
(Σ_λ Γ^k_{rλ}·Γ^λ_{θa}) · g_kb - (Σ_λ Γ^k_{θλ}·Γ^λ_{ra}) · g_kb
```

**Key difference**:
- LHS: Compat sums involve `Γ^λ_{rk}·g_λb` (Christoffel × metric)
- RHS: Commutator sums involve `Γ^k_{rλ}·Γ^λ_{θa}` (Christoffel × Christoffel)

These look fundamentally different in structure!

---

## Index Pattern Analysis

Let's trace the indices carefully:

### LHS Compat Terms

**r-direction compat sums** (multiplied by `Γ^k_{θa}`):
```
Σ_λ Γ^λ_{rk}·g_λb    -- First sum: Γ with indices (λ,r,k), metric (λ,b)
Σ_λ Γ^λ_{rb}·g_kλ    -- Second sum: Γ with indices (λ,r,b), metric (k,λ)
```

Multiplied by `Γ^k_{θa}`, we get:
```
Γ^k_{θa} · Σ_λ Γ^λ_{rk}·g_λb
Γ^k_{θa} · Σ_λ Γ^λ_{rb}·g_kλ
```

**θ-direction compat sums** (multiplied by `Γ^k_{ra}`):
```
Γ^k_{ra} · Σ_λ Γ^λ_{θk}·g_λb
Γ^k_{ra} · Σ_λ Γ^λ_{θb}·g_kλ
```

### RHS Commutator Terms

**Commutator sums** (multiplied by `g_kb`):
```
(Σ_λ Γ^k_{rλ}·Γ^λ_{θa}) · g_kb    -- Γ with (k,r,λ) times Γ with (λ,θ,a)
(Σ_λ Γ^k_{θλ}·Γ^λ_{ra}) · g_kb    -- Γ with (k,θ,λ) times Γ with (λ,r,a)
```

### The Mismatch

**LHS pattern**: `Γ^outer · (Σ_λ Γ^λ_inner · g)`
**RHS pattern**: `(Σ_λ Γ^outer · Γ^λ_inner) · g`

The LHS has the sum inside the product with the outer Γ, while the RHS has the sum at the outer level.

But more fundamentally:
- LHS sums contract with metric: `Γ^λ_{rk} · g_λb`
- RHS sums are pure Christoffel products: `Γ^k_{rλ} · Γ^λ_{θa}`

**How do these relate?** 🤔

---

## What Needs to Happen

After canceling the `∂Γ · g` terms (which match on both sides), we need to show:

```
Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ)
- Γ^k_{ra} · (Σ_λ Γ^λ_{θk}·g_λb + Σ_λ Γ^λ_{θb}·g_kλ)
=
(Σ_λ Γ^k_{rλ}·Γ^λ_{θa}) · g_kb - (Σ_λ Γ^k_{θλ}·Γ^λ_{ra}) · g_kb
```

This is **not** a purely algebraic simplification - it requires some mathematical property relating compat sums to commutator sums!

---

## Hypotheses

### Hypothesis 1: Schwarzschild-Specific Cancellation

Maybe in the Schwarzschild exterior region, most Christoffel symbols vanish, and the remaining terms happen to match?

**Problem**: Even with many vanishing components, I don't see how `Γ·Γ·g` becomes `Γ·Γ·g` with different index patterns.

### Hypothesis 2: Missing Identity

There might be a general identity in Riemannian geometry:

```
Γ^μ_{νa} · ∇_μ g_bc = [something involving Riemann tensor]
```

And this identity, combined with metric compatibility, gives the needed relationship.

**Question**: What is this identity?

### Hypothesis 3: Wrong Proof Approach

Maybe product rule + compat expansion is not the right way to prove this. Perhaps there's a more direct route.

**Alternative**: Prove it using RiemannUp properties directly, without expanding via compat?

---

## What I Tried (That Didn't Work)

### Attempt 1: Swapped Refolds

I proved lemmas (lines 6205-6227) that collapse compat sums back:
```
Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ) = Γ^k_{θa} · ∂_r g_kb
```

**Problem**: This is circular! I just undid the compat expansion. Doesn't help match RHS.

### Attempt 2: Direct Algebraic Tactics

Tried `ring`, `ring_nf`, `abel_nf` to normalize and close.

**Problem**: These tactics treat `sumIdx` and `dCoord` as atomic (opaque). They don't know how to relate compat sums to commutator sums.

### Attempt 3: Unfold RiemannUp

Tried to unfold the RiemannUp definition to see if things match syntactically.

**Problem**: After unfolding, the RHS still has commutator sums, which don't match the compat sums on LHS.

---

## Current Code (Line 6282)

```lean
-- Line 6270-6282
rw [prod_r, prod_θ]
rw [dCoord_g_via_compat_ext M r θ h_ext Idx.r k b,
    dCoord_g_via_compat_ext M r θ h_ext Idx.θ k b]

-- Now we have the expanded form. The RHS is RiemannUp · g
-- After product rule + compat expansion, LHS has:
--   [∂_r Γ^k_{θa} · g + Γ^k_{θa} · (Σ_λ Γ^λ_{rk}·g_λb + Σ_λ Γ^λ_{rb}·g_kλ)]
--   - [∂_θ Γ^k_{ra} · g + Γ^k_{ra} · (Σ_λ Γ^λ_{θk}·g_λb + Σ_λ Γ^λ_{θb}·g_kλ)]
-- RHS has (after distributing g):
--   [∂_r Γ^k_{θa} - ∂_θ Γ^k_{ra} + Σ_λ Γ^k_{rλ}·Γ^λ_{θa} - Σ_λ Γ^k_{θλ}·Γ^λ_{ra}] · g
-- Need to show the compat sums cancel and leave only commutator terms
sorry
```

---

## Summary for JP

**Current state**: Goal fully expanded with product rule + compat
**Blocker**: Don't see mathematical path from compat sums to commutator sums
**Build**: Clean, all tactics work correctly
**Need**: Mathematical insight or additional lemma

The ∂Γ terms match perfectly (✅), but the sum terms have different structures (❌).

**Key question**: How do compat sums (Γ·g products) transform into commutator sums (Γ·Γ products)?
