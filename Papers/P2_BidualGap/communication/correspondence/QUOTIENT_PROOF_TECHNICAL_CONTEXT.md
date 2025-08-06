# Technical Context: mul_K Equivalence Proof

**For**: Junior Professor  
**Purpose**: Technical details for completing Quotient.lean:112

## Exact Location and Context

**File**: `CReal/Quotient.lean`  
**Line**: 112  
**Function**: `mul_respects_equiv`

```lean
-- Goal 2: Z_xy ≈ Z_x'y'
· -- This is the core calculation that shows mul_K respects equivalence
  -- The proof involves showing that the bounds are equal and convergence works
  sorry -- Technical proof of mul_K respecting equivalence
```

## Setup Variables Available

At this point in the proof, you have:

```lean
x x' y y' : CReal                    -- The four constructive reals
hx : x ≈ x'                         -- Given equivalence 
hy : y ≈ y'                         -- Given equivalence
K_U : ℕ                             -- Uniform shift (from uniform_shift)
valid_xy : ValidShift x y K_U       -- ValidShift for (x,y)
valid_x'y' : ValidShift x' y' K_U   -- ValidShift for (x',y') - SAME K_U!
Z_xy := CReal.mul_K x y K_U valid_xy     -- First multiplication
Z_x'y' := CReal.mul_K x' y' K_U valid_x'y'  -- Second multiplication
```

**Key insight**: Both `valid_xy` and `valid_x'y'` use **identical bounds** because `uniform_shift` constructs them with `common_bound`.

## Goal Structure

Need to prove: `Z_xy ≈ Z_x'y'`, which means:
```lean
∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, |Z_xy.seq n - Z_x'y'.seq n| ≤ Modulus.reg k
```

Expanding the definitions:
```lean
|x.seq (n + K_U) * y.seq (n + K_U) - x'.seq (n + K_U) * y'.seq (n + K_U)| ≤ Modulus.reg k
```

## Proof Template

```lean
-- Goal 2: Z_xy ≈ Z_x'y'
· intro k
  -- Get convergence witnesses from the given equivalences
  obtain ⟨Nx, hNx⟩ := hx (k + 1)  -- x ≈ x' at precision k+1
  obtain ⟨Ny, hNy⟩ := hy (k + 1)  -- y ≈ y' at precision k+1
  
  -- Extract the common bounds (they're identical by uniform_shift design)
  rcases valid_xy with ⟨Bx, By, hBx_xy, hBy_xy, _⟩
  rcases valid_x'y' with ⟨Bx', By', hBx_x'y', hBy_x'y', _⟩
  -- Note: By construction of uniform_shift, Bx = Bx' and By = By' definitionally
  
  -- Choose N large enough for convergence
  use max (max Nx Ny) K_U
  intro n hn
  
  -- Unfold the mul_K definitions
  simp only [CReal.mul_K]
  
  -- Apply your signature algebraic manipulation
  have h_split := abs_mul_sub_mul 
    (x.seq (n + K_U)) (y.seq (n + K_U))
    (x'.seq (n + K_U)) (y'.seq (n + K_U))
  
  -- The rest follows your shift_invariance pattern, but using hx/hy convergences
  -- instead of regularity differences...
```

## Key Differences from shift_invariance

**Similarities**:
- Same algebraic manipulation: `|ab - cd| ≤ |a||b-d| + |a-c||d|`
- Same bound extraction and application
- Same `calc` proof structure

**Key Difference**:
- **shift_invariance**: Used `x.is_regular` to bound `|x.seq(n+K₁) - x.seq(n+K₂)|`
- **This proof**: Use given convergence `hx` to bound `|x.seq(n+K_U) - x'.seq(n+K_U)|`

## The Convergence Application

Where shift_invariance had:
```lean
|x.seq (n + K₁) - x.seq (n + K₂)| ≤ Modulus.reg (min (n + K₁) (n + K₂))
```

This proof has:
```lean
|x.seq (n + K_U) - x'.seq (n + K_U)| ≤ Modulus.reg (k + 1)  -- from hNx
```

Since `n ≥ max (max Nx Ny) K_U`, we have `n + K_U ≥ Nx`, so `hNx (n + K_U) ≤ Modulus.reg (k+1)`.

## Final Step Pattern

Similar to your shift_invariance ending:
```lean
calc |x.seq (n + K_U) * y.seq (n + K_U) - x'.seq (n + K_U) * y'.seq (n + K_U)|
    ≤ |x.seq (n + K_U)| * |y.seq (n + K_U) - y'.seq (n + K_U)| +
      |x.seq (n + K_U) - x'.seq (n + K_U)| * |y'.seq (n + K_U)| := h_split
  _ ≤ Bx * Modulus.reg (k + 1) + Modulus.reg (k + 1) * By := ...
  _ = (Bx + By) * Modulus.reg (k + 1) := by ring  
  _ ≤ ... -- Apply some bound management to get to reg k
  _ = Modulus.reg k := ...
```

## Available Lemmas

All the same lemmas from your shift_invariance proof:
- `abs_mul_sub_mul` (line 19 in Multiplication.lean)
- `Modulus.reg_mul_two`: `2 * reg(k+1) = reg k`
- `Modulus.reg_anti_mono`: monotonicity
- Bound applications from ValidShift structures

The main difference is you get to use the **given convergences** `hx` and `hy` directly rather than deriving them from regularity.

This should be very manageable given your shift_invariance success!