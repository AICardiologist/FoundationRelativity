# Reference: Similar Bound Calculations in Our Codebase

**For**: Junior Professor  
**Purpose**: Examples of bound calculation patterns used in our implementation

## Pattern 1: Multiplication Regularity (mul_K.is_regular)

**Location**: `CReal/Multiplication.lean:66-126`

This shows the standard pattern for bounding products using ValidShift:

```lean
have h1 : |x.seq (n + K)| * |y.seq (n + K) - y.seq (m + K)| ≤ 
          Bx * Modulus.reg (min (n + K) (m + K)) := by
  calc |x.seq (n + K)| * |y.seq (n + K) - y.seq (m + K)|
      ≤ Bx * |y.seq (n + K) - y.seq (m + K)| := by
        apply mul_le_mul_of_nonneg_right (hBx _) (abs_nonneg _)
    _ ≤ Bx * Modulus.reg (min (n + K) (m + K)) := by
        apply mul_le_mul_of_nonneg_left (y.is_regular _ _) 
        have : 0 ≤ Bx := le_trans (abs_nonneg _) (hBx 0)
        exact this
```

**Key techniques**:
- Extract bounds from ValidShift: `hBx : ∀ n, |x.seq n| ≤ Bx`
- Apply regularity: `y.is_regular _ _`
- Use `mul_le_mul_of_nonneg_right` for products
- Establish non-negativity of bounds

## Pattern 2: Combining Multiple Bounds

**Location**: `CReal/Multiplication.lean:117-126`

Shows how to combine bounds and apply precision management:

```lean
calc |x.seq (n + K) * y.seq (n + K) - x.seq (m + K) * y.seq (m + K)|
    ≤ |x.seq (n + K)| * |y.seq (n + K) - y.seq (m + K)| + 
      |x.seq (n + K) - x.seq (m + K)| * |y.seq (m + K)| := h_split
  _ ≤ Bx * Modulus.reg (min (n + K) (m + K)) + 
      Modulus.reg (min (n + K) (m + K)) * By := add_le_add h1 h2
  _ = (Bx + By) * Modulus.reg (min (n + K) (m + K)) := h3
  _ ≤ (2^K : ℚ) * Modulus.reg (min (n + K) (m + K)) := h4
  _ = (2^K : ℚ) * Modulus.reg (min n m + K) := by rw [h5]
  _ = Modulus.reg (min n m) := h6
```

**Key techniques**:
- Use `add_le_add` to combine inequalities
- Factor out common terms: `(Bx + By) * reg(...)`
- Apply ValidShift bound: `Bx + By ≤ 2^K`
- Use modulus arithmetic: `2^K * reg(N + K) = reg(N)`

## Pattern 3: Case Analysis and Symmetry

**Location**: Our partial shift_invariance attempt

Template for handling the `K₁ ≤ K₂` vs `K₂ < K₁` cases:

```lean
by_cases h : K₁ ≤ K₂

case pos =>
  -- Case: K₁ ≤ K₂, prove the bound directly
  calc |x.seq (n + K₁) * y.seq (n + K₁) - x.seq (n + K₂) * y.seq (n + K₂)|
      = |...algebraic manipulation...| := by ring
    _ ≤ |bound using K₁, K₂ bounds| := by ...
    _ ≤ Modulus.reg k := by ...

case neg =>
  -- Case: K₂ < K₁, use symmetry
  have : K₂ ≤ K₁ := le_of_not_le h
  rw [abs_sub_comm]  -- Flip the absolute value
  -- Apply same argument with roles swapped
```

## Pattern 4: Precision Management 

**Key insight**: When we have `n ≥ max k (max K₁ K₂)`, we can control the final precision:

```lean
have hn_large : n ≥ max k (max K₁ K₂) := hn
-- This gives us: n ≥ k, n ≥ K₁, n ≥ K₂
-- So we can bound things in terms of reg(k) at the end
```

## Pattern 5: Min Arithmetic

**Common manipulation**:
```lean
have h5 : min (n + K) (m + K) = min n m + K := by
  simp only [min_def]; split_ifs <;> omega
```

This lets us apply `reg_pow_mul`: `2^K * reg(min n m + K) = reg(min n m)`

## For shift_invariance Specifically

**Expected structure**:
```lean
lemma shift_invariance ... := by
  intro k
  use max k (max K₁ K₂)  -- Choose N large enough
  intro n hn
  simp only [mul_K]      -- Unfold definitions
  
  by_cases h : K₁ ≤ K₂
  case pos =>
    -- Extract bounds from hK₁, hK₂
    obtain ⟨Bx₁, By₁, hBx₁, hBy₁, hBound₁⟩ := hK₁
    obtain ⟨Bx₂, By₂, hBx₂, hBy₂, hBound₂⟩ := hK₂
    
    -- Apply the algebraic manipulation
    calc |x.seq (n + K₁) * y.seq (n + K₁) - x.seq (n + K₂) * y.seq (n + K₂)|
        = |... split using a*b - c*d = a*(b-d) + (a-c)*d ...| := by ring
      _ ≤ |... apply bounds and regularity ...| := by ...
      _ ≤ Modulus.reg k := by ...
  
  case neg =>
    -- Symmetric case with K₂ ≤ K₁
    ...
```

The key is managing the bounds from both ValidShift structures and showing the final result fits within `reg k`.