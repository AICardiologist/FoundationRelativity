/-
  Papers/P2_BidualGap/Constructive/CReal/Multiplication.lean
  
  
  ⚠️ ORPHANED FILE - NOT USED BY ANY OTHER MODULE
  ⚠️ DOES NOT COMPILE - olean not built
  ⚠️ OBSOLETE - Part of abandoned CReal approach
  
  This file is not imported by any active proof and can be ignored.
  Original purpose follows:
  Multiplication infrastructure for constructive reals.
  Contains: ValidShift, get_shift, mul_K, shift_invariance, common_bound, CReal.mul
-/

import Papers.P2_BidualGap.Constructive.CReal.Basic

set_option maxHeartbeats 600000

namespace Papers.P2_BidualGap.Constructive

open Classical

namespace CReal

/-- Helper lemma for multiplication bounds -/
lemma abs_mul_sub_mul (a b c d : ℚ) : 
    |a * b - c * d| ≤ |a| * |b - d| + |a - c| * |d| := by
  have : a * b - c * d = a * (b - d) + (a - c) * d := by ring
  rw [this]
  apply le_trans (abs_add _ _)
  apply add_le_add
  · rw [abs_mul]
  · rw [abs_mul]

/-- Common bound lemma: equivalent sequences can be bounded by the same constant -/
lemma common_bound {x x' : CReal} (_ : x ≈ x') :
    ∃ B : ℚ, (∀ n, |x.seq n| ≤ B) ∧ (∀ n, |x'.seq n| ≤ B) := by
  -- Extract individual bounds
  obtain ⟨Bx, hBx⟩ := bounded x
  obtain ⟨Bx', hBx'⟩ := bounded x'
  
  -- Use max as common bound
  use max Bx Bx'
  constructor
  · intro n
    exact le_trans (hBx n) (le_max_left Bx Bx')
  · intro n
    exact le_trans (hBx' n) (le_max_right Bx Bx')

/-- A valid shift for multiplication depends on bounds of x and y -/
structure ValidShift (x y : CReal) (K : ℕ) where
  Bx : ℚ
  By : ℚ
  hBx : ∀ n, |x.seq n| ≤ Bx
  hBy : ∀ n, |y.seq n| ≤ By
  hBound : Bx + By ≤ (2^K : ℚ)

/-- Extract shift data for multiplication -/
noncomputable def get_shift (x y : CReal) : Σ K : ℕ, ValidShift x y K :=
  -- Extract bounds
  let Bx := Classical.choose (bounded x)
  let hBx := Classical.choose_spec (bounded x)
  let By := Classical.choose (bounded y)
  let hBy := Classical.choose_spec (bounded y)
  
  -- Find K such that Bx + By ≤ 2^K
  let K := Classical.choose (Modulus.exists_pow_le (Bx + By))
  let hK := Classical.choose_spec (Modulus.exists_pow_le (Bx + By))
  
  -- Construct ValidShift
  ⟨K, Bx, By, hBx, hBy, hK⟩

/-- Multiplication with explicit shift K -/
def mul_K (x y : CReal) (K : ℕ) (hK : ValidShift x y K) : CReal :=
  { seq := fun n => x.seq (n + K) * y.seq (n + K)
    is_regular := by
      intro n m
      -- Use helper lemma for multiplication bound
      have h_split : |x.seq (n + K) * y.seq (n + K) - x.seq (m + K) * y.seq (m + K)| ≤ 
                     |x.seq (n + K)| * |y.seq (n + K) - y.seq (m + K)| + 
                     |x.seq (n + K) - x.seq (m + K)| * |y.seq (m + K)| :=
        abs_mul_sub_mul _ _ _ _
      
      -- Extract bounds from ValidShift
      obtain ⟨Bx, By, hBx, hBy, hBound⟩ := hK
      
      -- Bound each term
      have h1 : |x.seq (n + K)| * |y.seq (n + K) - y.seq (m + K)| ≤ 
                Bx * Modulus.reg (min (n + K) (m + K)) := by
        calc |x.seq (n + K)| * |y.seq (n + K) - y.seq (m + K)|
            ≤ Bx * |y.seq (n + K) - y.seq (m + K)| := by
              apply mul_le_mul_of_nonneg_right (hBx _) (abs_nonneg _)
          _ ≤ Bx * Modulus.reg (min (n + K) (m + K)) := by
              apply mul_le_mul_of_nonneg_left (y.is_regular _ _) 
              have : 0 ≤ Bx := le_trans (abs_nonneg _) (hBx 0)
              exact this
      
      have h2 : |x.seq (n + K) - x.seq (m + K)| * |y.seq (m + K)| ≤ 
                Modulus.reg (min (n + K) (m + K)) * By := by
        calc |x.seq (n + K) - x.seq (m + K)| * |y.seq (m + K)|
            ≤ |x.seq (n + K) - x.seq (m + K)| * By := by
              apply mul_le_mul_of_nonneg_left (hBy _) (abs_nonneg _)
          _ ≤ Modulus.reg (min (n + K) (m + K)) * By := by
              apply mul_le_mul_of_nonneg_right (x.is_regular _ _)
              have : 0 ≤ By := le_trans (abs_nonneg _) (hBy 0)
              exact this
      
      -- Combine bounds
      have h3 : Bx * Modulus.reg (min (n + K) (m + K)) + Modulus.reg (min (n + K) (m + K)) * By
                = (Bx + By) * Modulus.reg (min (n + K) (m + K)) := by
        ring
      
      -- Use the precision shift
      have h4 : (Bx + By) * Modulus.reg (min (n + K) (m + K)) ≤ 
                (2^K : ℚ) * Modulus.reg (min (n + K) (m + K)) := by
        apply mul_le_mul_of_nonneg_right hBound (Modulus.reg_nonneg _)
      
      -- Apply the generalized reg_pow_mul lemma
      have h5 : min (n + K) (m + K) = min n m + K := by
        simp only [min_def]; split_ifs <;> omega
      have h6 : (2^K : ℚ) * Modulus.reg (min n m + K) = Modulus.reg (min n m) := by
        exact Modulus.reg_pow_mul _ _
      
      -- Final calculation
      calc |x.seq (n + K) * y.seq (n + K) - x.seq (m + K) * y.seq (m + K)|
          ≤ |x.seq (n + K)| * |y.seq (n + K) - y.seq (m + K)| + 
            |x.seq (n + K) - x.seq (m + K)| * |y.seq (m + K)| := h_split
        _ ≤ Bx * Modulus.reg (min (n + K) (m + K)) + 
            Modulus.reg (min (n + K) (m + K)) * By := add_le_add h1 h2
        _ = (Bx + By) * Modulus.reg (min (n + K) (m + K)) := h3
        _ ≤ (2^K : ℚ) * Modulus.reg (min (n + K) (m + K)) := h4
        _ = (2^K : ℚ) * Modulus.reg (min n m + K) := by rw [h5]
        _ = Modulus.reg (min n m) := h6 }

/-- `mul_K` is independent of the chosen precision shift. -/
lemma shift_invariance (x y : CReal) (K₁ K₂ : ℕ)
    (hK₁ : ValidShift x y K₁) (hK₂ : ValidShift x y K₂) :
    mul_K x y K₁ hK₁ ≈ mul_K x y K₂ hK₂ := by
  -- We have to establish the setoid equivalence.
  intro k

  -- Unpack both `ValidShift` structures.
  rcases hK₁ with ⟨Bx₁, By₁, hBx₁, hBy₁, _⟩
  rcases hK₂ with ⟨Bx₂, By₂, hBx₂, hBy₂, _⟩

  -- Use the *same* (larger) bounds for both shifts.
  let Bx : ℚ := max Bx₁ Bx₂
  let By : ℚ := max By₁ By₂

  -- Derived bounds for every index `n`.
  have hBx : ∀ n, |x.seq n| ≤ Bx := by
    intro n
    have h₁ : |x.seq n| ≤ Bx₁ := hBx₁ n
    have : (Bx₁ : ℚ) ≤ Bx := le_max_left _ _
    exact le_trans h₁ this
  have hBy : ∀ n, |y.seq n| ≤ By := by
    intro n
    have h₁ : |y.seq n| ≤ By₁ := hBy₁ n
    have : (By₁ : ℚ) ≤ By := le_max_left _ _
    exact le_trans h₁ this

  -- Non–negativity of the unified bounds.
  have hBx_nonneg : (0 : ℚ) ≤ Bx := by
    have : |x.seq 0| ≤ Bx := hBx 0
    exact le_trans (abs_nonneg _) this
  have hBy_nonneg : (0 : ℚ) ≤ By := by
    have : |y.seq 0| ≤ By := hBy 0
    exact le_trans (abs_nonneg _) this

  -- A strictly positive constant that dominates `(Bx + By)`.
  have C_pos : (0 : ℚ) < Bx + By + 1 := by
    have h₀ : (0 : ℚ) < (1 : ℚ) := by norm_num
    have : (0 : ℚ) ≤ Bx + By := add_nonneg hBx_nonneg hBy_nonneg
    exact add_pos_of_nonneg_of_pos this h₀

  -- Use the generic "large‐`n`" modulus lemma with that constant.
  obtain ⟨N₀, hN₀⟩ :=
    Modulus.reg_bound_large (Bx + By + 1) C_pos k

  -- A final index that is large enough for *both* shifts.
  let N : ℕ := max N₀ (max K₁ K₂)
  use N
  intro n hn

  -- Show that `n` is large enough for the `reg_bound_large` witness.
  have hn₀ : n ≥ N₀ := le_trans (le_max_left _ _) hn

  -- Expand the two sequences appearing in the goal.
  simp only [mul_K] at *

  -- Main algebraic split:  |ab − cd| ≤ |a||b−d| + |a−c||d|
  have h_split :=
    abs_mul_sub_mul
      (x.seq (n + K₁)) (y.seq (n + K₁))
      (x.seq (n + K₂)) (y.seq (n + K₂))

  -- Bound the first product term: |a|·|b−d|.
  have h₁ : |x.seq (n + K₁)| *
            |y.seq (n + K₁) - y.seq (n + K₂)|
          ≤ Bx * Modulus.reg (min (n + K₁) (n + K₂)) := by
    calc
      |x.seq (n + K₁)| *
        |y.seq (n + K₁) - y.seq (n + K₂)|
          ≤ Bx *
            |y.seq (n + K₁) - y.seq (n + K₂)| := by
              apply mul_le_mul_of_nonneg_right (hBx _) (abs_nonneg _)
      _ ≤ Bx * Modulus.reg (min (n + K₁) (n + K₂)) := by
          apply mul_le_mul_of_nonneg_left (y.is_regular _ _) hBx_nonneg

  -- Bound the second product term: |a−c|·|d|.
  have h₂ : |x.seq (n + K₁) - x.seq (n + K₂)| *
            |y.seq (n + K₂)|
          ≤ Modulus.reg (min (n + K₁) (n + K₂)) * By := by
    calc
      |x.seq (n + K₁) - x.seq (n + K₂)| *
        |y.seq (n + K₂)|
          ≤ |x.seq (n + K₁) - x.seq (n + K₂)| * By := by
              apply mul_le_mul_of_nonneg_left (hBy _) (abs_nonneg _)
      _ ≤ Modulus.reg (min (n + K₁) (n + K₂)) * By := by
          apply mul_le_mul_of_nonneg_right (x.is_regular _ _) hBy_nonneg

  -- Combine the two pieces and extract a common factor.
  have h₃ :
      |x.seq (n + K₁) * y.seq (n + K₁) -
        x.seq (n + K₂) * y.seq (n + K₂)|
      ≤ (Bx + By) * Modulus.reg (min (n + K₁) (n + K₂)) := by
    calc
      _ ≤ |x.seq (n + K₁)| *
            |y.seq (n + K₁) - y.seq (n + K₂)| +
          |x.seq (n + K₁) - x.seq (n + K₂)| *
            |y.seq (n + K₂)| := h_split
      _ ≤ Bx * Modulus.reg _ + Modulus.reg _ * By :=
        add_le_add h₁ h₂
      _ = (Bx + By) * Modulus.reg (min (n + K₁) (n + K₂)) := by ring

  -- `min (n+K₁) (n+K₂)` is **at least** `n`, hence
  -- `reg(min …) ≤ reg n` by antitonicity.
  have h_min_le : n ≤ min (n + K₁) (n + K₂) := by
    exact le_min (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have h_reg_mono :
      Modulus.reg (min (n + K₁) (n + K₂)) ≤ Modulus.reg n :=
    Modulus.reg_anti_mono h_min_le

  -- Substitute the weaker modulus into the bound.
  have h₄ :
      |x.seq (n + K₁) * y.seq (n + K₁) -
        x.seq (n + K₂) * y.seq (n + K₂)|
      ≤ (Bx + By) * Modulus.reg n :=
    le_trans h₃ (by
      have : (Bx + By) * Modulus.reg (min (n + K₁) (n + K₂))
            ≤ (Bx + By) * Modulus.reg n := by
        apply mul_le_mul_of_nonneg_left h_reg_mono
        exact add_nonneg hBx_nonneg hBy_nonneg
      simpa using this)

  ------------------------------------------------------------------
  -- Last step: shrink the coefficient to hit `reg k`.
  ------------------------------------------------------------------
  -- `(Bx + By) * reg n ≤ (Bx + By + 1) * reg n`
  have h₅ :
      (Bx + By) * Modulus.reg n
      ≤ (Bx + By + 1) * Modulus.reg n := by
    have : (Bx + By) ≤ Bx + By + 1 := by linarith
    exact mul_le_mul_of_nonneg_right this (Modulus.reg_nonneg _)

  -- Use the witness `N₀` from `reg_bound_large`.
  have h₆ :
      (Bx + By + 1) * Modulus.reg n ≤ Modulus.reg k :=
    hN₀ n hn₀

  -- Put everything together.
  have :
      |x.seq (n + K₁) * y.seq (n + K₁) -
        x.seq (n + K₂) * y.seq (n + K₂)|
      ≤ Modulus.reg k :=
    le_trans (le_trans h₄ h₅) h₆

  -- This is precisely the goal the setoid wants.
  exact this

/-- Uniform shift for pairs of equivalent sequences -/
noncomputable def uniform_shift {x x' y y' : CReal} (hx : x ≈ x') (hy : y ≈ y') :
    Σ K_U : ℕ, (ValidShift x y K_U) × (ValidShift x' y' K_U) :=
  -- Extract COMMON bounds using the common_bound lemma
  let B_X := Classical.choose (common_bound hx)
  let hB_X := Classical.choose_spec (common_bound hx)
  -- hB_X.1 bounds x, hB_X.2 bounds x'
  
  let B_Y := Classical.choose (common_bound hy)
  let hB_Y := Classical.choose_spec (common_bound hy)
  
  -- Find K_U based on these specific common bounds
  let K_U := Classical.choose (Modulus.exists_pow_le (B_X + B_Y))
  let hK_U := Classical.choose_spec (Modulus.exists_pow_le (B_X + B_Y))
  
  -- Construct ValidShift records using THE SAME bounds
  let valid_xy : ValidShift x y K_U := {
    Bx := B_X, By := B_Y,
    hBx := hB_X.1, hBy := hB_Y.1,
    hBound := hK_U
  }
  
  let valid_x'y' : ValidShift x' y' K_U := {
    Bx := B_X, By := B_Y,  -- CRITICAL: Definitionally the same bounds
    hBx := hB_X.2, hBy := hB_Y.2,
    hBound := hK_U
  }
  
  ⟨K_U, valid_xy, valid_x'y'⟩

/--  The two `ValidShift`s returned by `uniform_shift`
     share their bounds **definitionally**. -/
lemma uniform_shift_bounds_eq
    {x x' y y' : CReal} {hx : x ≈ x'} {hy : y ≈ y'} :
  let data := CReal.uniform_shift hx hy
  (((data.2).1).Bx = ((data.2).2).Bx) ∧
  (((data.2).1).By = ((data.2).2).By) := by
  -- unfold and reduce everything: both sides become the same `B_X` / `B_Y`
  dsimp [CReal.uniform_shift]    -- expands the `let`s
  simp                           -- `rfl` after dsimp

/-- Multiplication of constructive reals with definitional transparency -/
noncomputable def mul (x y : CReal) : CReal :=
  let data := get_shift x y
  mul_K x y data.1 data.2

end CReal

end Papers.P2_BidualGap.Constructive