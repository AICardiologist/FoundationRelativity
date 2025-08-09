/-
  Papers/P2_BidualGap/Constructive/CReal/Quotient.lean
  
  Quotient structure and well-definedness proofs for constructive reals.
  Contains: RC definition, lifted operations, well-definedness proofs
-/

import Papers.P2_BidualGap.Constructive.CReal.Multiplication

set_option maxHeartbeats 600000

namespace Papers.P2_BidualGap.Constructive

open Classical

/-- The type of constructive real numbers as a quotient -/
def RC : Type := Quotient CReal.instSetoid

namespace RC

/-- Zero element -/
instance : Zero RC := ⟨Quotient.mk CReal.instSetoid CReal.zero⟩

/-- One element -/
instance : One RC := ⟨Quotient.mk CReal.instSetoid CReal.one⟩

/-- Addition respects the equivalence relation -/
lemma add_respects_equiv : ∀ (x x' y y' : CReal), x ≈ x' → y ≈ y' → CReal.add x y ≈ CReal.add x' y' := by
  intro x x' y y' hx hy k
  -- Get witnesses for x ≈ x' and y ≈ y' at precision k+1
  obtain ⟨Nx, hNx⟩ := hx (k + 1)
  obtain ⟨Ny, hNy⟩ := hy (k + 1)
  
  -- Take N = max(Nx, Ny) to handle both
  use max Nx Ny
  intro n hn
  
  -- Extract the bounds we need
  have hnx : n ≥ Nx := le_trans (le_max_left _ _) hn
  have hny : n ≥ Ny := le_trans (le_max_right _ _) hn
  
  -- The sequences are defined with shift n+1
  simp only [CReal.add]
  
  -- Split the difference
  have h1 : |x.seq (n + 1) + y.seq (n + 1) - (x'.seq (n + 1) + y'.seq (n + 1))| =
            |(x.seq (n + 1) - x'.seq (n + 1)) + (y.seq (n + 1) - y'.seq (n + 1))| := by
    congr 1; ring
  
  -- Apply triangle inequality
  have h2 : |(x.seq (n + 1) - x'.seq (n + 1)) + (y.seq (n + 1) - y'.seq (n + 1))| ≤
            |x.seq (n + 1) - x'.seq (n + 1)| + |y.seq (n + 1) - y'.seq (n + 1)| :=
    abs_add _ _
  
  -- Apply the convergence bounds (noting n+1 ≥ Nx+1 when n ≥ Nx)
  have h3 : |x.seq (n + 1) - x'.seq (n + 1)| ≤ Modulus.reg (k + 1) := by
    apply hNx (n + 1)
    omega
  
  have h4 : |y.seq (n + 1) - y'.seq (n + 1)| ≤ Modulus.reg (k + 1) := by
    apply hNy (n + 1)
    omega
  
  -- Combine everything
  calc |x.seq (n + 1) + y.seq (n + 1) - (x'.seq (n + 1) + y'.seq (n + 1))|
      = |(x.seq (n + 1) - x'.seq (n + 1)) + (y.seq (n + 1) - y'.seq (n + 1))| := h1
    _ ≤ |x.seq (n + 1) - x'.seq (n + 1)| + |y.seq (n + 1) - y'.seq (n + 1)| := h2
    _ ≤ Modulus.reg (k + 1) + Modulus.reg (k + 1) := add_le_add h3 h4
    _ = 2 * Modulus.reg (k + 1) := by ring
    _ = Modulus.reg k := Modulus.reg_mul_two k

/-- Negation respects the equivalence relation -/
lemma neg_respects_equiv : ∀ (x x' : CReal), x ≈ x' → CReal.neg x ≈ CReal.neg x' := by
  intro x x' hx k
  obtain ⟨N, hN⟩ := hx k
  use N
  intro n hn
  simp only [CReal.neg]
  -- Goal: |-x.seq n - -x'.seq n| ≤ Modulus.reg k
  -- This is the same as |x'.seq n - x.seq n|
  have : -x.seq n - -x'.seq n = x'.seq n - x.seq n := by ring
  rw [this, abs_sub_comm]
  exact hN n hn


/-- Multiplication respects the equivalence relation - restructured proof -/
lemma mul_respects_equiv : ∀ (x x' y y' : CReal), x ≈ x' → y ≈ y' → CReal.mul x y ≈ CReal.mul x' y' := by
  intro x x' y y' hx hy
  
  -- Step 1: Get uniform shift K_U using Junior Professor's approach
  -- Store the entire term to preserve definitional equality
  have shift_data := CReal.uniform_shift hx hy
  let K_U := shift_data.1
  let valid_xy := (shift_data.2).1
  let valid_x'y' := (shift_data.2).2
  
  -- Define intermediate terms using mul_K with K_U
  let Z_xy := CReal.mul_K x y K_U valid_xy
  let Z_x'y' := CReal.mul_K x' y' K_U valid_x'y'
  
  -- Apply transitivity: mul x y ≈ Z_xy ≈ Z_x'y' ≈ mul x' y'
  have h1 : CReal.mul x y ≈ Z_xy := by
    -- This follows from shift_invariance and definitional transparency
    unfold CReal.mul
    let data_xy := CReal.get_shift x y
    apply CReal.shift_invariance x y data_xy.1 K_U data_xy.2 valid_xy
  
  have h2 : Z_xy ≈ Z_x'y' := by
    intro k

    /- We work at the slightly finer precision
         kp = k + K_U + 1.
         The extra "+ K_U" lets us absorb the factor (Bx + By) ≤ 2^K_U,
         and the final "+ 1" lets us halve reg afterwards (2·reg(k+1)=reg k). -/
    let kp : ℕ := k + K_U + 1

    -- Convergence witnesses for the given equivalences at precision kp
    obtain ⟨Nx, hNx⟩ := hx kp
    obtain ⟨Ny, hNy⟩ := hy kp

    ------------------------------------------------------------------
    -- Equal bounds coming from `uniform_shift`
    ------------------------------------------------------------------

    /-!
      `valid_xy`  and `valid_x'y'` come from
        let ⟨K_U, valid_xy, valid_x'y'⟩ := CReal.uniform_shift hx hy
      and have type  `ValidShift … K_U`.

      The helper lemma

          hBounds_eq : valid_xy.Bx = valid_x'y'.Bx ∧ …

      was obtained just before this point:
    -/
    have hBounds_eq :=
      (CReal.uniform_shift_bounds_eq (x:=x) (x':=x')
                                     (y:=y) (y':=y')
                                     (hx:=hx) (hy:=hy))

    /-! --------------------------------------------------------------------
         **Key step**:  pattern‑match *with an equation binder*.
         We keep   hxy  and  hxy'  as "bridge" equalities.
    -------------------------------------------------------------------------/  
    cases hxy  : valid_xy   with
    | mk Bx By hBx hBy hBound =>
      cases hxy' : valid_x'y' with
      | mk Bx' By' hBx' hBy' hBound' =>

        /-! `hxy  : valid_xy   = _`
            `hxy' : valid_x'y' = _`
            `hBounds_eq.1 : valid_xy.Bx = valid_x'y'.Bx`
            Goal: `Bx' = Bx` and `By' = By`. -/

        have hBx_eq_final : Bx' = Bx := by
          -- 1.  Use the helper lemma (orient it correctly).
          -- 2.  Rewrite both sides with `hxy` and `hxy'`.
          have h := (hBounds_eq.1).symm
          simpa [hxy, hxy'] using h

        have hBy_eq_final : By' = By := by
          have h := (hBounds_eq.2).symm
          simpa [hxy, hxy'] using h

        -- Non‑negativity of the bounds  
        have hBx_nonneg : (0 : ℚ) ≤ Bx := by
          have : |x.seq 0| ≤ Bx := hBx 0
          exact le_trans (abs_nonneg _) this
        have hBy_nonneg : (0 : ℚ) ≤ By := by
          have : |y.seq 0| ≤ By := hBy 0
          exact le_trans (abs_nonneg _) this

    /- Choose an index `N` that is large enough for *both*
        convergence witnesses. -/
    use max Nx Ny
    intro n hn
    have hnNx : Nx ≤ n := le_trans (le_max_left _ _) hn
    have hnNy : Ny ≤ n := le_trans (le_max_right _ _) hn

    -- Abbreviation for the shifted index
    let idx : ℕ := n + K_U
    have hidxNx : Nx ≤ idx := Nat.le_trans hnNx (Nat.le_add_right _ _)
    have hidxNy : Ny ≤ idx := Nat.le_trans hnNy (Nat.le_add_right _ _)

    -- Unfold the two sequences involved
    simp only [Z_xy, Z_x'y', CReal.mul_K] at *

    -- Algebraic split:  |ab − cd| ≤ |a||b−d| + |a−c||d|
    have h_split :=
      CReal.abs_mul_sub_mul
        (x.seq  idx)  (y.seq  idx)
        (x'.seq idx)  (y'.seq idx)

        --------------------------------------------------------------------
        -- Bound the first product term  |a|·|b−d|
        --------------------------------------------------------------------
        have h1 : |x.seq idx| * |y.seq idx - y'.seq idx|
                ≤ Bx * Modulus.reg kp := by
          have hdiff : |y.seq idx - y'.seq idx| ≤ Modulus.reg kp := by
            simpa using hNy idx hidxNy
          have hboundx : |x.seq idx| ≤ Bx := hBx idx
          calc
            |x.seq idx| * |y.seq idx - y'.seq idx|
                ≤ Bx * |y.seq idx - y'.seq idx| := by
                  apply mul_le_mul_of_nonneg_right hboundx (abs_nonneg _)
            _ ≤ Bx * Modulus.reg kp := by
                  apply mul_le_mul_of_nonneg_left hdiff hBx_nonneg

        --------------------------------------------------------------------
        -- Bound the second product term  |a−c|·|d|
        --------------------------------------------------------------------
        have h2 : |x.seq idx - x'.seq idx| * |y'.seq idx|
                ≤ Modulus.reg kp * By := by
          have hdiff : |x.seq idx - x'.seq idx| ≤ Modulus.reg kp := by
            simpa using hNx idx hidxNx
          have hboundy : |y'.seq idx| ≤ By := by
            -- Use the established equality By' = By
            rw [← hBy_eq_final]
            exact hBy' idx
          calc
            |x.seq idx - x'.seq idx| * |y'.seq idx|
                ≤ Modulus.reg kp * |y'.seq idx| := by
                  apply mul_le_mul_of_nonneg_right hdiff (abs_nonneg _)
            _ ≤ Modulus.reg kp * By := by
                  apply mul_le_mul_of_nonneg_left hboundy (Modulus.reg_nonneg _)

        --------------------------------------------------------------------
        -- Combine the two pieces
        --------------------------------------------------------------------
        have h_sum :
            |x.seq idx * y.seq idx - x'.seq idx * y'.seq idx|
            ≤ (Bx + By) * Modulus.reg kp := by
          calc
            |x.seq idx * y.seq idx - x'.seq idx * y'.seq idx|
                ≤ |x.seq idx| * |y.seq idx - y'.seq idx| +
                  |x.seq idx - x'.seq idx| * |y'.seq idx|      := h_split
            _ ≤ Bx * Modulus.reg kp + Modulus.reg kp * By      :=
                  add_le_add h1 h2
            _ = (Bx + By) * Modulus.reg kp                     := by ring

        --------------------------------------------------------------------
        -- Use  Bx + By ≤ 2^K_U  (from ValidShift bounds)
        --------------------------------------------------------------------
        have h_coeff :
            (Bx + By) * Modulus.reg kp
            ≤ (2 ^ K_U : ℚ) * Modulus.reg kp := by
          apply mul_le_mul_of_nonneg_right hBound (Modulus.reg_nonneg _)

        -- Collapse the power‑of‑two factor via `reg_pow_mul`
        have h_regpow :
            (2 ^ K_U : ℚ) * Modulus.reg kp = Modulus.reg (k + 1) := by
          -- `kp = k + K_U + 1` by definition
          -- reg_pow_mul says: 2^K * reg(N + K) = reg(N) 
          -- We have: 2^K_U * reg(k + K_U + 1) and want reg(k + 1)
          -- We need to show: (k + 1) + K_U = k + K_U + 1
          have : (k + 1) + K_U = k + K_U + 1 := by ring
          unfold kp
          rw [← this]
          exact Modulus.reg_pow_mul (k + 1) K_U

        have h_final₁ :
            |x.seq idx * y.seq idx - x'.seq idx * y'.seq idx|
            ≤ Modulus.reg (k + 1) := by
          have h_tmp := le_trans h_sum h_coeff
          simpa [h_regpow] using h_tmp

        --------------------------------------------------------------------
        -- Halve: 2·reg(k+1) = reg k  ⇒  reg(k+1) ≤ reg k
        --------------------------------------------------------------------
        have h_regmono : Modulus.reg (k + 1) ≤ Modulus.reg k :=
          Modulus.reg_anti_mono (Nat.le_succ k)

        have :
            |x.seq idx * y.seq idx - x'.seq idx * y'.seq idx|
            ≤ Modulus.reg k :=
          le_trans h_final₁ h_regmono

        exact this
  
  have h3 : Z_x'y' ≈ CReal.mul x' y' := by
    -- Apply shift_invariance symmetrically
    apply Setoid.symm
    unfold CReal.mul
    let data_x'y' := CReal.get_shift x' y'
    apply CReal.shift_invariance x' y' data_x'y'.1 K_U data_x'y'.2 valid_x'y'
  
  -- Combine with transitivity
  exact Setoid.trans h1 (Setoid.trans h2 h3)


/-- Lifted addition -/
def add : RC → RC → RC :=
  Quotient.lift₂ (fun x y => Quotient.mk CReal.instSetoid (CReal.add x y)) 
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound (add_respects_equiv a₁ a₂ b₁ b₂ h₁ h₂))

/-- Lifted negation -/
def neg : RC → RC :=
  Quotient.lift (fun x => Quotient.mk CReal.instSetoid (CReal.neg x)) 
    (fun a b h => Quotient.sound (neg_respects_equiv a b h))

/-- Lifted multiplication -/
noncomputable def mul : RC → RC → RC :=
  Quotient.lift₂ (fun x y => Quotient.mk CReal.instSetoid (CReal.mul x y)) 
    (fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound (mul_respects_equiv a₁ a₂ b₁ b₂ h₁ h₂))

instance : Add RC := ⟨add⟩
instance : Neg RC := ⟨neg⟩
noncomputable instance : Mul RC := ⟨mul⟩

/-- Embed a rational as a constructive real -/
def from_rat (q : ℚ) : RC := Quotient.mk CReal.instSetoid (CReal.from_rat q)

end RC

end Papers.P2_BidualGap.Constructive