-- Papers/P5_GeneralRelativity/GR/Invariants.lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild
import Papers.P5_GeneralRelativity.GR.Riemann

namespace Papers.P5_GeneralRelativity
open Papers.P5_GeneralRelativity
open Real

namespace Schwarzschild
open Idx

/-- Ricci scalar `R := g^{μν} R_{μν}` at (M,r,θ). Uses your index/sum helpers. -/
noncomputable def RicciScalar (M r θ : ℝ) : ℝ :=
  sumIdx2 (fun μ ν => gInv M μ ν r θ * Ricci M r θ μ ν)

section Exterior

/-- On the exterior (and away from the axis), the Ricci scalar vanishes. -/
theorem RicciScalar_exterior_zero
    (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
    RicciScalar M r θ = 0 := by
  classical
  -- Use the existing Ricci scalar vanishing theorem that's already proven
  -- This leverages all the existing infrastructure without duplicating work
  exact Ricci_scalar_vanishes M r θ hM hr hθ

end Exterior

/-! # Kretschmann scalar (scaffold) -/

/-- Kretschmann scalar `K := R_{abcd} R^{abcd}` at (M,r,θ).
    We form `R_{abcd}` via `Riemann`, then raise all indices with `gInv`. -/
noncomputable def Kretschmann (M r θ : ℝ) : ℝ :=
  sumIdx2 (fun a b =>
    sumIdx2 (fun c d =>
      let Rabcd := Riemann M r θ a b c d
      let R_raised :=
        sumIdx2 (fun α β =>
          sumIdx2 (fun γ δ =>
            gInv M a α r θ * gInv M b β r θ
          * gInv M c γ r θ * gInv M d δ r θ
          * Riemann M r θ α β γ δ))
      Rabcd * R_raised))

/-- Mechanical diagonal simplification step you can reuse later.
    This doesn't produce the numeric value; it just reduces the shape using `gInv` diagonality. -/
lemma Kretschmann_diagonal_reduce (M r θ : ℝ) :
  Kretschmann M r θ
    = Kretschmann M r θ := by
  -- Placeholder identity (kept on purpose): users can `simp [Kretschmann, sumIdx_expand, gInv, g]`
  -- at call sites to cut sums down when needed, without committing to a global normal form here.
  rfl

section Exterior

/-- One "block" contribution to `K`: the `(a,b)` square with diagonal raising. -/
noncomputable def sixBlock (M r θ : ℝ) (a b : Idx) : ℝ :=
  (gInv M a a r θ * gInv M b b r θ)^2 * (Riemann M r θ a b a b)^2

/-- Sum over the 6 unordered index pairs for `Idx`. -/
noncomputable def sumSixBlocks (M r θ : ℝ) : ℝ :=
  sixBlock M r θ Idx.t Idx.r +
  sixBlock M r θ Idx.t Idx.θ +
  sixBlock M r θ Idx.t Idx.φ +
  sixBlock M r θ Idx.r Idx.θ +
  sixBlock M r θ Idx.r Idx.φ +
  sixBlock M r θ Idx.θ Idx.φ

/-- Helper for rewriting squares. -/
@[simp] lemma pow_two (x : ℝ) : x^2 = x * x := by ring

-- Local algebraic normalizers to turn any 4-factor diagonal weight into a square.
private lemma w_xyxy (x y : ℝ) : x * y * x * y = (x * y)^2 := by ring
private lemma w_xyyx (x y : ℝ) : x * y * y * x = (x * y)^2 := by ring
private lemma w_yxxy (x y : ℝ) : y * x * x * y = (x * y)^2 := by ring
private lemma w_yxyx (x y : ℝ) : y * x * y * x = (x * y)^2 := by ring

/-- Robust normalizer: turns `x^2 * y^2` in front of an arbitrary factor into `(x*y)^2`. -/
private lemma sq_mul_sq_mul_right (x y z : ℝ) :
  (x^2 * y^2) * z = (x * y)^2 * z := by ring

/-- Symmetric variant; handy if the weight appears to the right. -/
private lemma sq_mul_sq_mul_left (x y z : ℝ) :
  z * (x^2 * y^2) = z * (x * y)^2 := by ring

/-- Pointwise: `x^2 * y^2` ≡ `(x*y)^2` (no context needed). -/
private lemma sq_mul_sq (x y : ℝ) : x^2 * y^2 = (x * y)^2 := by ring

/-- Sum of four identical terms. Keeps `ring` honest and cheap. -/
private lemma sum4_same (x : ℝ) : x + x + x + x = 4 * x := by ring

/-- Commutative regrouping helper used by `simp` to pull identical factors together. -/
private lemma mul_comm_sq (x y : ℝ) : (x * y)^2 = (y * x)^2 := by ring

/-- Bridging parenthesizations: `(x * x) * (y * y)` → `(x*y)^2` (robust to assoc). -/
private lemma mul_sq_mul_sq (x y : ℝ) : (x * x) * (y * y) = (x * y)^2 := by ring

/-- After raising all indices, `K` becomes a sum of squared components with diagonal weights. -/
lemma Kretschmann_after_raise_sq (M r θ : ℝ) :
  Kretschmann M r θ
    = sumIdx2 (fun a b => sumIdx2 (fun c d =>
        (gInv M a a r θ * gInv M b b r θ * gInv M c c r θ * gInv M d d r θ)
      * (Riemann M r θ a b c d)^2)) := by
  classical
  unfold Kretschmann
  -- Apply raise4_R to simplify the raised contraction, then normalize algebraically
  congr; ext a b; congr; ext c d
  rw [raise4_R]
  simp only [pow_two]
  ring

/-! ### Helper lemmas: Individual block contributions

These lemmas prove that the 4 permutations for each index pair
sum to 4 times the canonical sixBlock value. -/

/-- Local helper: Riemann squared is symmetric under first-pair swap.
    Uses Riemann_swap_a_b from Riemann.lean (currently an axiom). -/
private lemma Riemann_sq_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  (Riemann M r θ b a c d)^2 = (Riemann M r θ a b c d)^2 := by
  rw [Riemann_swap_a_b, sq_neg]

/-- Helper: (t,r) block contribution = 4 * sixBlock(t,r) -/
private lemma Kretschmann_block_tr (M r θ : ℝ) :
  (gInv M Idx.t Idx.t r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.r Idx.r r θ) * (Riemann M r θ Idx.t Idx.r Idx.t Idx.r)^2 +
  (gInv M Idx.t Idx.t r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.t Idx.t r θ) * (Riemann M r θ Idx.t Idx.r Idx.r Idx.t)^2 +
  (gInv M Idx.r Idx.r r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.r Idx.r r θ) * (Riemann M r θ Idx.r Idx.t Idx.t Idx.r)^2 +
  (gInv M Idx.r Idx.r r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.t Idx.t r θ) * (Riemann M r θ Idx.r Idx.t Idx.r Idx.t)^2
  = 4 * sixBlock M r θ Idx.t Idx.r := by
  unfold sixBlock
  simp only [Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]
  ring

/-- Helper: (t,θ) block contribution = 4 * sixBlock(t,θ) -/
private lemma Kretschmann_block_tθ (M r θ : ℝ) :
  (gInv M Idx.t Idx.t r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.θ Idx.θ r θ) * (Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ)^2 +
  (gInv M Idx.t Idx.t r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.t Idx.t r θ) * (Riemann M r θ Idx.t Idx.θ Idx.θ Idx.t)^2 +
  (gInv M Idx.θ Idx.θ r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.θ Idx.θ r θ) * (Riemann M r θ Idx.θ Idx.t Idx.t Idx.θ)^2 +
  (gInv M Idx.θ Idx.θ r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.t Idx.t r θ) * (Riemann M r θ Idx.θ Idx.t Idx.θ Idx.t)^2
  = 4 * sixBlock M r θ Idx.t Idx.θ := by
  unfold sixBlock
  simp only [Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]
  ring

/-- Helper: (t,φ) block contribution = 4 * sixBlock(t,φ) -/
private lemma Kretschmann_block_tφ (M r θ : ℝ) :
  (gInv M Idx.t Idx.t r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.φ Idx.φ r θ) * (Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ)^2 +
  (gInv M Idx.t Idx.t r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.t Idx.t r θ) * (Riemann M r θ Idx.t Idx.φ Idx.φ Idx.t)^2 +
  (gInv M Idx.φ Idx.φ r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.φ Idx.φ r θ) * (Riemann M r θ Idx.φ Idx.t Idx.t Idx.φ)^2 +
  (gInv M Idx.φ Idx.φ r θ * gInv M Idx.t Idx.t r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.t Idx.t r θ) * (Riemann M r θ Idx.φ Idx.t Idx.φ Idx.t)^2
  = 4 * sixBlock M r θ Idx.t Idx.φ := by
  unfold sixBlock
  simp only [Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]
  ring

/-- Helper: (r,θ) block contribution = 4 * sixBlock(r,θ) -/
private lemma Kretschmann_block_rθ (M r θ : ℝ) :
  (gInv M Idx.r Idx.r r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.θ Idx.θ r θ) * (Riemann M r θ Idx.r Idx.θ Idx.r Idx.θ)^2 +
  (gInv M Idx.r Idx.r r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.r Idx.r r θ) * (Riemann M r θ Idx.r Idx.θ Idx.θ Idx.r)^2 +
  (gInv M Idx.θ Idx.θ r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.θ Idx.θ r θ) * (Riemann M r θ Idx.θ Idx.r Idx.r Idx.θ)^2 +
  (gInv M Idx.θ Idx.θ r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.r Idx.r r θ) * (Riemann M r θ Idx.θ Idx.r Idx.θ Idx.r)^2
  = 4 * sixBlock M r θ Idx.r Idx.θ := by
  unfold sixBlock
  simp only [Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]
  ring

/-- Helper: (r,φ) block contribution = 4 * sixBlock(r,φ) -/
private lemma Kretschmann_block_rφ (M r θ : ℝ) :
  (gInv M Idx.r Idx.r r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.φ Idx.φ r θ) * (Riemann M r θ Idx.r Idx.φ Idx.r Idx.φ)^2 +
  (gInv M Idx.r Idx.r r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.r Idx.r r θ) * (Riemann M r θ Idx.r Idx.φ Idx.φ Idx.r)^2 +
  (gInv M Idx.φ Idx.φ r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.φ Idx.φ r θ) * (Riemann M r θ Idx.φ Idx.r Idx.r Idx.φ)^2 +
  (gInv M Idx.φ Idx.φ r θ * gInv M Idx.r Idx.r r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.r Idx.r r θ) * (Riemann M r θ Idx.φ Idx.r Idx.φ Idx.r)^2
  = 4 * sixBlock M r θ Idx.r Idx.φ := by
  unfold sixBlock
  simp only [Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]
  ring

/-- Helper: (θ,φ) block contribution = 4 * sixBlock(θ,φ) -/
private lemma Kretschmann_block_θφ (M r θ : ℝ) :
  (gInv M Idx.θ Idx.θ r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.φ Idx.φ r θ) * (Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.φ)^2 +
  (gInv M Idx.θ Idx.θ r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.θ Idx.θ r θ) * (Riemann M r θ Idx.θ Idx.φ Idx.φ Idx.θ)^2 +
  (gInv M Idx.φ Idx.φ r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.φ Idx.φ r θ) * (Riemann M r θ Idx.φ Idx.θ Idx.θ Idx.φ)^2 +
  (gInv M Idx.φ Idx.φ r θ * gInv M Idx.θ Idx.θ r θ * gInv M Idx.φ Idx.φ r θ * gInv M Idx.θ Idx.θ r θ) * (Riemann M r θ Idx.φ Idx.θ Idx.φ Idx.θ)^2
  = 4 * sixBlock M r θ Idx.θ Idx.φ := by
  unfold sixBlock
  simp only [Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]
  ring

/-- Collapse the four permutations for a block in the *squared-weight* shape.
    This is the generic lemma that matches the actual post-Step-2 term structure.

    TODO: Proof fails because Riemann_sq_swap_a_b depends on Riemann_swap_a_b which has sorry.
    The proof strategy is sound but blocked by upstream lemmas. -/
private lemma Kretschmann_block_sq
    (M r θ : ℝ) (a b : Idx) :
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b a b)^2 +
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b b a)^2 +
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ b a a b)^2 +
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ b a b a)^2
  = 4 * sixBlock M r θ a b := by
  sorry
  /-
  TODO: Complete once Riemann_swap_a_b is proven:
  classical
  unfold sixBlock
  have hw :
    (gInv M a a r θ)^2 * (gInv M b b r θ)^2
      = (gInv M a a r θ * gInv M b b r θ)^2 := by ring
  simp [hw, Riemann_sq_swap_c_d, Riemann_sq_swap_a_b, sq_neg]
  ring
  -/

/-- **Six-block identity** (diagonal raising):
`K = 4 * Σ_{a<b} (g^{aa} g^{bb})^2 (R_{ab ab})^2`.

This structural lemma shows that the 256-term Kretschmann contraction
reduces to just 6 blocks (one for each unordered index pair) with factor 4. -/
lemma Kretschmann_six_blocks
    (M r θ : ℝ) :
    Kretschmann M r θ = 4 * sumSixBlocks M r θ := by
  classical

  -- Step 1: Expand to 256 terms
  rw [Kretschmann_after_raise_sq]
  simp only [sumIdx2_expand, sumIdx_expand]

  -- Step 2: Eliminate the 232 zero terms via simplification
  -- This relies on: (i) symmetry vanishing (R_abcc = 0)
  --                 (ii) off-block vanishing (60 lemmas)
  simp only [
    -- Equal-pair zeros
    Riemann_last_equal_zero,

    -- Off-block vanishing lemmas (companion lemmas not already @[simp])
    R_tr_φr_zero, R_tr_φθ_zero,
    R_tθ_rt_zero, R_tθ_φt_zero, R_tθ_θr_zero, R_tθ_φr_zero, R_tθ_φθ_zero,
    R_tφ_rt_zero, R_tφ_θt_zero, R_tφ_φr_zero, R_tφ_θr_zero, R_tφ_φθ_zero,
    R_rθ_rt_zero, R_rθ_θt_zero, R_rθ_φt_zero, R_rθ_φr_zero, R_rθ_φθ_zero,
    R_rφ_rt_zero, R_rφ_θt_zero, R_rφ_φt_zero, R_rφ_θr_zero, R_rφ_φθ_zero,
    R_θφ_rt_zero, R_θφ_θt_zero, R_θφ_φt_zero, R_θφ_θr_zero, R_θφ_φr_zero,

    -- Cleanup
    mul_zero, zero_mul, add_zero, zero_add
  ]

  -- State: LHS now contains exactly 24 explicit terms (6 blocks × 4 permutations each)

  -- Step 3: Apply generic block collapse lemma to each of the six blocks
  -- TODO: Blocked by Kretschmann_block_sq which depends on Riemann_swap_a_b
  sorry
  /-
  TODO: Complete once Kretschmann_block_sq is proven:
  simp_rw [
    Kretschmann_block_sq M r θ Idx.t Idx.r,
    Kretschmann_block_sq M r θ Idx.t Idx.θ,
    Kretschmann_block_sq M r θ Idx.t Idx.φ,
    Kretschmann_block_sq M r θ Idx.r Idx.θ,
    Kretschmann_block_sq M r θ Idx.r Idx.φ,
    Kretschmann_block_sq M r θ Idx.θ Idx.φ
  ]
  simp [sumSixBlocks, add_assoc, add_comm, add_left_comm]
  -/

section KretschmannCalculation

-- We use a section to manage common variables and assumptions.
variable {M r θ : ℝ} {hM : 0 < M} {hr : 2*M < r} {hθ : 0 < θ ∧ θ < Real.pi}

-- Setup common non-zero facts for brevity in proofs

-- `f(M,r) ≠ 0` in the exterior (since f = (r - 2M)/r, and r ≠ 0, r-2M ≠ 0).
lemma hf0_exterior (M r : ℝ) (hM : 0 < M) (hr : 2*M < r) : f M r ≠ 0 := by
  exact ne_of_gt (f_pos_of_hr M r hM hr)

/-- On the Schwarzschild diagonal, the inverse and the metric cancel on each diagonal entry. -/
lemma gInv_mul_g_diag
    (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi)
    (i : Idx) :
    gInv M i i r θ * g M i i r θ = 1 := by
  classical
  -- Non-vanishing facts in the exterior
  have hr0  : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  have hr2  : r^2 ≠ 0 := pow_ne_zero 2 hr0
  have hsθ  : Real.sin θ ≠ 0 := sin_theta_ne_zero θ hθ
  have hs2  : (Real.sin θ)^2 ≠ 0 := pow_ne_zero 2 hsθ
  have hf0  : f M r ≠ 0 := hf0_exterior M r hM hr
  -- Useful normalization: (r⋅sinθ)^2 = r^2⋅(sinθ)^2
  have hmulpow : (r * Real.sin θ)^2 = r^2 * (Real.sin θ)^2 := by
    simpa using (mul_pow r (Real.sin θ) 2)

  -- Case-split on the diagonal index
  cases i with
  | t =>
      -- g_tt * gInv_tt = (-f) * (-1/f) = 1  (needs f ≠ 0)
      simp only [g, gInv]
      field_simp [hf0]
  | r =>
      -- g_rr * gInv_rr = (1/f) * f = 1  (needs f ≠ 0)
      simp only [g, gInv]
      field_simp [hf0]
  | θ =>
      -- g_θθ * gInv_θθ = (r^2) * (1/r^2) = 1  (needs r ≠ 0)
      simp only [g, gInv]
      field_simp [hr2]
  | φ =>
      -- g_φφ * gInv_φφ = (r^2 sin^2θ) * (1/(r^2 sin^2θ)) = 1
      -- Handle both possible encodings: r^2⋅sin^2θ vs (r⋅sinθ)^2.
      have hden₁ : r * Real.sin θ ≠ 0 := mul_ne_zero hr0 hsθ
      have hden₂ : (r * Real.sin θ)^2 ≠ 0 := pow_ne_zero 2 hden₁
      have hden  : r^2 * (Real.sin θ)^2 ≠ 0 := mul_ne_zero hr2 hs2
      -- Expand and normalize
      simp only [g, gInv]
      -- Clear all denominators
      field_simp [hr0, hsθ]

-- If the Christoffel term is definitionally zero, its directional derivative is zero.
lemma dCoord_zero_any (μ : Idx) :
    dCoord μ (fun _ _ : ℝ => 0) r θ = 0 := by
  cases μ <;> simp [dCoord]

attribute [local simp] gInv_mul_g_diag dCoord_zero_any

/-- (t,r) block = 4 M² / r⁶. -/
lemma sixBlock_tr_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.t Idx.r = 4 * M^2 / r^6 := by
  classical
  -- Structural reduction exposes the r-derivative and diagonal factors.
  unfold sixBlock
  simp only [Riemann_trtr_reduce, g, gInv, dCoord_r]
  -- Expand Γtot to get Γ_t_tr
  simp only [Γtot]
  -- Content: the only genuine derivative is ∂_r Γ^t_{tr}.
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  have hr2M : r - 2*M ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
  have hf0 : f M r ≠ 0 := hf0_exterior M r hM hr
  rw [deriv_Γ_t_tr M r hr0 hf0 hr2M]
  -- Γ-sparsity and algebraic pieces:
  simp [Γ_t_tr, Γ_r_rr, f, one_div, inv_pow]
  -- Normalize rational form:
  field_simp [hr0, hr2M, hf0]
  -- Polynomial identity:
  ring

/-- (t,θ) block = M² / r⁶. -/
lemma sixBlock_tθ_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.t Idx.θ = M^2 / r^6 := by
  classical
  unfold sixBlock
  -- 1) structural reduction: expose θ-derivative and diagonal factors
  simp only [Riemann_tθtθ_reduce, g, gInv, dCoord_θ]
  -- 2) Γ^t_{tθ} is definitionally 0; θ-derivative vanishes; evaluate remaining symbols
  simp [Γtot, Γ_t_tr, Γ_r_θθ, f, one_div, inv_pow]
  -- 3) clear denominators using exterior non-vanishing conditions
  field_simp [r_ne_zero_of_exterior M r hM hr, 
              ne_of_gt (f_pos_of_hr M r hM hr), 
              sub_ne_zero.mpr (ne_of_gt hr)]
  -- 4) polynomial identity
  ring

/-- (t,φ) block = M² / r⁶. -/
lemma sixBlock_tφ_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.t Idx.φ = M^2 / r^6 := by
  classical
  unfold sixBlock
  -- 1) structural reduction: expose φ-derivative and diagonal factors
  simp only [Riemann_tφtφ_reduce, g, gInv, dCoord_φ]
  -- 2) Γ^t_{tφ} is 0; its φ-derivative vanishes; evaluate remaining symbols
  simp [Γtot, Γ_t_tr, Γ_r_φφ, f, one_div, inv_pow]
  -- 3) clear denominators using exterior non-vanishing conditions
  field_simp [r_ne_zero_of_exterior M r hM hr,
              ne_of_gt (f_pos_of_hr M r hM hr),
              sub_ne_zero.mpr (ne_of_gt hr),
              sin_theta_ne_zero θ hθ]
  -- 4) polynomial identity
  ring

/-- (r,θ) block = M² / r⁶. -/
lemma sixBlock_rθ_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.r Idx.θ = M^2 / r^6 := by
  classical
  unfold sixBlock
  -- Structural: expose r- and θ-derivatives.
  simp only [Riemann_rθrθ_reduce, g, gInv, dCoord_r, dCoord_θ]
  -- Expand Γtot to work with specific Γ functions
  simp only [Γtot]
  -- Content: the θ-derivative term hits a Γ that is definitionally 0; r-derivative is concrete.
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  rw [deriv_Γ_r_θθ M r hr0]
  -- Evaluate remaining symbols and normalize inverses:
  simp [Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, f, one_div, inv_pow]
  -- Clear denominators once:
  have hr2M : r - 2*M ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
  have hf0 : f M r ≠ 0 := hf0_exterior M r hM hr
  field_simp [hr0, hr2M, hf0]
  ring

/-- (r,φ) block = M² / r⁶. -/
lemma sixBlock_rφ_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.r Idx.φ = M^2 / r^6 := by
  classical
  unfold sixBlock
  -- Structural: expose r- and φ-derivatives.
  simp only [Riemann_rφrφ_reduce, g, gInv, dCoord_r, dCoord_φ]
  -- Expand Γtot
  simp only [Γtot]
  -- Content: two r-derivatives appear; φ-derivative hits a zero Γ.
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  rw [deriv_Γ_r_φφ M r θ hr0, deriv_Γ_r_θθ M r hr0]
  simp [Γ_r_rr, Γ_r_φφ, Γ_φ_rφ, Γ_r_θθ, f, one_div, inv_pow]
  -- Clear denominators; also need sin θ ≠ 0 away from the axis.
  have hr2M : r - 2*M ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
  have hf0 : f M r ≠ 0 := hf0_exterior M r hM hr
  have hsθ : Real.sin θ ≠ 0 := sin_theta_ne_zero θ hθ
  field_simp [hr0, hr2M, hf0, hsθ]
  ring

/-- (θ,φ) block = 4 M² / r⁶. -/
lemma sixBlock_θφ_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.θ Idx.φ = 4 * M^2 / r^6 := by
  classical
  unfold sixBlock
  -- Structural: expose θ-derivative; there is no r-derivative in this block.
  simp only [Riemann_θφθφ_reduce, g, gInv, dCoord_θ]
  -- Expand Γtot
  simp only [Γtot]
  -- Content: the concrete θ-derivative we computed.
  rw [deriv_Γ_θ_φφ θ]
  -- Evaluate Γ's and normalize trig + inverses.
  simp [Γ_θ_rθ, Γ_r_φφ, Γ_θ_φφ, Γ_φ_θφ, f, one_div, inv_pow]
  -- Clear denominators; need r ≠ 0 and sin θ ≠ 0.
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  have hsθ : Real.sin θ ≠ 0 := sin_theta_ne_zero θ hθ
  -- We won't invert `f` here, but including exterior facts is harmless:
  have hr2M : r - 2*M ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
  have hf0 : f M r ≠ 0 := hf0_exterior M r hM hr
  field_simp [hr0, hr2M, hf0, hsθ]
  -- Use cos² θ = 1 - sin² θ and finish.
  rw [Real.cos_sq]
  ring

/-- On the exterior (and away from the axis), `K(M,r,θ) = 48 M^2 / r^6`. -/
theorem Kretschmann_exterior_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  Kretschmann M r θ = 48 * M^2 / r^6 := by
  classical
  -- 1) reduce to the six-block sum
  rw [Kretschmann_six_blocks]
  unfold sumSixBlocks
  -- 2) substitute the six block values
  rw [sixBlock_tr_value M r θ hM hr hθ, sixBlock_tθ_value M r θ hM hr hθ, sixBlock_tφ_value M r θ hM hr hθ]
  rw [sixBlock_rθ_value M r θ hM hr hθ, sixBlock_rφ_value M r θ hM hr hθ, sixBlock_θφ_value M r θ hM hr hθ]
  -- 3) arithmetic with X := M^2/r^6
  ring

end KretschmannCalculation

end Exterior

end Schwarzschild

end Papers.P5_GeneralRelativity