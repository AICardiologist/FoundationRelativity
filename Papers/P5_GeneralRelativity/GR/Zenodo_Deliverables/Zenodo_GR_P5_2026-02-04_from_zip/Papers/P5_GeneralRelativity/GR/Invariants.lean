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

-- Normalize raw four-factor weights into squared weights (for Kretschmann blocks)
private lemma weight_xyxy (x y : ℝ) : x * y * x * y = x^2 * y^2 := by ring
private lemma weight_xyyx (x y : ℝ) : x * y * y * x = x^2 * y^2 := by ring
private lemma weight_yxxy (x y : ℝ) : y * x * x * y = x^2 * y^2 := by ring
private lemma weight_yxyx (x y : ℝ) : y * x * y * x = x^2 * y^2 := by ring

/-- Simplify `0^2` directly (for cleanup in large sums). -/
private lemma zero_sq : (0:ℝ)^2 = 0 := by simp


-- Reorder the outer `sumIdx2` to pair (a,b) with (b,a), keeping diagonals together.
private lemma sumIdx2_expand_pairs (f : Idx → Idx → ℝ) :
  sumIdx2 f =
    (f Idx.t Idx.r + f Idx.r Idx.t) +
    (f Idx.t Idx.θ + f Idx.θ Idx.t) +
    (f Idx.t Idx.φ + f Idx.φ Idx.t) +
    (f Idx.r Idx.θ + f Idx.θ Idx.r) +
    (f Idx.r Idx.φ + f Idx.φ Idx.r) +
    (f Idx.θ Idx.φ + f Idx.φ Idx.θ) +
    (f Idx.t Idx.t + f Idx.r Idx.r + f Idx.θ Idx.θ + f Idx.φ Idx.φ) := by
  -- Expand the 4×4 sum and regroup by AC.
  simp [sumIdx2_expand, add_assoc, add_left_comm, add_comm]

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
  ring_nf

/-! ### Helper lemmas: Individual block contributions

These lemmas prove that the 4 permutations for each index pair
sum to 4 times the canonical sixBlock value. -/

/-- Local helper: Riemann squared is symmetric under first-pair swap.
    Uses `Riemann_swap_a_b` on the exterior/off-axis domain. -/
private lemma Riemann_sq_swap_a_b
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0)
    (a b c d : Idx) :
  (Riemann M r θ b a c d)^2 = (Riemann M r θ a b c d)^2 := by
  rw [Riemann_swap_a_b M r θ h_ext hθ, sq_neg]

-- First-pair antisymmetry: R_{a a c d} = 0.
private lemma Riemann_first_equal_zero
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0)
    (a c d : Idx) :
  Riemann M r θ a a c d = 0 := by
  have h := Riemann_swap_a_b M r θ h_ext hθ a a c d
  have h' : (2:ℝ) * Riemann M r θ a a c d = 0 := by
    calc
      (2:ℝ) * Riemann M r θ a a c d
          = Riemann M r θ a a c d + Riemann M r θ a a c d := by ring
      _ = Riemann M r θ a a c d + (- Riemann M r θ a a c d) := by
            simpa using congrArg (fun x => Riemann M r θ a a c d + x) h
      _ = 0 := by ring
  have h2 : (2:ℝ) ≠ 0 := by exact two_ne_zero
  exact (mul_eq_zero.mp h').resolve_left h2

-- Fixed-order swap helpers to normalize the *first* index pair.
private lemma Riemann_sq_swap_rt
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) (c d : Idx) :
  (Riemann M r θ Idx.r Idx.t c d)^2 = (Riemann M r θ Idx.t Idx.r c d)^2 := by
  simpa using (Riemann_sq_swap_a_b M r θ h_ext hθ Idx.t Idx.r c d)

private lemma Riemann_sq_swap_θt
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) (c d : Idx) :
  (Riemann M r θ Idx.θ Idx.t c d)^2 = (Riemann M r θ Idx.t Idx.θ c d)^2 := by
  simpa using (Riemann_sq_swap_a_b M r θ h_ext hθ Idx.t Idx.θ c d)

private lemma Riemann_sq_swap_φt
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) (c d : Idx) :
  (Riemann M r θ Idx.φ Idx.t c d)^2 = (Riemann M r θ Idx.t Idx.φ c d)^2 := by
  simpa using (Riemann_sq_swap_a_b M r θ h_ext hθ Idx.t Idx.φ c d)

private lemma Riemann_sq_swap_θr
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) (c d : Idx) :
  (Riemann M r θ Idx.θ Idx.r c d)^2 = (Riemann M r θ Idx.r Idx.θ c d)^2 := by
  simpa using (Riemann_sq_swap_a_b M r θ h_ext hθ Idx.r Idx.θ c d)

private lemma Riemann_sq_swap_φr
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) (c d : Idx) :
  (Riemann M r θ Idx.φ Idx.r c d)^2 = (Riemann M r θ Idx.r Idx.φ c d)^2 := by
  simpa using (Riemann_sq_swap_a_b M r θ h_ext hθ Idx.r Idx.φ c d)

private lemma Riemann_sq_swap_φθ
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) (c d : Idx) :
  (Riemann M r θ Idx.φ Idx.θ c d)^2 = (Riemann M r θ Idx.θ Idx.φ c d)^2 := by
  simpa using (Riemann_sq_swap_a_b M r θ h_ext hθ Idx.θ Idx.φ c d)


-- A single squared-weight term is exactly a `sixBlock`.
private lemma sixBlock_sq_form (M r θ : ℝ) (a b : Idx) :
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b a b)^2 =
    sixBlock M r θ a b := by
  unfold sixBlock
  ring

-- Squared-weight variants that tolerate swapped weight order and/or last-pair order.
private lemma sixBlock_sq_form_swap_cd (M r θ : ℝ) (a b : Idx) :
  (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b b a)^2 =
    sixBlock M r θ a b := by
  have hcd :
      (Riemann M r θ a b b a)^2 = (Riemann M r θ a b a b)^2 := by
    simpa using (Riemann_sq_swap_c_d M r θ a b a b)
  calc
    (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b b a)^2
        = (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b a b)^2 := by
            rw [hcd]
    _ = sixBlock M r θ a b := by
          simpa using (sixBlock_sq_form M r θ a b)

private lemma sixBlock_sq_form_swap_wt (M r θ : ℝ) (a b : Idx) :
  (gInv M b b r θ)^2 * (gInv M a a r θ)^2 * (Riemann M r θ a b a b)^2 =
    sixBlock M r θ a b := by
  calc
    (gInv M b b r θ)^2 * (gInv M a a r θ)^2 * (Riemann M r θ a b a b)^2
        = (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b a b)^2 := by ring
    _ = sixBlock M r θ a b := by
          simpa using (sixBlock_sq_form M r θ a b)

private lemma sixBlock_sq_form_swap_wt_cd (M r θ : ℝ) (a b : Idx) :
  (gInv M b b r θ)^2 * (gInv M a a r θ)^2 * (Riemann M r θ a b b a)^2 =
    sixBlock M r θ a b := by
  calc
    (gInv M b b r θ)^2 * (gInv M a a r θ)^2 * (Riemann M r θ a b b a)^2
        = (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b b a)^2 := by ring
    _ = sixBlock M r θ a b := by
          have hcd :
              (Riemann M r θ a b b a)^2 = (Riemann M r θ a b a b)^2 := by
            simpa using (Riemann_sq_swap_c_d M r θ a b a b)
          -- apply the base form after swapping the last pair
          calc
            (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b b a)^2
                = (gInv M a a r θ)^2 * (gInv M b b r θ)^2 * (Riemann M r θ a b a b)^2 := by
                    rw [hcd]
            _ = sixBlock M r θ a b := by
                  simpa using (sixBlock_sq_form M r θ a b)

/-- **Six-block identity** (diagonal raising):
`K = 4 * Σ_{a<b} (g^{aa} g^{bb})^2 (R_{ab ab})^2`.

This structural lemma shows that the 256-term Kretschmann contraction
reduces to just 6 blocks (one for each unordered index pair) with factor 4. -/
lemma Kretschmann_six_blocks
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) :
    Kretschmann M r θ = 4 * sumSixBlocks M r θ := by
  classical

  -- Step 1: Expand to 256 terms
  rw [Kretschmann_after_raise_sq]
  -- Pair (a,b) with (b,a) at the outer sum to match block lemmas.
  rw [sumIdx2_expand_pairs]
  -- Expand the inner sums over (c,d).
  simp only [sumIdx2_expand]

  -- Step 2: Eliminate the 232 zero terms via simplification
  -- This relies on: (i) symmetry vanishing (R_abcc = 0)
  --                 (ii) off-block vanishing (60 lemmas)
  simp only [
    -- Equal-pair zeros
    Riemann_last_equal_zero,
    Riemann_first_equal_zero M r θ h_ext hθ,

    -- Off-block vanishing lemmas (full list; `simp only` ignores @[simp] tags)
    R_tr_tθ_zero, R_tr_θt_zero, R_tr_tφ_zero, R_tr_φt_zero, R_tr_rθ_zero, R_tr_θr_zero,
    R_tr_rφ_zero, R_tr_φr_zero, R_tr_θφ_zero, R_tr_φθ_zero,

    R_tθ_tr_zero, R_tθ_rt_zero, R_tθ_tφ_zero, R_tθ_φt_zero, R_tθ_rθ_zero, R_tθ_θr_zero,
    R_tθ_rφ_zero, R_tθ_φr_zero, R_tθ_θφ_zero, R_tθ_φθ_zero,

    R_tφ_tr_zero, R_tφ_rt_zero, R_tφ_tθ_zero, R_tφ_θt_zero, R_tφ_rφ_zero, R_tφ_φr_zero,
    R_tφ_rθ_zero, R_tφ_θr_zero, R_tφ_θφ_zero, R_tφ_φθ_zero,

    R_rθ_tr_zero, R_rθ_rt_zero, R_rθ_tθ_zero, R_rθ_θt_zero, R_rθ_tφ_zero, R_rθ_φt_zero,
    R_rθ_rφ_zero, R_rθ_φr_zero, R_rθ_θφ_zero, R_rθ_φθ_zero,

    R_rφ_tr_zero, R_rφ_rt_zero, R_rφ_tθ_zero, R_rφ_θt_zero, R_rφ_tφ_zero, R_rφ_φt_zero,
    R_rφ_rθ_zero, R_rφ_θr_zero, R_rφ_θφ_zero, R_rφ_φθ_zero,

    R_θφ_tr_zero, R_θφ_rt_zero, R_θφ_tθ_zero, R_θφ_θt_zero, R_θφ_tφ_zero, R_θφ_φt_zero,
    R_θφ_rθ_zero, R_θφ_θr_zero, R_θφ_rφ_zero, R_θφ_φr_zero,

    -- Cleanup
    zero_sq, mul_zero, add_zero, zero_add
  ]
  -- Normalize the squared Riemann terms by swapping pairs, then clear any newly matching zeros.
  try
    simp_rw [
      Riemann_sq_swap_rt M r θ h_ext hθ,
      Riemann_sq_swap_θt M r θ h_ext hθ,
      Riemann_sq_swap_φt M r θ h_ext hθ,
      Riemann_sq_swap_θr M r θ h_ext hθ,
      Riemann_sq_swap_φr M r θ h_ext hθ,
      Riemann_sq_swap_φθ M r θ h_ext hθ,
      Riemann_sq_swap_c_d
    ]
  simp only [
    Riemann_last_equal_zero,
    R_tr_tθ_zero, R_tr_θt_zero, R_tr_tφ_zero, R_tr_φt_zero, R_tr_rθ_zero, R_tr_θr_zero,
    R_tr_rφ_zero, R_tr_φr_zero, R_tr_θφ_zero, R_tr_φθ_zero,

    R_tθ_tr_zero, R_tθ_rt_zero, R_tθ_tφ_zero, R_tθ_φt_zero, R_tθ_rθ_zero, R_tθ_θr_zero,
    R_tθ_rφ_zero, R_tθ_φr_zero, R_tθ_θφ_zero, R_tθ_φθ_zero,

    R_tφ_tr_zero, R_tφ_rt_zero, R_tφ_tθ_zero, R_tφ_θt_zero, R_tφ_rφ_zero, R_tφ_φr_zero,
    R_tφ_rθ_zero, R_tφ_θr_zero, R_tφ_θφ_zero, R_tφ_φθ_zero,

    R_rθ_tr_zero, R_rθ_rt_zero, R_rθ_tθ_zero, R_rθ_θt_zero, R_rθ_tφ_zero, R_rθ_φt_zero,
    R_rθ_rφ_zero, R_rθ_φr_zero, R_rθ_θφ_zero, R_rθ_φθ_zero,

    R_rφ_tr_zero, R_rφ_rt_zero, R_rφ_tθ_zero, R_rφ_θt_zero, R_rφ_tφ_zero, R_rφ_φt_zero,
    R_rφ_rθ_zero, R_rφ_θr_zero, R_rφ_θφ_zero, R_rφ_φθ_zero,

    R_θφ_tr_zero, R_θφ_rt_zero, R_θφ_tθ_zero, R_θφ_θt_zero, R_θφ_tφ_zero, R_θφ_φt_zero,
    R_θφ_rθ_zero, R_θφ_θr_zero, R_θφ_rφ_zero, R_θφ_φr_zero,

    zero_sq, mul_zero, zero_mul, add_zero, zero_add
  ]

  -- State: LHS now contains exactly 24 explicit terms (6 blocks × 4 permutations each)

  -- Normalize raw 4-factor weights into squared weights.
  simp only [weight_xyxy, weight_xyyx]

  -- Step 3: Canonicalize last-pair order, convert each term to `sixBlock`,
  -- then collapse 4 identical terms per block.
  simp only [
    sixBlock_sq_form,
    sixBlock_sq_form_swap_cd,
    sixBlock_sq_form_swap_wt,
    sixBlock_sq_form_swap_wt_cd,
    sumSixBlocks
  ]
  ring_nf

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
lemma sixBlock_tr_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (_hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.t Idx.r = 4 * M^2 / r^6 := by
  classical
  unfold sixBlock
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  have hf0 : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr)
  simp only [gInv, Riemann_trtr_eq M r θ hM hr, pow_two]
  field_simp [hr0, hf0]
  ring

/-- (t,θ) block = M² / r⁶. -/
lemma sixBlock_tθ_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (_hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.t Idx.θ = M^2 / r^6 := by
  classical
  unfold sixBlock
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  have hf0 : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr)
  simp only [gInv, Riemann_tθtθ_eq M r θ hM hr, pow_two]
  field_simp [hr0, hf0]

/-- (t,φ) block = M² / r⁶. -/
lemma sixBlock_tφ_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.t Idx.φ = M^2 / r^6 := by
  classical
  unfold sixBlock
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  have hf0 : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr)
  have hsθ : Real.sin θ ≠ 0 := sin_theta_ne_zero θ hθ
  simp only [gInv, Riemann_tφtφ_eq M r θ hM hr, pow_two]
  field_simp [hr0, hf0, hsθ]

/-- (r,θ) block = M² / r⁶. -/
lemma sixBlock_rθ_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (_hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.r Idx.θ = M^2 / r^6 := by
  classical
  unfold sixBlock
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  have hf0 : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr)
  simp only [gInv, Riemann_rθrθ_eq M r θ hM hr, pow_two]
  field_simp [hr0, hf0]

/-- (r,φ) block = M² / r⁶. -/
lemma sixBlock_rφ_value (M r θ : ℝ) (hM : 0 < M) (hr : 2*M < r) (hθ : 0 < θ ∧ θ < Real.pi) :
  sixBlock M r θ Idx.r Idx.φ = M^2 / r^6 := by
  classical
  unfold sixBlock
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  have hf0 : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr)
  have hsθ : Real.sin θ ≠ 0 := sin_theta_ne_zero θ hθ
  simp only [gInv, Riemann_rφrφ_eq M r θ hM hr, pow_two]
  field_simp [hr0, hf0, hsθ]

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
  simp [Γ_θ_rθ, Γ_r_φφ, Γ_θ_φφ, Γ_φ_θφ, one_div, inv_pow]
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
  have h_ext : Exterior M r θ := ⟨hM, hr⟩
  have hsθ : Real.sin θ ≠ 0 := sin_theta_ne_zero θ hθ
  rw [Kretschmann_six_blocks M r θ h_ext hsθ]
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
