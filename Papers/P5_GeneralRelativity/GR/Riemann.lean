-- Papers/P5_GeneralRelativity/GR/Riemann.lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild

namespace Papers.P5_GeneralRelativity
open Papers.P5_GeneralRelativity
open Real

namespace Schwarzschild
open Idx

/-!
  # Riemann tensor (scaffold)

  We work at fixed `(M, r, θ)` and use the project's `Γtot` aggregator:
  `Γtot M r θ ρ μ ν` ≡ Γ^ρ_{μν}(r,θ) in Schwarzschild coordinates.

  The helper `dCoord μ F r θ` implements the coordinate derivative ∂_μ F
  for 2-argument fields F : ℝ → ℝ → ℝ, with only `r` and `θ` directions active.
-/

/-- Coordinate derivative in the μ-direction for fields `F : ℝ → ℝ → ℝ`.
    Only `r` and `θ` derivatives are nonzero; `t` and `φ` derivatives are zero
    (static and axisymmetric). -/
@[simp] noncomputable def dCoord (μ : Idx) (F : ℝ → ℝ → ℝ) (r θ : ℝ) : ℝ :=
  match μ with
  | Idx.r => deriv (fun s => F s θ) r
  | Idx.θ => deriv (fun t => F r t) θ
  | _     => 0

@[simp] lemma dCoord_t (F : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord Idx.t F r θ = 0 := rfl

@[simp] lemma dCoord_φ (F : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord Idx.φ F r θ = 0 := rfl

@[simp] lemma dCoord_r (F : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord Idx.r F r θ = deriv (fun s => F s θ) r := rfl

@[simp] lemma dCoord_θ (F : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord Idx.θ F r θ = deriv (fun t => F r t) θ := rfl

@[simp] lemma dCoord_θ_const (c r θ : ℝ) :
  dCoord Idx.θ (fun _ _ => c) r θ = 0 := by
  simp [dCoord_θ]

@[simp] lemma dCoord_φ_const (c r θ : ℝ) :
  dCoord Idx.φ (fun _ _ => c) r θ = 0 := by
  simp [dCoord_φ]

/-- Mixed-index Riemann tensor:
    `RiemannUp M r θ ρ σ μ ν = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ}
                               + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}`. -/
noncomputable def RiemannUp
    (M r θ : ℝ) (ρ σ μ ν : Idx) : ℝ :=
  dCoord μ (fun r θ => Γtot M r θ ρ ν σ) r θ
- dCoord ν (fun r θ => Γtot M r θ ρ μ σ) r θ
+ sumIdx (fun lam =>
    Γtot M r θ ρ μ lam * Γtot M r θ lam ν σ
  - Γtot M r θ ρ ν lam * Γtot M r θ lam μ σ)

/-- Fully-lowered Riemann tensor `R_{a b c d}` by lowering the first index with `g`. -/
noncomputable def Riemann
    (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b c d)

/-- Contract the first index against the diagonal metric:
    only the term `ρ = a` contributes. -/
@[simp] lemma Riemann_contract_first
  (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d =
    g M a a r θ * RiemannUp M r θ a b c d := by
  classical
  -- expand the ρ-sum and use the diagonal equations for g
  cases a <;> -- a = t | r | θ | φ
    simp [Riemann, sumIdx_expand, g]

/-! ## Small structural simp lemmas -/

/-- Trivial case: `R^ρ{}_{σ μ μ} = 0` by definition. -/
@[simp] lemma RiemannUp_mu_eq_nu (M r θ : ℝ) (ρ σ μ : Idx) :
  RiemannUp M r θ ρ σ μ μ = 0 := by
  -- Expand the definition and cancel.
  simp [RiemannUp]

@[simp] lemma RiemannUp_swap_mu_nu
    (M r θ : ℝ) (ρ σ μ ν : Idx) :
  RiemannUp M r θ ρ σ μ ν = - RiemannUp M r θ ρ σ ν μ := by
  -- Directly from the definition: each term flips sign under μ ↔ ν
  simp [RiemannUp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

/-- Antisymmetry in the last two (lower) slots after lowering the first index. -/
lemma Riemann_swap_c_d
    (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d = - Riemann M r θ a b d c := by
  classical
  unfold Riemann
  -- Riemann is the lowered version of RiemannUp; use μ↔ν antisymmetry of RiemannUp
  -- and pull the minus out of the finite sum.
  have h : (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b c d)
          = (fun ρ => - (g M a ρ r θ * RiemannUp M r θ ρ b d c)) := by
    funext ρ
    -- from μ↔ν antisymmetry on the mixed tensor
    rw [RiemannUp_swap_mu_nu]
    ring
  calc
    sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b c d)
        = sumIdx (fun ρ => - (g M a ρ r θ * RiemannUp M r θ ρ b d c)) := by rw [h]
    _   = - sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b d c) := by
            rw [sumIdx_neg (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b d c)]

/-- Helper lemma for squaring: (-x)^2 = x^2. -/
@[simp] lemma sq_neg (x : ℝ) : (-x)^2 = x^2 := by ring

/-- Antisymmetry in the first two (lower) slots. R_abcd = -R_bacd. -/
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d = - Riemann M r θ b a c d := by
  -- Standard property of the Riemann tensor derived from its definition.
  sorry -- Requires expanding the definition and using properties of the connection.

/-- Squared symmetry in the first pair. Safer for simp. -/
lemma Riemann_sq_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  (Riemann M r θ b a c d)^2 = (Riemann M r θ a b c d)^2 := by
  rw [Riemann_swap_a_b, sq_neg]

/-- Squared symmetry in the last pair. Safer for simp. -/
lemma Riemann_sq_swap_c_d (M r θ : ℝ) (a b c d : Idx) :
  (Riemann M r θ a b d c)^2 = (Riemann M r θ a b c d)^2 := by
  rw [Riemann_swap_c_d, sq_neg]

/-- If the first index is lowered with a diagonal `g`, in many cases only `ρ = a`
    contributes in the sum. This lemma doesn't assert diagonality; it's a
    convenient rewriting point for later `simp [g]`. -/
@[simp] lemma Riemann_lower_def (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d
    = sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b c d) := rfl

/-- For the `tθtθ` component: compute the λ-sum in `RiemannUp` by enumeration. -/
@[simp] lemma row_tθtθ (M r θ : ℝ) :
  sumIdx (fun lam =>
      Γtot M r θ Idx.t Idx.t lam * Γtot M r θ lam Idx.θ Idx.θ
    - Γtot M r θ Idx.t Idx.θ lam * Γtot M r θ lam Idx.t Idx.θ)
  = Γ_t_tr M r * Γ_r_θθ M r := by
  classical
  -- Enumerate lam = t | r | θ | φ and let the Γ-table decide each clause
  have ht : (Γtot M r θ Idx.t Idx.t Idx.t * Γtot M r θ Idx.t Idx.θ Idx.θ
           - Γtot M r θ Idx.t Idx.θ Idx.t * Γtot M r θ Idx.t Idx.t Idx.θ) = 0 := by
    simp only [Γtot]; simp
  have hr : (Γtot M r θ Idx.t Idx.t Idx.r * Γtot M r θ Idx.r Idx.θ Idx.θ
           - Γtot M r θ Idx.t Idx.θ Idx.r * Γtot M r θ Idx.r Idx.t Idx.θ)
           = Γ_t_tr M r * Γ_r_θθ M r := by
    simp only [Γtot]; simp
  have hθ : (Γtot M r θ Idx.t Idx.t Idx.θ * Γtot M r θ Idx.θ Idx.θ Idx.θ
           - Γtot M r θ Idx.t Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.t Idx.θ) = 0 := by
    simp only [Γtot]; simp
  have hφ : (Γtot M r θ Idx.t Idx.t Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.θ
           - Γtot M r θ Idx.t Idx.θ Idx.φ * Γtot M r θ Idx.φ Idx.t Idx.θ) = 0 := by
    simp only [Γtot]; simp
  -- put the four cases together
  simp only [sumIdx_expand]
  rw [ht, hr, hθ, hφ]
  ring

/-- For the `tφtφ` component: compute the λ-sum in `RiemannUp` by enumeration. -/
@[simp] lemma row_tφtφ (M r θ : ℝ) :
  sumIdx (fun lam =>
      Γtot M r θ Idx.t Idx.t lam * Γtot M r θ lam Idx.φ Idx.φ
    - Γtot M r θ Idx.t Idx.φ lam * Γtot M r θ lam Idx.t Idx.φ)
  = Γ_t_tr M r * Γ_r_φφ M r θ := by
  classical
  have ht : (Γtot M r θ Idx.t Idx.t Idx.t * Γtot M r θ Idx.t Idx.φ Idx.φ
           - Γtot M r θ Idx.t Idx.φ Idx.t * Γtot M r θ Idx.t Idx.t Idx.φ) = 0 := by
    simp only [Γtot]; simp
  have hr : (Γtot M r θ Idx.t Idx.t Idx.r * Γtot M r θ Idx.r Idx.φ Idx.φ
           - Γtot M r θ Idx.t Idx.φ Idx.r * Γtot M r θ Idx.r Idx.t Idx.φ)
           = Γ_t_tr M r * Γ_r_φφ M r θ := by
    simp only [Γtot]; simp
  have hθ : (Γtot M r θ Idx.t Idx.t Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
           - Γtot M r θ Idx.t Idx.φ Idx.θ * Γtot M r θ Idx.θ Idx.t Idx.φ) = 0 := by
    simp only [Γtot]; simp
  have hφ : (Γtot M r θ Idx.t Idx.t Idx.φ * Γtot M r θ Idx.φ Idx.φ Idx.φ
           - Γtot M r θ Idx.t Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.t Idx.φ) = 0 := by
    simp only [Γtot]; simp
  -- put the four cases together
  simp only [sumIdx_expand]
  rw [ht, hr, hθ, hφ]
  ring

/-- For the `rθrθ` component: compute the λ-sum in `RiemannUp` by enumeration. -/
@[simp] lemma row_rθrθ (M r θ : ℝ) :
  sumIdx (fun lam =>
      Γtot M r θ Idx.r Idx.r lam * Γtot M r θ lam Idx.θ Idx.θ
    - Γtot M r θ Idx.r Idx.θ lam * Γtot M r θ lam Idx.r Idx.θ)
  = Γ_r_rr M r * Γ_r_θθ M r - Γ_θ_rθ r * Γ_r_θθ M r := by
  classical
  have ht : (Γtot M r θ Idx.r Idx.r Idx.t * Γtot M r θ Idx.t Idx.θ Idx.θ
           - Γtot M r θ Idx.r Idx.θ Idx.t * Γtot M r θ Idx.t Idx.r Idx.θ) = 0 := by
    simp only [Γtot]; simp
  have hr : (Γtot M r θ Idx.r Idx.r Idx.r * Γtot M r θ Idx.r Idx.θ Idx.θ
           - Γtot M r θ Idx.r Idx.θ Idx.r * Γtot M r θ Idx.r Idx.r Idx.θ)
           = Γ_r_rr M r * Γ_r_θθ M r := by
    simp only [Γtot]; simp
  have hθ : (Γtot M r θ Idx.r Idx.r Idx.θ * Γtot M r θ Idx.θ Idx.θ Idx.θ
           - Γtot M r θ Idx.r Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.r Idx.θ)
           = - Γ_θ_rθ r * Γ_r_θθ M r := by
    simp [Γtot, Γ_θ_rθ]; ring
  have hφ : (Γtot M r θ Idx.r Idx.r Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.θ
           - Γtot M r θ Idx.r Idx.θ Idx.φ * Γtot M r θ Idx.φ Idx.r Idx.θ) = 0 := by
    simp only [Γtot]; simp
  -- put the four cases together
  simp only [sumIdx_expand]
  rw [ht, hr, hθ, hφ]
  ring

/-- Canonical reduction for `R_{rθrθ}`. Keeps derivatives symbolic, just like your Ricci pipeline. -/
lemma Riemann_rθrθ_reduce (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.r Idx.θ
    = g M Idx.r Idx.r r θ * (dCoord Idx.r (fun r θ => Γtot M r θ Idx.r Idx.θ Idx.θ) r θ
                              - dCoord Idx.θ (fun r θ => Γtot M r θ Idx.r Idx.r Idx.θ) r θ
                              + Γ_r_rr M r * Γ_r_θθ M r
                              - Γ_θ_rθ r * Γ_r_θθ M r) := by
  classical
  -- 1) Contract first index
  rw [Riemann_contract_first]
  -- 2) Unfold exactly once
  unfold RiemannUp
  -- 3) Expand dCoord_r
  simp only [dCoord_r]
  -- 4) Apply the row lemma
  rw [row_rθrθ]
  -- 5) Algebra
  ring

/-- For the `θφθφ` component: compute the λ-sum in `RiemannUp` by enumeration. -/
@[simp] lemma row_θφθφ (M r θ : ℝ) :
  sumIdx (fun lam =>
      Γtot M r θ Idx.θ Idx.θ lam * Γtot M r θ lam Idx.φ Idx.φ
    - Γtot M r θ Idx.θ Idx.φ lam * Γtot M r θ lam Idx.θ Idx.φ)
  = Γ_θ_rθ r * Γ_r_φφ M r θ - Γ_θ_φφ θ * Γ_φ_θφ θ := by
  classical
  have ht : (Γtot M r θ Idx.θ Idx.θ Idx.t * Γtot M r θ Idx.t Idx.φ Idx.φ
           - Γtot M r θ Idx.θ Idx.φ Idx.t * Γtot M r θ Idx.t Idx.θ Idx.φ) = 0 := by
    simp only [Γtot]; simp
  have hr : (Γtot M r θ Idx.θ Idx.θ Idx.r * Γtot M r θ Idx.r Idx.φ Idx.φ
           - Γtot M r θ Idx.θ Idx.φ Idx.r * Γtot M r θ Idx.r Idx.θ Idx.φ)
           = Γ_θ_rθ r * Γ_r_φφ M r θ := by
    simp [Γtot, Γ_θ_rθ]
  have hθ : (Γtot M r θ Idx.θ Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
           - Γtot M r θ Idx.θ Idx.φ Idx.θ * Γtot M r θ Idx.θ Idx.θ Idx.φ) = 0 := by
    simp only [Γtot]; simp
  have hφ : (Γtot M r θ Idx.θ Idx.θ Idx.φ * Γtot M r θ Idx.φ Idx.φ Idx.φ
           - Γtot M r θ Idx.θ Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.φ)
           = - Γ_θ_φφ θ * Γ_φ_θφ θ := by
    simp [Γtot, Γ_θ_φφ, Γ_φ_θφ]
  -- put the four cases together
  simp only [sumIdx_expand]
  rw [ht, hr, hθ, hφ]
  ring

/-- Canonical reduction for `R_{θφθφ}`. Again, fully structural; no numeric evaluation. -/
lemma Riemann_θφθφ_reduce (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.φ
    = g M Idx.θ Idx.θ r θ * (dCoord Idx.θ (fun r θ => Γtot M r θ Idx.θ Idx.φ Idx.φ) r θ
                              - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.θ Idx.θ Idx.φ) r θ
                              + Γ_θ_rθ r * Γ_r_φφ M r θ
                              - Γ_θ_φφ θ * Γ_φ_θφ θ) := by
  classical
  -- 1) Contract first index
  rw [Riemann_contract_first]
  -- 2) Unfold exactly once
  unfold RiemannUp
  -- 3) Expand dCoord_θ and kill dCoord_φ
  simp only [dCoord_θ, dCoord_φ]
  -- 4) Apply the row lemma
  rw [row_θφθφ]
  -- 5) Algebra
  ring

/-- For the `trtr` component: compute the λ-sum in `RiemannUp` by enumeration. -/
@[simp] lemma row_trtr (M r θ : ℝ) :
  sumIdx (fun lam =>
      Γtot M r θ Idx.t Idx.t lam * Γtot M r θ lam Idx.r Idx.r
    - Γtot M r θ Idx.t Idx.r lam * Γtot M r θ lam Idx.t Idx.r)
  = Γ_t_tr M r * Γ_r_rr M r - Γ_t_tr M r * Γ_t_tr M r := by
  classical
  have ht : (Γtot M r θ Idx.t Idx.t Idx.t * Γtot M r θ Idx.t Idx.r Idx.r
           - Γtot M r θ Idx.t Idx.r Idx.t * Γtot M r θ Idx.t Idx.t Idx.r)
           = - Γ_t_tr M r * Γ_t_tr M r := by
    simp only [Γtot]; simp
  have hr : (Γtot M r θ Idx.t Idx.t Idx.r * Γtot M r θ Idx.r Idx.r Idx.r
           - Γtot M r θ Idx.t Idx.r Idx.r * Γtot M r θ Idx.r Idx.t Idx.r)
           = Γ_t_tr M r * Γ_r_rr M r := by
    simp only [Γtot]; simp
  have hθ : (Γtot M r θ Idx.t Idx.t Idx.θ * Γtot M r θ Idx.θ Idx.r Idx.r
           - Γtot M r θ Idx.t Idx.r Idx.θ * Γtot M r θ Idx.θ Idx.t Idx.r) = 0 := by
    simp only [Γtot]; simp
  have hφ : (Γtot M r θ Idx.t Idx.t Idx.φ * Γtot M r θ Idx.φ Idx.r Idx.r
           - Γtot M r θ Idx.t Idx.r Idx.φ * Γtot M r θ Idx.φ Idx.t Idx.r) = 0 := by
    simp only [Γtot]; simp
  -- put the four cases together
  simp only [sumIdx_expand]
  rw [ht, hr, hθ, hφ]
  ring

/-- Canonical reduction for `R_{t r t r}`. Staticity kills all `∂_t`-terms. -/
lemma Riemann_trtr_reduce (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.t Idx.r
    = g M Idx.t Idx.t r θ * (- dCoord Idx.r (fun r θ => Γtot M r θ Idx.t Idx.t Idx.r) r θ
                              + Γ_t_tr M r * Γ_r_rr M r
                              - Γ_t_tr M r * Γ_t_tr M r) := by
  classical
  -- 1) Contract first index
  rw [Riemann_contract_first]
  -- 2) Unfold exactly once
  unfold RiemannUp
  -- 3) Kill static derivative
  simp only [dCoord_t]
  -- 4) Apply the row lemma
  rw [row_trtr]
  -- 5) Algebra
  ring

/-- Canonical reduction for `R_{t θ t θ}`. -/
lemma Riemann_tθtθ_reduce (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ
    = g M Idx.t Idx.t r θ * (- dCoord Idx.θ (fun r θ => Γtot M r θ Idx.t Idx.t Idx.θ) r θ
                             + Γ_t_tr M r * Γ_r_θθ M r) := by
  classical
  -- 1) Contract first index
  rw [Riemann_contract_first]
  -- 2) Unfold exactly once
  unfold RiemannUp
  -- 3) Simplify (dCoord_t will give 0)
  simp only [dCoord_t]
  -- 4) Apply the row lemma
  rw [row_tθtθ]
  -- 5) Algebra
  ring

/-- Canonical reduction for `R_{t φ t φ}` (axisymmetry kills `∂_φ`). -/
lemma Riemann_tφtφ_reduce (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ
    = g M Idx.t Idx.t r θ * Γ_t_tr M r * Γ_r_φφ M r θ := by
  classical
  -- 1) Contract first index
  rw [Riemann_contract_first]
  -- 2) Unfold exactly once
  unfold RiemannUp
  -- 3) Kill static and axisymmetric derivatives
  simp only [dCoord_t, dCoord_φ]
  -- 4) Apply the row lemma
  rw [row_tφtφ]
  -- 5) Algebra
  ring

/-- For the `rφrφ` component: compute the λ-sum in `RiemannUp` by enumeration. -/
@[simp] lemma row_rφrφ (M r θ : ℝ) :
  sumIdx (fun lam =>
      Γtot M r θ Idx.r Idx.r lam * Γtot M r θ lam Idx.φ Idx.φ
    - Γtot M r θ Idx.r Idx.φ lam * Γtot M r θ lam Idx.r Idx.φ)
  = Γ_r_rr M r * Γ_r_φφ M r θ - Γ_φ_rφ r * Γ_r_φφ M r θ := by
  classical
  have ht : (Γtot M r θ Idx.r Idx.r Idx.t * Γtot M r θ Idx.t Idx.φ Idx.φ
           - Γtot M r θ Idx.r Idx.φ Idx.t * Γtot M r θ Idx.t Idx.r Idx.φ) = 0 := by
    simp only [Γtot]; simp
  have hr : (Γtot M r θ Idx.r Idx.r Idx.r * Γtot M r θ Idx.r Idx.φ Idx.φ
           - Γtot M r θ Idx.r Idx.φ Idx.r * Γtot M r θ Idx.r Idx.r Idx.φ)
           = Γ_r_rr M r * Γ_r_φφ M r θ := by
    simp only [Γtot]; simp
  have hθ : (Γtot M r θ Idx.r Idx.r Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
           - Γtot M r θ Idx.r Idx.φ Idx.θ * Γtot M r θ Idx.θ Idx.r Idx.φ) = 0 := by
    simp only [Γtot]; simp
  have hφ : (Γtot M r θ Idx.r Idx.r Idx.φ * Γtot M r θ Idx.φ Idx.φ Idx.φ
           - Γtot M r θ Idx.r Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.r Idx.φ)
           = - Γ_φ_rφ r * Γ_r_φφ M r θ := by
    simp [Γtot, Γ_φ_rφ]; ring
  -- put the four cases together
  simp only [sumIdx_expand]
  rw [ht, hr, hθ, hφ]
  ring

/-- Canonical reduction for `R_{r φ r φ}`.  Axisymmetry kills all `∂_φ`-terms. -/
lemma Riemann_rφrφ_reduce (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.r Idx.φ
    = g M Idx.r Idx.r r θ * (dCoord Idx.r (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ
                              - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.r Idx.r Idx.φ) r θ
                              + Γ_r_rr M r * Γ_r_φφ M r θ
                              - Γ_φ_rφ r * Γ_r_φφ M r θ) := by
  classical
  -- 1) Contract first index
  rw [Riemann_contract_first]
  -- 2) Unfold exactly once
  unfold RiemannUp
  -- 3) Expand dCoord_r and kill dCoord_φ
  simp only [dCoord_r, dCoord_φ]
  -- 4) Apply the row lemma
  rw [row_rφrφ]
  -- 5) Algebra
  ring

/-- Helper: collapse a single index sum using metric diagonality -/
@[simp] lemma collapse1 (M r θ : ℝ) (a : Idx) (X : Idx → ℝ) :
  sumIdx (fun α => gInv M a α r θ * X α) = gInv M a a r θ * X a := by
  classical
  cases a <;> simp [sumIdx_expand, gInv]

/-- Helper lemma for pulling a constant factor out of sumIdx. -/
lemma sumIdx_mul_left' (c : ℝ) (f : Idx → ℝ) :
    sumIdx (fun i => c * f i) = c * sumIdx f := by
  classical
  simp only [sumIdx_expand]
  ring

/-- Helper lemma for pulling a constant factor out of sumIdx2. -/
lemma sumIdx2_mul_left' (c : ℝ) (f : Idx → Idx → ℝ) :
    sumIdx2 (fun i j => c * f i j) = c * sumIdx2 f := by
  simp only [sumIdx2, sumIdx_mul_left']

-- The _mul_left' versions already exist and work fine

/-- Right-sided single-index collapse (pairs with existing `collapse1`). -/
@[simp] lemma collapse1_right (M r θ : ℝ) (a : Idx) (X : Idx → ℝ) :
  sumIdx (fun α => X α * gInv M a α r θ) = X a * gInv M a a r θ := by
  classical
  cases a <;> simp [sumIdx_expand, gInv, mul_comm, mul_left_comm, mul_assoc]

/-- Two-index raiser: collapses `(α,β)` in one go using the diagonal `gInv`. -/
lemma raise2_T (M r θ : ℝ) (a b : Idx) (T : Idx → Idx → ℝ) :
  sumIdx2 (fun α β => gInv M a α r θ * gInv M b β r θ * T α β)
    = gInv M a a r θ * gInv M b b r θ * T a b := by
  classical
  -- Direct case analysis on all 16 combinations
  cases a <;> cases b <;>
    simp only [sumIdx2, sumIdx_expand, gInv] <;>
    simp <;>
    ring

/-- Four-index raiser: compose the two-index raiser twice. -/
lemma raise4_R
    (M r θ : ℝ) (a b c d : Idx) :
  (sumIdx2 fun α β =>
    sumIdx2 fun γ δ =>
      gInv M a α r θ * gInv M b β r θ
    * gInv M c γ r θ * gInv M d δ r θ
    * Riemann M r θ α β γ δ)
  =
  (gInv M a a r θ * gInv M b b r θ
 * gInv M c c r θ * gInv M d d r θ)
  * Riemann M r θ a b c d := by
  classical
  -- Transform to nested application of raise2_T
  calc (sumIdx2 fun α β => sumIdx2 fun γ δ =>
          gInv M a α r θ * gInv M b β r θ * gInv M c γ r θ * gInv M d δ r θ * Riemann M r θ α β γ δ)
      = sumIdx2 (fun α β => gInv M a α r θ * gInv M b β r θ *
          sumIdx2 (fun γ δ => gInv M c γ r θ * gInv M d δ r θ * Riemann M r θ α β γ δ)) := by
        congr; ext α β; simp only [← sumIdx2_mul_left']; congr; ext; ring
    _ = sumIdx2 (fun α β => gInv M a α r θ * gInv M b β r θ *
          (gInv M c c r θ * gInv M d d r θ * Riemann M r θ α β c d)) := by
        congr; ext α β; rw [raise2_T]
    _ = sumIdx2 (fun α β => gInv M a α r θ * gInv M b β r θ * gInv M c c r θ * gInv M d d r θ * Riemann M r θ α β c d) := by
        congr; ext; ring
    _ = gInv M c c r θ * gInv M d d r θ * sumIdx2 (fun α β => gInv M a α r θ * gInv M b β r θ * Riemann M r θ α β c d) := by
        rw [← sumIdx2_mul_left']; congr; ext; ring
    _ = gInv M c c r θ * gInv M d d r θ * (gInv M a a r θ * gInv M b b r θ * Riemann M r θ a b c d) := by
        congr; rw [raise2_T]
    _ = gInv M a a r θ * gInv M b b r θ * gInv M c c r θ * gInv M d d r θ * Riemann M r θ a b c d := by
        ring

end Schwarzschild
end Papers.P5_GeneralRelativity