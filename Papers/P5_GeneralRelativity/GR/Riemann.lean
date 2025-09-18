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
@[simp] lemma Riemann_swap_c_d
    (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d = - Riemann M r θ a b d c := by
  -- Use the previous lemma through the lowering definition
  sorry

/-- If the first index is lowered with a diagonal `g`, in many cases only `ρ = a`
    contributes in the sum. This lemma doesn't assert diagonality; it's a
    convenient rewriting point for later `simp [g]`. -/
@[simp] lemma Riemann_lower_def (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d
    = sumIdx (fun ρ => g M a ρ r θ * RiemannUp M r θ ρ b c d) := rfl

/-- Canonical reduction for `R_{rθrθ}`. Keeps derivatives symbolic, just like your Ricci pipeline. -/
@[simp] lemma Riemann_rθrθ_reduce (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.r Idx.θ
    =
      deriv (fun s => Γ_r_θθ M s) r
    - dCoord Idx.θ (fun r θ => Γtot M r θ Idx.r Idx.r Idx.θ) r θ
    + Γ_r_rr M r * Γ_r_θθ M r
    - (Γ_θ_rθ r) * (Γ_r_θθ M r) := by
  classical
  -- Expand + kill zero entries; keep derivatives symbolic
  unfold Riemann RiemannUp
  -- TODO: Complete this reduction using existing Γtot patterns
  sorry

/-- Canonical reduction for `R_{θφθφ}`. Again, fully structural; no numeric evaluation. -/
@[simp] lemma Riemann_θφθφ_reduce (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.φ
    =
      deriv (fun t => Γ_θ_φφ t) θ
    - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.θ Idx.θ Idx.φ) r θ
    + (Γ_θ_rθ r) * (Γ_r_φφ M r θ)
    - (Γ_θ_φφ θ) * (Γ_φ_θφ θ) := by
  classical
  unfold Riemann RiemannUp
  -- φ-derivatives drop out by axisymmetry (`dCoord φ … = 0`) via `[simp]`
  -- TODO: Complete this reduction using existing Γtot patterns
  sorry

end Schwarzschild
end Papers.P5_GeneralRelativity