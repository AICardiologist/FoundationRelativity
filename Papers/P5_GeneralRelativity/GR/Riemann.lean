-- Papers/P5_GeneralRelativity/GR/Riemann.lean
import Papers.P5_GeneralRelativity.GR.Schwarzschild
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace Papers.P5_GeneralRelativity
open Papers.P5_GeneralRelativity
open Real
open Filter Topology
open scoped BigOperators

namespace Schwarzschild
open Idx

/-! ## Exterior Domain Definition -/

/-- The exterior domain: region where r > 2M, ensuring r ≠ 0 and f(r) ≠ 0. -/
structure Exterior (M r θ : ℝ) : Prop where
  hM : 0 < M
  hr_ex : 2 * M < r

namespace Exterior

lemma r_ne_zero {M r θ : ℝ} (h : Exterior M r θ) : r ≠ 0 :=
  r_ne_zero_of_exterior M r h.hM h.hr_ex

lemma f_ne_zero {M r θ : ℝ} (h : Exterior M r θ) : f M r ≠ 0 :=
  ne_of_gt (f_pos_of_hr M r h.hM h.hr_ex)

/-- The Exterior domain (for fixed M > 0) forms an open set in ℝ × ℝ.

    TOPOLOGICAL INFRASTRUCTURE (Level 3 De-Axiomatization):
    This lemma establishes that {(r,θ) | r > 2M} is open in the product topology.

    **Significance:** Proving Exterior is open would allow us to:
    1. Show nabla_g = 0 holds in a neighborhood of any Exterior point
    2. Conclude derivatives of nabla_g are zero (derivative of constant = 0)
    3. Eliminate AX_nabla_g_zero from Riemann_swap_a_b

    However, this requires additional infrastructure (deriv of locally constant function)
    which is deferred. The critical path (R_μν = 0) doesn't need this lemma.
-/
lemma isOpen_exterior_set (M : ℝ) (hM : 0 < M) :
    IsOpen {p : ℝ × ℝ | 2 * M < p.1} := by
  -- The set {(r,θ) | 2M < r} is the preimage of (2M, ∞) under projection π₁
  have : {p : ℝ × ℝ | 2 * M < p.1} = Prod.fst ⁻¹' Set.Ioi (2 * M) := by
    ext p
    simp [Set.mem_preimage, Set.mem_Ioi]
  rw [this]
  -- Projection is continuous and (2M, ∞) is open in ℝ
  exact IsOpen.preimage continuous_fst isOpen_Ioi

/-- **PRIORITY 1.1: General topology helper for Level 3**

    If a function f equals zero on an open set U containing x,
    then its derivative at x is zero.

    This is the key lemma for eliminating AX_nabla_g_zero.

    **Strategy (from professor):**
    1. U is a neighborhood of x (since U is open and x ∈ U)
    2. f is eventually equal to the zero function near x
    3. The derivative of f equals the derivative of the zero function
    4. The derivative of a constant is zero
-/
lemma deriv_zero_of_locally_zero {f : ℝ → ℝ} {x : ℝ} {U : Set ℝ}
    (hU_open : IsOpen U) (hx : x ∈ U) (hf_zero : ∀ y ∈ U, f y = 0) :
    deriv f x = 0 := by
  -- Step 1: U is a neighborhood of x
  have h_nhds : U ∈ 𝓝 x := hU_open.mem_nhds hx

  -- Step 2: f is eventually equal to the zero function near x
  have h_eventually_eq_zero : f =ᶠ[𝓝 x] (fun _ => 0) := by
    apply eventually_of_mem h_nhds
    intro y hy
    simp [hf_zero y hy]

  -- Step 3: The derivative of f equals the derivative of the zero function
  -- Use Filter.EventuallyEq.deriv_eq
  rw [h_eventually_eq_zero.deriv_eq]

  -- Step 4: The derivative of a constant is zero
  simp [deriv_const]

end Exterior

-- -------------- BEGIN: adapter + simp setup for Riemann.lean --------------

-- Temporarily disabled SimpSetup to fix attribute ordering
/-
section SimpSetup
  -- Always useful:
  attribute [local simp] dCoord_t dCoord_r dCoord_θ dCoord_φ deriv_const
  attribute [local simp] deriv_pow_two_at deriv_sin_sq_at

  -- Abstract-sum algebra:
  attribute [local simp] sumIdx_expand sumIdx2_expand

  -- Nonzero Γtot projections:
  attribute [local simp]
    Γtot_t_tr Γtot_t_rt Γtot_r_tt Γtot_r_rr Γtot_r_θθ Γtot_r_φφ
    Γtot_θ_rθ Γtot_θ_θr Γtot_φ_rφ Γtot_φ_φr Γtot_θ_φφ Γtot_φ_θφ Γtot_φ_φθ

  -- Zero Γtot projections frequently used:
  attribute [local simp]
    Γtot_t_θt_zero Γtot_t_θr_zero Γtot_r_θr_zero Γtot_θ_θθ_zero
end SimpSetup
-/

-- Adapter layer:
-- If Riemann.lean refers to projection names WITHOUT the `_zero` suffix,
-- provide local wrappers that forward to your `_zero` lemmas.

-- t-row: purely diagonal zeros that Riemann.lean may reference without `_zero`.
@[simp] lemma Γtot_t_tt (M r θ : ℝ) : Γtot M r θ Idx.t Idx.t Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_rr (M r θ : ℝ) : Γtot M r θ Idx.t Idx.r Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_θθ (M r θ : ℝ) : Γtot M r θ Idx.t Idx.θ Idx.θ = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_φφ (M r θ : ℝ) : Γtot M r θ Idx.t Idx.φ Idx.φ = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_rθ (M r θ : ℝ) : Γtot M r θ Idx.t Idx.r Idx.θ = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_θr (M r θ : ℝ) : Γtot M r θ Idx.t Idx.θ Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_rφ (M r θ : ℝ) : Γtot M r θ Idx.t Idx.r Idx.φ = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_φr (M r θ : ℝ) : Γtot M r θ Idx.t Idx.φ Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_θφ (M r θ : ℝ) : Γtot M r θ Idx.t Idx.θ Idx.φ = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_φθ (M r θ : ℝ) : Γtot M r θ Idx.t Idx.φ Idx.θ = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_tθ (M r θ : ℝ) : Γtot M r θ Idx.t Idx.t Idx.θ = 0 := by simp [Γtot]
@[simp] lemma Γtot_t_θt (M r θ : ℝ) : Γtot M r θ Idx.t Idx.θ Idx.t = 0 := by simp [Γtot]

-- r-row missing combinations:
@[simp] lemma Γtot_r_tr (M r θ : ℝ) : Γtot M r θ Idx.r Idx.t Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_r_rt (M r θ : ℝ) : Γtot M r θ Idx.r Idx.r Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_r_tθ (M r θ : ℝ) : Γtot M r θ Idx.r Idx.t Idx.θ = 0 := by simp [Γtot]
@[simp] lemma Γtot_r_θt (M r θ : ℝ) : Γtot M r θ Idx.r Idx.θ Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_r_tφ (M r θ : ℝ) : Γtot M r θ Idx.r Idx.t Idx.φ = 0 := by simp [Γtot]
@[simp] lemma Γtot_r_φt (M r θ : ℝ) : Γtot M r θ Idx.r Idx.φ Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_r_θφ (M r θ : ℝ) : Γtot M r θ Idx.r Idx.θ Idx.φ = 0 := by simp [Γtot]
@[simp] lemma Γtot_r_φθ (M r θ : ℝ) : Γtot M r θ Idx.r Idx.φ Idx.θ = 0 := by simp [Γtot]

-- θ-row missing combinations:
@[simp] lemma Γtot_θ_tt (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.t Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_rr (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.r Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_tr (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.t Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_rt (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.r Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_tφ (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.t Idx.φ = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_φt (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.φ Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_rφ (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.r Idx.φ = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_φr (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.φ Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_θθ (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.θ Idx.θ = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_tθ (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.t Idx.θ = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_θt (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.θ Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_θφ (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.θ Idx.φ = 0 := by simp [Γtot]
@[simp] lemma Γtot_θ_φθ (M r θ : ℝ) : Γtot M r θ Idx.θ Idx.φ Idx.θ = 0 := by simp [Γtot]

-- φ-row missing combinations:
@[simp] lemma Γtot_φ_tt (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.t Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_rr (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.r Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_tr (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.t Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_rt (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.r Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_tθ (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.t Idx.θ = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_θt (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.θ Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_tφ (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.t Idx.φ = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_φt (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.φ Idx.t = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_rθ (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.r Idx.θ = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_θr (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.θ Idx.r = 0 := by simp [Γtot]
@[simp] lemma Γtot_φ_θθ (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.θ Idx.θ = 0 := by simp [Γtot]
-- Removed duplicate: Γtot_φ_θφ is already defined in Schwarzschild.lean
@[simp] lemma Γtot_φ_φφ (M r θ : ℝ) : Γtot M r θ Idx.φ Idx.φ Idx.φ = 0 := by simp [Γtot]

-- -------------- END: adapter + simp setup for Riemann.lean ----------------

/-!
  # Riemann tensor (scaffold)

  We work at fixed `(M, r, θ)` and use the project's `Γtot` aggregator:
  `Γtot M r θ ρ μ ν` ≡ Γ^ρ_{μν}(r,θ) in Schwarzschild coordinates.

  The helper `dCoord μ F r θ` implements the coordinate derivative ∂_μ F
  for 2-argument fields F : ℝ → ℝ → ℝ, with only `r` and `θ` directions active.
  
  ## Current Status (Sprint 4 - Architecture Complete)
  
  Key Achievements:
  - ✅ Fixed `deriv_Γ_r_φφ_θ` using HasDerivAt approach (fully proven)
  - ✅ `bracket_θφ_rφ_scalar_zero` fully proven: direct cancellation
  - ✅ Scalar bracket architecture with CRITICAL index fix:
    * For `R_{rφ θφ}`: λ=θ term is `Γ^r_{θθ}·Γ^θ_{φφ}` (corrected from wrong index)
    * For `R_{θφ rφ}`: λ=θ term is `Γ^θ_{rθ}·Γ^θ_{φφ}`
  - ✅ Added covariant derivative framework for first-pair antisymmetry
  - ✅ Architecture successfully avoids `mul_eq_zero` disjunctions
  - ✅ Build is GREEN - all infrastructure complete
  
  Remaining sorries (7 total, all with complete documentation):
  - Covariant derivative framework (3): `nabla_g_zero`, `ricci_identity_on_g`, `Riemann_swap_a_b`
  - Scalar brackets (2): `bracket_rφ_θφ_scalar_zero` off-axis, `Riemann_first_equal_zero`
  - Vanishing lemmas (2): `R_rφ_θφ_zero`, `R_θφ_rφ_zero` (follow from brackets)
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

/-! ⚠️  FORMER QUARANTINED AXIOM - AXIOM CALIBRATION COMPLETE (2025-09-30)

**ELIMINATION PATH (COMPLETED ✅):**
1. ✅ Hypothesis-carrying infrastructure added (dCoord_add/sub/mul_of_diff)
2. ✅ Metric differentiability lemmas added (6 lemmas for g)
3. ✅ Christoffel differentiability lemmas added (10 rigorous proofs)
4. ✅ Made _of_diff versions @[simp] for automatic use
5. ✅ discharge_diff tactic auto-proves differentiability
6. ✅ Axiom ELIMINATED - All automatic reasoning axiom-free!

**FORMER AXIOM - NOW DELETED:**
The AX_differentiable_hack axiom that was here has been successfully eliminated.
All differentiability for **concrete functions** (metric, Christoffel) is now proven rigorously.

**CURRENT STATUS (Level 2.999):**
- ✅ Zero project axioms
- ✅ All `simp` automatic reasoning uses axiom-free `@[simp]` lemmas
- ⚠️ 3 sorries remain in legacy lemmas (lines 711, 717, 723) for arbitrary functions
  These are NOT axioms and are only used in explicit `rw` with abstract function variables.

**FOR AXIOM CALIBRATION:** Goal achieved - zero axioms in critical path,
all automatic reasoning axiom-free. The 3 sorries are in non-critical infrastructure
for abstract function manipulation (like dCoord linearity for arbitrary f, g).

**AUDIT:** Run `grep -n "SCAFFOLD_TODO" Riemann.lean` - should find only lines 711, 717, 723.
-/

/-! ### Differentiability Lemmas for Schwarzschild Components

These lemmas establish differentiability of the metric components and related functions,
eliminating the need for `AX_differentiable_hack` in critical proofs.
-/

/-- The function r ↦ r is differentiable everywhere. -/
lemma differentiableAt_id (r : ℝ) : DifferentiableAt ℝ id r :=
  differentiableAt_fun_id

/-- The function r ↦ r^n is differentiable everywhere for natural n. -/
lemma differentiableAt_pow (n : ℕ) (r : ℝ) : DifferentiableAt ℝ (fun x => x^n) r :=
  Differentiable.differentiableAt (differentiable_pow n)

/-- The function r ↦ 1/r is differentiable for r ≠ 0. -/
lemma differentiableAt_inv (r : ℝ) (hr : r ≠ 0) : DifferentiableAt ℝ (fun x => x⁻¹) r :=
  DifferentiableAt.inv differentiableAt_fun_id hr

/-- The Schwarzschild function f(r) = 1 - 2M/r is differentiable on Exterior (r > 2M). -/
lemma differentiableAt_f (M r : ℝ) (h_ext : Exterior M r 0) :
    DifferentiableAt ℝ (fun r' => f M r') r := by
  have hr_ne := Exterior.r_ne_zero h_ext
  simp only [f]
  -- f(r) = 1 - 2M/r = 1 - 2M * r⁻¹
  apply DifferentiableAt.sub
  · exact differentiableAt_const 1
  · apply DifferentiableAt.const_mul
    exact differentiableAt_inv r hr_ne

/-! ### Path A: C3 Smoothness via ContDiffAt Infrastructure

    Per Professor's Final MEMORANDUM (October 1, 2025):
    Use ContDiffAt to prove C^∞, then specialize to derive required differentiability.

    For f(r) = 1 - 2M/r: Prove C^∞ → C^2 → deriv f is C^1 → deriv f is DifferentiableAt
    For sin²θ: Prove C^∞ → C^2 → deriv (sin²θ) is C^1 → differentiable
-/

/-- Proving f(r) = 1 - 2M/r is C^∞ when r ≠ 0 -/
lemma contDiffAt_f (M r : ℝ) (hr : r ≠ 0) :
  ContDiffAt ℝ ⊤ (fun r' => f M r') r := by
  unfold f
  -- f(r) = 1 - (2 * M) / r
  apply ContDiffAt.sub
  { apply contDiffAt_const } -- 1
  { apply ContDiffAt.div
    { apply contDiffAt_const } -- 2*M
    { apply contDiffAt_id }    -- r
    { exact hr }
  }

/-- Proving sin²(θ) is C^∞ -/
lemma contDiffAt_sin_sq (θ : ℝ) :
  ContDiffAt ℝ ⊤ (fun θ' => Real.sin θ' ^ 2) θ := by
  apply ContDiffAt.pow
  -- Real.contDiff_sin proves sin is C^∞ everywhere.
  exact Real.contDiff_sin.contDiffAt

/-- sin θ is differentiable everywhere. -/
lemma differentiableAt_sin (θ : ℝ) : DifferentiableAt ℝ Real.sin θ :=
  Real.differentiableAt_sin

/-- cos θ is differentiable everywhere. -/
lemma differentiableAt_cos (θ : ℝ) : DifferentiableAt ℝ Real.cos θ :=
  Real.differentiableAt_cos

/-- sin²θ is differentiable everywhere. -/
lemma differentiableAt_sin_sq (θ : ℝ) : DifferentiableAt ℝ (fun θ' => (Real.sin θ')^2) θ :=
  DifferentiableAt.pow (Real.differentiableAt_sin) 2

/-! ### Helper Predicates for De-Axiomatization -/

/-- Helper predicate: f is differentiable at (r,θ) in the r-direction. -/
def DifferentiableAt_r (f : ℝ → ℝ → ℝ) (r θ : ℝ) : Prop :=
  DifferentiableAt ℝ (fun r' => f r' θ) r

/-- Helper predicate: f is differentiable at (r,θ) in the θ-direction. -/
def DifferentiableAt_θ (f : ℝ → ℝ → ℝ) (r θ : ℝ) : Prop :=
  DifferentiableAt ℝ (fun θ' => f r θ') θ

/-! ### Metric Component Differentiability -/

/-- g_tt(r) = -f(r) is differentiable in r-direction on Exterior. -/
lemma differentiableAt_g_tt_r (M r θ : ℝ) (h_ext : Exterior M r θ) :
    DifferentiableAt_r (fun r θ => g M Idx.t Idx.t r θ) r θ := by
  simp only [DifferentiableAt_r, g]
  -- Build Exterior M r 0 from h_ext : Exterior M r θ
  have h_ext_0 : Exterior M r 0 := ⟨h_ext.hM, h_ext.hr_ex⟩
  exact DifferentiableAt.neg (differentiableAt_f M r h_ext_0)

/-- g_rr(r) = 1/f(r) is differentiable in r-direction on Exterior. -/
lemma differentiableAt_g_rr_r (M r θ : ℝ) (h_ext : Exterior M r θ) :
    DifferentiableAt_r (fun r θ => g M Idx.r Idx.r r θ) r θ := by
  simp only [DifferentiableAt_r, g]
  -- Build Exterior M r 0 from h_ext : Exterior M r θ
  have h_ext_0 : Exterior M r 0 := ⟨h_ext.hM, h_ext.hr_ex⟩
  exact DifferentiableAt.inv (differentiableAt_f M r h_ext_0) (Exterior.f_ne_zero h_ext)

/-- g_θθ(r) = r² is differentiable in r-direction everywhere. -/
lemma differentiableAt_g_θθ_r (M r θ : ℝ) :
    DifferentiableAt_r (fun r θ => g M Idx.θ Idx.θ r θ) r θ := by
  simp only [DifferentiableAt_r, g]
  exact differentiableAt_pow 2 r

/-- g_φφ(r,θ) = r²sin²θ is differentiable in r-direction everywhere. -/
lemma differentiableAt_g_φφ_r (M r θ : ℝ) :
    DifferentiableAt_r (fun r θ => g M Idx.φ Idx.φ r θ) r θ := by
  simp only [DifferentiableAt_r, g]
  apply DifferentiableAt.mul
  · exact differentiableAt_pow 2 r
  · exact differentiableAt_const _

/-- g_φφ(r,θ) = r²sin²θ is differentiable in θ-direction everywhere. -/
lemma differentiableAt_g_φφ_θ (M r θ : ℝ) :
    DifferentiableAt_θ (fun r θ => g M Idx.φ Idx.φ r θ) r θ := by
  simp only [DifferentiableAt_θ, g]
  apply DifferentiableAt.mul
  · exact differentiableAt_const _
  · exact differentiableAt_sin_sq θ

/-! ### Christoffel Symbol Differentiability

Differentiability lemmas for all nonzero Christoffel symbol components.
These are needed to eliminate AX_differentiable_hack from Stage-1 Riemann computations.

NOTE: These lemmas are currently admitted with SCAFFOLD_TODO as placeholders. The Christoffel symbols
are explicit rational/algebraic/trigonometric functions, so differentiability is mathematically
obvious. Full proofs can be filled in if needed, but for now we prioritize getting the
infrastructure working.
-/

-- Γ^t_{tr} = M/(r²f(r)) - depends on r only
lemma differentiableAt_Γ_t_tr_r (M r : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt ℝ (fun r' => Γ_t_tr M r') r := by
  simp only [Γ_t_tr]
  -- Γ_t_tr M r = M / (r^2 * f M r)
  apply DifferentiableAt.div
  · -- M is constant
    exact differentiableAt_const M
  · -- r^2 * f M r is differentiable
    apply DifferentiableAt.mul
    · -- r^2 is differentiable
      exact differentiable_pow 2 |>.differentiableAt
    · -- f M r is differentiable
      -- f M r = 1 - 2*M/r
      show DifferentiableAt ℝ (fun r' => f M r') r
      unfold f
      apply DifferentiableAt.sub
      · exact differentiableAt_const 1
      · apply DifferentiableAt.div
        · exact differentiableAt_const (2 * M)
        · exact differentiableAt_id r
        · exact r_ne_zero_of_exterior M r hM hr
  · -- Denominator ≠ 0: r^2 * f M r ≠ 0
    have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
    have hf : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr)
    exact mul_ne_zero (pow_ne_zero 2 hr0) hf

-- Γ^r_{tt} = Mf(r)/r² - depends on r only
lemma differentiableAt_Γ_r_tt_r (M r : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt ℝ (fun r' => Γ_r_tt M r') r := by
  simp only [Γ_r_tt]
  -- Γ_r_tt M r = M * f M r / r^2
  apply DifferentiableAt.div
  · apply DifferentiableAt.mul
    · exact differentiableAt_const M
    · show DifferentiableAt ℝ (fun r' => f M r') r
      unfold f
      apply DifferentiableAt.sub
      · exact differentiableAt_const 1
      · apply DifferentiableAt.div
        · exact differentiableAt_const (2 * M)
        · exact differentiableAt_id r
        · exact r_ne_zero_of_exterior M r hM hr
  · exact differentiable_pow 2 |>.differentiableAt
  · exact pow_ne_zero 2 (r_ne_zero_of_exterior M r hM hr)

-- Γ^r_{rr} = -M/(r²f(r)) - depends on r only
lemma differentiableAt_Γ_r_rr_r (M r : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt ℝ (fun r' => Γ_r_rr M r') r := by
  simp only [Γ_r_rr, Γ_t_tr]
  -- Γ_r_rr M r = -M / (r^2 * f M r), which is -Γ_t_tr
  have h := differentiableAt_Γ_t_tr_r M r hM hr
  simpa using h.const_mul (-1)

-- Γ^r_{θθ} = -(r - 2M) - depends on r only
lemma differentiableAt_Γ_r_θθ_r (M r : ℝ) :
    DifferentiableAt ℝ (fun r' => Γ_r_θθ M r') r := by
  simp only [Γ_r_θθ]
  -- Γ_r_θθ M r = -(r - 2*M)
  apply DifferentiableAt.neg
  apply DifferentiableAt.sub
  · exact differentiableAt_id r
  · exact differentiableAt_const (2 * M)

-- Γ^r_{φφ} = -(r - 2M)sin²θ - depends on both r and θ
lemma differentiableAt_Γ_r_φφ_r (M r θ : ℝ) :
    DifferentiableAt ℝ (fun r' => Γ_r_φφ M r' θ) r := by
  simp only [Γ_r_φφ]
  -- Γ_r_φφ M r θ = -(r - 2*M) * sin²θ
  apply DifferentiableAt.mul
  · apply DifferentiableAt.neg
    apply DifferentiableAt.sub
    · exact differentiableAt_id r
    · exact differentiableAt_const (2 * M)
  · exact differentiableAt_const (Real.sin θ ^ 2)

lemma differentiableAt_Γ_r_φφ_θ (M r θ : ℝ) :
    DifferentiableAt ℝ (fun θ' => Γ_r_φφ M r θ') θ := by
  simp only [Γ_r_φφ]
  -- Γ_r_φφ M r θ = -(r - 2*M) * sin²θ
  apply DifferentiableAt.mul
  · exact differentiableAt_const (-(r - 2*M))
  · exact differentiableAt_sin_sq θ

-- Γ^θ_{rθ} = 1/r - depends on r only
lemma differentiableAt_Γ_θ_rθ_r (r : ℝ) (hr : r ≠ 0) :
    DifferentiableAt ℝ (fun r' => Γ_θ_rθ r') r := by
  simp only [Γ_θ_rθ]
  -- Γ_θ_rθ r = 1/r
  apply DifferentiableAt.div
  · exact differentiableAt_const 1
  · exact differentiableAt_id r
  · exact hr

-- Γ^θ_{φφ} = -cos(θ)sin(θ) - depends on θ only
lemma differentiableAt_Γ_θ_φφ_θ (θ : ℝ) :
    DifferentiableAt ℝ (fun θ' => Γ_θ_φφ θ') θ := by
  simp only [Γ_θ_φφ]
  -- Γ_θ_φφ θ = -(cos θ * sin θ)
  have h := (differentiableAt_cos θ).mul (differentiableAt_sin θ)
  simpa using h.const_mul (-1)

-- Γ^φ_{rφ} = 1/r - depends on r only
lemma differentiableAt_Γ_φ_rφ_r (r : ℝ) (hr : r ≠ 0) :
    DifferentiableAt ℝ (fun r' => Γ_φ_rφ r') r := by
  simp only [Γ_φ_rφ]
  -- Γ_φ_rφ r = 1/r (same as Γ_θ_rθ)
  exact differentiableAt_Γ_θ_rθ_r r hr

-- Γ^φ_{θφ} = cos(θ)/sin(θ) - depends on θ only
lemma differentiableAt_Γ_φ_θφ_θ (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    DifferentiableAt ℝ (fun θ' => Γ_φ_θφ θ') θ := by
  simp only [Γ_φ_θφ]
  -- Γ_φ_θφ θ = cos θ / sin θ
  apply DifferentiableAt.div
  · exact differentiableAt_cos θ
  · exact differentiableAt_sin θ
  · exact hθ

-- Now the composite Γtot differentiability lemmas
-- These handle the case-by-case structure of Γtot

lemma differentiableAt_Γtot_t_tr_r (M r θ : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt_r (fun r θ => Γtot M r θ Idx.t Idx.t Idx.r) r θ := by
  simp only [DifferentiableAt_r, Γtot_t_tr]
  exact differentiableAt_Γ_t_tr_r M r hM hr

lemma differentiableAt_Γtot_r_tt_r (M r θ : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt_r (fun r θ => Γtot M r θ Idx.r Idx.t Idx.t) r θ := by
  simp only [DifferentiableAt_r, Γtot_r_tt]
  exact differentiableAt_Γ_r_tt_r M r hM hr

lemma differentiableAt_Γtot_r_rr_r (M r θ : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt_r (fun r θ => Γtot M r θ Idx.r Idx.r Idx.r) r θ := by
  simp only [DifferentiableAt_r, Γtot_r_rr]
  exact differentiableAt_Γ_r_rr_r M r hM hr

lemma differentiableAt_Γtot_r_θθ_r (M r θ : ℝ) :
    DifferentiableAt_r (fun r θ => Γtot M r θ Idx.r Idx.θ Idx.θ) r θ := by
  simp only [DifferentiableAt_r, Γtot_r_θθ]
  exact differentiableAt_Γ_r_θθ_r M r

lemma differentiableAt_Γtot_r_φφ_r (M r θ : ℝ) :
    DifferentiableAt_r (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ := by
  simp only [DifferentiableAt_r, Γtot_r_φφ]
  exact differentiableAt_Γ_r_φφ_r M r θ

lemma differentiableAt_Γtot_r_φφ_θ (M r θ : ℝ) :
    DifferentiableAt_θ (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ := by
  simp only [DifferentiableAt_θ, Γtot_r_φφ]
  exact differentiableAt_Γ_r_φφ_θ M r θ

lemma differentiableAt_Γtot_θ_rθ_r (M r θ : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt_r (fun r θ => Γtot M r θ Idx.θ Idx.r Idx.θ) r θ := by
  simp only [DifferentiableAt_r, Γtot_θ_rθ]
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  exact differentiableAt_Γ_θ_rθ_r r hr0

lemma differentiableAt_Γtot_θ_φφ_θ (M r θ : ℝ) :
    DifferentiableAt_θ (fun r θ => Γtot M r θ Idx.θ Idx.φ Idx.φ) r θ := by
  simp only [DifferentiableAt_θ, Γtot_θ_φφ]
  exact differentiableAt_Γ_θ_φφ_θ θ

lemma differentiableAt_Γtot_φ_rφ_r (M r θ : ℝ) (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt_r (fun r θ => Γtot M r θ Idx.φ Idx.r Idx.φ) r θ := by
  simp only [DifferentiableAt_r, Γtot_φ_rφ]
  have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM hr
  exact differentiableAt_Γ_φ_rφ_r r hr0

lemma differentiableAt_Γtot_φ_θφ_θ (M r θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    DifferentiableAt_θ (fun r θ => Γtot M r θ Idx.φ Idx.θ Idx.φ) r θ := by
  simp only [DifferentiableAt_θ, Γtot_φ_θφ]
  exact differentiableAt_Γ_φ_θφ_θ θ hθ

/-! ### Differentiability for Γtot_nonzero (Dependent Type Version)

This is the key lemma that allows us to prove differentiability for Γtot with arbitrary indices,
by requiring a proof that the indices form a nonzero combination. The proof proceeds by case
analysis on the NonzeroChristoffel predicate, mapping each of the 13 cases to the corresponding
base differentiability lemma.
-/

lemma differentiableAt_Γtot_nonzero_r (M r θ : ℝ) (μ ν ρ : Idx) (h : NonzeroChristoffel μ ν ρ)
    (hM : 0 < M) (hr : 2 * M < r) :
    DifferentiableAt ℝ (fun r' => Γtot_nonzero M r' θ μ ν ρ h) r := by
  cases h
  case t_tr => exact differentiableAt_Γ_t_tr_r M r hM hr
  case t_rt => exact differentiableAt_Γ_t_tr_r M r hM hr
  case r_tt => exact differentiableAt_Γ_r_tt_r M r hM hr
  case r_rr => exact differentiableAt_Γ_r_rr_r M r hM hr
  case r_θθ => exact differentiableAt_Γ_r_θθ_r M r
  case r_φφ => exact differentiableAt_Γ_r_φφ_r M r θ
  case θ_rθ => exact differentiableAt_Γ_θ_rθ_r r (r_ne_zero_of_exterior M r hM hr)
  case θ_θr => exact differentiableAt_Γ_θ_rθ_r r (r_ne_zero_of_exterior M r hM hr)
  case θ_φφ => exact differentiableAt_const (Γ_θ_φφ θ)
  case φ_rφ => exact differentiableAt_Γ_φ_rφ_r r (r_ne_zero_of_exterior M r hM hr)
  case φ_φr => exact differentiableAt_Γ_φ_rφ_r r (r_ne_zero_of_exterior M r hM hr)
  case φ_θφ => exact differentiableAt_const (Γ_φ_θφ θ)
  case φ_φθ => exact differentiableAt_const (Γ_φ_θφ θ)

lemma differentiableAt_Γtot_nonzero_θ (M r θ : ℝ) (μ ν ρ : Idx) (h : NonzeroChristoffel μ ν ρ)
    (hθ : Real.sin θ ≠ 0) :
    DifferentiableAt ℝ (fun θ' => Γtot_nonzero M r θ' μ ν ρ h) θ := by
  cases h
  case t_tr => exact differentiableAt_const (Γ_t_tr M r)
  case t_rt => exact differentiableAt_const (Γ_t_tr M r)
  case r_tt => exact differentiableAt_const (Γ_r_tt M r)
  case r_rr => exact differentiableAt_const (Γ_r_rr M r)
  case r_θθ => exact differentiableAt_const (Γ_r_θθ M r)
  case r_φφ => exact differentiableAt_Γ_r_φφ_θ M r θ
  case θ_rθ => exact differentiableAt_const (Γ_θ_rθ r)
  case θ_θr => exact differentiableAt_const (Γ_θ_rθ r)
  case θ_φφ => exact differentiableAt_Γ_θ_φφ_θ θ
  case φ_rφ => exact differentiableAt_const (Γ_φ_rφ r)
  case φ_φr => exact differentiableAt_const (Γ_φ_rφ r)
  case φ_θφ => exact differentiableAt_Γ_φ_θφ_θ θ hθ
  case φ_φθ => exact differentiableAt_Γ_φ_θφ_θ θ hθ

/-! ### Automated Tactic for Differentiability Hypothesis Discharge

This tactic automatically discharges differentiability hypotheses for the `_of_diff` lemmas.
It tries two strategies:
1. Prove differentiability using concrete lemmas and combinators
2. Prove direction mismatch (e.g., μ ≠ Idx.r)
-/

/-- Robust, recursive tactic for discharging differentiability hypotheses.
    Prioritizes localization (P ∨ Q) before standard differentiability (P).
    Final version per Professor's MEMORANDUM (October 1, 2025). -/
syntax "discharge_diff" : tactic

macro_rules
| `(tactic| discharge_diff) =>
  `(tactic| (
      first
      -- Strategy 1: Localization (P ∨ Q)
      -- These strategies must be attempted BEFORE unfolding definitions.
      -- 1a. Assertive (Prove P)
      | { left; discharge_diff }
      -- 1b. Mismatch (Prove Q)
      | { right; simp [Idx.noConfusion] }
      -- 1c. Combinators (_of_cond)
      | { apply DifferentiableAt_r_add_of_cond <;> discharge_diff }
      | { apply DifferentiableAt_θ_add_of_cond <;> discharge_diff }
      | { apply DifferentiableAt_r_mul_of_cond <;> discharge_diff }
      | { apply DifferentiableAt_θ_mul_of_cond <;> discharge_diff }

      -- Strategy 2: Standard Differentiability (P)
      -- If localization fails, we unfold definitions and attempt standard proofs.
      | {
          (try { unfold DifferentiableAt_r DifferentiableAt_θ })
          first
          -- 2a. Combinators (Standard Mathlib)
          | { apply DifferentiableAt.add <;> discharge_diff }
          | { apply DifferentiableAt.mul <;> discharge_diff }
          | { apply DifferentiableAt.sub <;> discharge_diff }

          -- 2b. Base Facts (Explicit Application with hypothesis discharge)
          | { apply Γtot_differentiable_r <;> try assumption }
          | { apply Γtot_differentiable_θ <;> try assumption }
          | { apply g_differentiable_r <;> try assumption }
          | { apply g_differentiable_θ <;> try assumption }
          | { apply ContractionC_differentiable_r <;> try assumption }
          | { apply ContractionC_differentiable_θ <;> try assumption }
          -- Add C3 facts here when Path A is complete:
          | { apply dCoord_g_differentiable_r <;> try assumption }
          | { apply dCoord_g_differentiable_θ <;> try assumption }

          -- 2c. Fallback
          | { simp only [differentiableAt_const] }
          | assumption
        }
  ))

/-! ### Hypothesis-Carrying `dCoord` Infrastructure (De-Axiomatization)

The following lemmas provide rigorous versions of dCoord linearity rules with explicit
differentiability hypotheses. These replace the axiom-dependent versions for the critical path.

The helper predicates `DifferentiableAt_r` and `DifferentiableAt_θ` are defined above.
-/

/-- Linearity of dCoord over addition with explicit differentiability hypotheses. -/
@[simp] lemma dCoord_add_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
    dCoord μ (fun r θ => f r θ + g r θ) r θ =
    dCoord μ f r θ + dCoord μ g r θ := by
  cases μ
  case t => simp [dCoord]
  case r =>
    simp only [dCoord]
    apply deriv_add
    · exact hf_r.resolve_right (by simp)
    · exact hg_r.resolve_right (by simp)
  case θ =>
    simp only [dCoord]
    apply deriv_add
    · exact hf_θ.resolve_right (by simp)
    · exact hg_θ.resolve_right (by simp)
  case φ => simp [dCoord]

/-- Linearity of dCoord over subtraction with explicit differentiability hypotheses. -/
@[simp] lemma dCoord_sub_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
    dCoord μ (fun r θ => f r θ - g r θ) r θ =
    dCoord μ f r θ - dCoord μ g r θ := by
  cases μ
  case t => simp [dCoord]
  case r =>
    simp only [dCoord]
    apply deriv_sub
    · exact hf_r.resolve_right (by simp)
    · exact hg_r.resolve_right (by simp)
  case θ =>
    simp only [dCoord]
    apply deriv_sub
    · exact hf_θ.resolve_right (by simp)
    · exact hg_θ.resolve_right (by simp)
  case φ => simp [dCoord]

/-- Product rule for dCoord with explicit differentiability hypotheses. -/
@[simp] lemma dCoord_mul_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hf_r : DifferentiableAt_r f r θ ∨ μ ≠ Idx.r)
    (hg_r : DifferentiableAt_r g r θ ∨ μ ≠ Idx.r)
    (hf_θ : DifferentiableAt_θ f r θ ∨ μ ≠ Idx.θ)
    (hg_θ : DifferentiableAt_θ g r θ ∨ μ ≠ Idx.θ) :
    dCoord μ (fun r θ => f r θ * g r θ) r θ =
    dCoord μ f r θ * g r θ + f r θ * dCoord μ g r θ := by
  cases μ
  case t => simp [dCoord]
  case r =>
    simp only [dCoord]
    apply deriv_mul
    · exact hf_r.resolve_right (by simp)
    · exact hg_r.resolve_right (by simp)
  case θ =>
    simp only [dCoord]
    apply deriv_mul
    · exact hf_θ.resolve_right (by simp)
    · exact hg_θ.resolve_right (by simp)
  case φ => simp [dCoord]

/-! #### Calculus infrastructure for dCoord -/

/- Legacy lemmas dCoord_add/sub/mul DELETED per professor mandate (2025-10-01).
   These were unsound (used SCAFFOLD_TODO for arbitrary function differentiability).
   All uses refactored to use axiom-free _of_diff versions. -/

/-- Helper lemma to prove composite differentiability (r-direction) without case explosion.
    Uses the "Condition Localization" tactic pattern. -/
lemma DifferentiableAt_r_add_of_cond (A B : ℝ → ℝ → ℝ) (r θ : ℝ) (μ : Idx)
    (hA : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r)
    (hB : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r) :
    DifferentiableAt_r (fun r θ => A r θ + B r θ) r θ ∨ μ ≠ Idx.r := by
  -- Localize the condition
  by_cases h_coord : μ = Idx.r
  -- Case 1: μ = Idx.r. We must prove differentiability.
  · left
    -- Extract the differentiability fact by showing μ ≠ Idx.r is false
    have hA_diff := hA.resolve_right (by simp [h_coord])
    have hB_diff := hB.resolve_right (by simp [h_coord])
    -- Unfold definitions to ensure Mathlib's lemma unifies correctly
    unfold DifferentiableAt_r at *
    -- Apply the standard Mathlib lemma for sum differentiability
    exact DifferentiableAt.add hA_diff hB_diff
  -- Case 2: μ ≠ Idx.r. The goal is trivially true.
  · right
    exact h_coord

/-- Helper lemma for composite differentiability (θ-direction). -/
lemma DifferentiableAt_θ_add_of_cond (A B : ℝ → ℝ → ℝ) (r θ : ℝ) (μ : Idx)
    (hA : DifferentiableAt_θ A r θ ∨ μ ≠ Idx.θ)
    (hB : DifferentiableAt_θ B r θ ∨ μ ≠ Idx.θ) :
    DifferentiableAt_θ (fun r θ => A r θ + B r θ) r θ ∨ μ ≠ Idx.θ := by
  by_cases h_coord : μ = Idx.θ
  · left
    have hA_diff := hA.resolve_right (by simp [h_coord])
    have hB_diff := hB.resolve_right (by simp [h_coord])
    unfold DifferentiableAt_θ at *
    exact DifferentiableAt.add hA_diff hB_diff
  · right
    exact h_coord

/-- Push `dCoord` across a 4-term sum (refactored to use _of_diff). -/
lemma dCoord_add4 (μ : Idx) (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hA_r : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r)
    (hB_r : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r)
    (hC_r : DifferentiableAt_r C r θ ∨ μ ≠ Idx.r)
    (hD_r : DifferentiableAt_r D r θ ∨ μ ≠ Idx.r)
    (hA_θ : DifferentiableAt_θ A r θ ∨ μ ≠ Idx.θ)
    (hB_θ : DifferentiableAt_θ B r θ ∨ μ ≠ Idx.θ)
    (hC_θ : DifferentiableAt_θ C r θ ∨ μ ≠ Idx.θ)
    (hD_θ : DifferentiableAt_θ D r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ =
  dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ := by
  -- Expand: A + B + C + D associates as ((A + B) + C) + D
  -- Apply dCoord_add_of_diff three times with composed differentiability proofs
  have hab_r := DifferentiableAt_r_add_of_cond A B r θ μ hA_r hB_r
  have hab_θ := DifferentiableAt_θ_add_of_cond A B r θ μ hA_θ hB_θ
  have habc_r := DifferentiableAt_r_add_of_cond (fun r θ => A r θ + B r θ) C r θ μ hab_r hC_r
  have habc_θ := DifferentiableAt_θ_add_of_cond (fun r θ => A r θ + B r θ) C r θ μ hab_θ hC_θ
  rw [dCoord_add_of_diff μ (fun r θ => (A r θ + B r θ) + C r θ) D r θ habc_r hD_r habc_θ hD_θ]
  rw [dCoord_add_of_diff μ (fun r θ => A r θ + B r θ) C r θ hab_r hC_r hab_θ hC_θ]
  rw [dCoord_add_of_diff μ A B r θ hA_r hB_r hA_θ hB_θ]

/-- `dCoord_add4` specialized to a fully flattened 4-term sum (refactored). -/
lemma dCoord_add4_flat (μ : Idx) (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ)
    (hA_r : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r)
    (hB_r : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r)
    (hC_r : DifferentiableAt_r C r θ ∨ μ ≠ Idx.r)
    (hD_r : DifferentiableAt_r D r θ ∨ μ ≠ Idx.r)
    (hA_θ : DifferentiableAt_θ A r θ ∨ μ ≠ Idx.θ)
    (hB_θ : DifferentiableAt_θ B r θ ∨ μ ≠ Idx.θ)
    (hC_θ : DifferentiableAt_θ C r θ ∨ μ ≠ Idx.θ)
    (hD_θ : DifferentiableAt_θ D r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ =
  dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ := by
  simpa [add_comm, add_left_comm, add_assoc] using
    dCoord_add4 μ A B C D r θ hA_r hB_r hC_r hD_r hA_θ hB_θ hC_θ hD_θ


/-- Distribution of `dCoord` over the abstract finite sum `sumIdx` (refactored). -/
@[simp] lemma dCoord_sumIdx (μ : Idx) (F : Idx → ℝ → ℝ → ℝ) (r θ : ℝ)
    (hF_r : ∀ i, DifferentiableAt_r (F i) r θ ∨ μ ≠ Idx.r)
    (hF_θ : ∀ i, DifferentiableAt_θ (F i) r θ ∨ μ ≠ Idx.θ) :
  dCoord μ (fun r θ => sumIdx (fun i => F i r θ)) r θ =
  sumIdx (fun i => dCoord μ (fun r θ => F i r θ) r θ) := by
  -- Expand sumIdx on both sides
  simp only [sumIdx_expand]
  -- Use dCoord_add4 with the helper lemmas
  rw [dCoord_add4]
  -- Discharge the 8 differentiability obligations
  · apply hF_r
  · apply hF_r
  · apply hF_r
  · apply hF_r
  · apply hF_θ
  · apply hF_θ
  · apply hF_θ
  · apply hF_θ

/-
-- === gInv activation note ===
-- Choose ONE domain strategy when enabling `gInv`:
--   (A) Local, hypothesis-gated lemmas:
--       State metric_inverse_id with assumptions `hr : r ≠ 0`, `hs : Real.sin θ ≠ 0`.
--       Keeps `gInv` total, lemmas are valid where denominators are nonzero.
--   (B) Chart-restricted sections:
--       `section Domain; variable (hr : r ≠ 0) (hs : Real.sin θ ≠ 0) ... end`
--       Clean simp behavior inside the chart; no global assumptions leak.
--
-- In either case, keep `[simp]` facts local to RHS sections.
-/

/-
-- === Metric inverse (ready to enable when domain/regularity choices are fixed) ===
-- Diagonal inverse for the usual Schwarzschild-like diagonal metric.
-- NOTE: you may want domain guards (r ≠ 0, sin θ ≠ 0) or work in a chart where those hold.

def gInv (M : ℝ) (μ ν : Idx) (r θ : ℝ) : ℝ :=
  match μ, ν with
  | Idx.t, Idx.t => 1 / (f M r)
  | Idx.r, Idx.r => f M r
  | Idx.θ, Idx.θ => 1 / (r * r)
  | Idx.φ, Idx.φ => 1 / (r * r * (Real.sin θ) * (Real.sin θ))
  | _, _         => 0

-- Metric-inverse identity (statement; choose both left and right identities if you like):
-- lemma metric_inverse_id_left (M : ℝ) :
--   ∀ (μ ν : Idx) (r θ : ℝ),
--     sumIdx (fun e => g M μ e r θ * gInv M e ν r θ) = if μ = ν then 1 else 0 := by
--   -- diagonal-by-diagonal case split; reduce off-diagonal terms by `simp [g, gInv]`
--   -- use standard algebraic identities, then handle domain conditions if needed
--   SCAFFOLD_TODO

-- lemma metric_inverse_id_right (M : ℝ) :
--   ∀ (μ ν : Idx) (r θ : ℝ),
--     sumIdx (fun e => gInv M μ e r θ * g M e ν r θ) = if μ = ν then 1 else 0 := by
--   SCAFFOLD_TODO

-- When `gInv` is enabled, these diagonality simp facts help a lot.
-- Keep them local (`local attribute [simp]`) in RHS sections if you prefer.

-- Off-diagonal vanishes:
-- @[simp] lemma gInv_offdiag (M : ℝ) (μ ν : Idx) (r θ : ℝ) :
--   μ ≠ ν → gInv M μ ν r θ = 0 := by
--   intro h
--   cases μ <;> cases ν <;> simp [gInv, h]  -- `simp` handles the non-matching branches

-- Diagonal cases (optional granular versions; helpful for `simp`):
-- @[simp] lemma gInv_tt (M r θ) : gInv M Idx.t Idx.t r θ = 1 / (f M r) := by simp [gInv]
-- @[simp] lemma gInv_rr (M r θ) : gInv M Idx.r Idx.r r θ = f M r       := by simp [gInv]
-- @[simp] lemma gInv_θθ (M r θ) : gInv M Idx.θ Idx.θ r θ = 1 / (r*r)   := by simp [gInv]
-- @[simp] lemma gInv_φφ (M r θ) : gInv M Idx.φ Idx.φ r θ = 1 / (r*r*(Real.sin θ)^2) := by
--   simp [gInv, sq, pow_two]
-/

/-- Derivative of function times constant. -/
@[simp] lemma deriv_mul_const (f : ℝ → ℝ) (c : ℝ) (x : ℝ) :
  deriv (fun y => f y * c) x = deriv f x * c := by
  simp [deriv_mul, deriv_const']

/-- Derivative of constant times function. -/
@[simp] lemma deriv_const_mul (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
  deriv (fun y => c * f y) x = c * deriv f x := by
  simp [deriv_mul, deriv_const']

/-! ### Targeted derivative calculators for Γ (robust to older Mathlib) -/

/-- General reciprocal derivative, via `HasDerivAt.inv` then `.deriv`. -/
@[simp] lemma deriv_inv_general
  (f : ℝ → ℝ) (x : ℝ) (hf₀ : f x ≠ 0) (hf : DifferentiableAt ℝ f x) :
  deriv (fun y => (f y)⁻¹) x = - deriv f x / (f x)^2 := by
  classical
  have hf' : HasDerivAt f (deriv f x) x := hf.hasDerivAt
  simpa using (hf'.inv hf₀).deriv

/-- `d/dr Γ^t_{tr}(r)` in closed rational form.
    `Γ^t_{tr}(r) = M / (r^2 * f(r))`. -/
@[simp] lemma deriv_Γ_t_tr_at
  (M r : ℝ) (hr : r ≠ 0) (hf : f M r ≠ 0) :
  deriv (fun s => Γ_t_tr M s) r
    = - (2 * M) * (r * f M r + M) / (r^4 * (f M r)^2) := by
  classical
  -- Let H(s) = s² · f(s). We first compute H′(r).
  have hd1 : DifferentiableAt ℝ (fun s => s^2) r :=
    (differentiable_pow 2).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun s => f M s) r :=
    (contDiffAt_f M r hr).differentiableAt le_top
  have hHdiff : DifferentiableAt ℝ (fun s => s^2 * f M s) r := hd1.mul hd2
  have hf' := f_hasDerivAt M r hr
  have h_prod :
      deriv (fun s => s^2 * f M s) r
        = (2 * r) * f M r + r^2 * (2 * M / r^2) := by
    have h1 : deriv (fun s => s^2) r = 2 * r := deriv_pow_two_at r
    have h2 : deriv (fun s => f M s) r = 2 * M / r^2 := by simpa using hf'.deriv
    have h_mul := deriv_mul hd1 hd2
    -- `deriv (g*h) = deriv g * h + g * deriv h`
    calc
      deriv (fun s => s^2 * f M s) r
          = deriv ((fun s => s^2) * (fun s => f M s)) r := by rfl
      _   = deriv (fun s => s^2) r * f M r + (r^2) * deriv (fun s => f M s) r := by
              simpa using h_mul
      _   = (2 * r) * f M r + r^2 * (2 * M / r^2) := by simpa [h1, h2]
  -- Derivative of H⁻¹ at r.
  have hden : r^2 * f M r ≠ 0 := mul_ne_zero (pow_ne_zero 2 hr) hf
  have h_inv :
      deriv (fun s => (s^2 * f M s)⁻¹) r
        = - deriv (fun s => s^2 * f M s) r / ((r^2 * f M r)^2) := by
    simpa using deriv_inv_general (fun s => s^2 * f M s) r hden hHdiff
  -- Rewrite Γ^t_{tr} and differentiate with `deriv_const_mul`.
  have hΓfun : (fun s => Γ_t_tr M s) = (fun s => M * ((s^2 * f M s)⁻¹)) := by
    funext s; simp [Γ_t_tr, div_eq_mul_inv]
  -- Final calc chain (one `field_simp` at the end).
  calc
    deriv (fun s => Γ_t_tr M s) r
        = deriv (fun s => M * ((s^2 * f M s)⁻¹)) r := by rw [hΓfun]
    _   = M * deriv (fun s => (s^2 * f M s)⁻¹) r := by
            rw [deriv_const_mul M (fun s => (s^2 * f M s)⁻¹) r]
    _   = M * ( - deriv (fun s => s^2 * f M s) r / ((r^2 * f M r)^2) ) := by
            rw [h_inv]
    _   = - M * ((2 * r) * f M r + r^2 * (2 * M / r^2)) / ((r^2 * f M r)^2) := by
            rw [h_prod]; ring
    _   = - (2 * M) * (r * f M r + M) / (r^4 * (f M r)^2) := by
            field_simp [hr, hf]

/-- `d/dr Γ^r_{rr}(r)` is the opposite sign of `d/dr Γ^t_{tr}(r)` since `Γ^r_{rr} = - Γ^t_{tr}`. -/
@[simp] lemma deriv_Γ_r_rr_at
  (M r : ℝ) (hr : r ≠ 0) (hf : f M r ≠ 0) :
  deriv (fun s => Γ_r_rr M s) r
    = (2 * M) * (r * f M r + M) / (r^4 * (f M r)^2) := by
  classical
  -- Pointwise identity: Γ^r_{rr} = - Γ^t_{tr}.
  have hΓfun : (fun s => Γ_r_rr M s) = (fun s => (-1) * Γ_t_tr M s) := by
    funext s; simp [Γ_r_rr, Γ_t_tr]; ring
  -- Reduce to the known derivative of Γ_t_tr.
  calc
    deriv (fun s => Γ_r_rr M s) r
        = deriv (fun s => (-1) * Γ_t_tr M s) r := by rw [hΓfun]
    _   = (-1) * deriv (fun s => Γ_t_tr M s) r := by
            rw [deriv_const_mul (-1) (fun s => Γ_t_tr M s) r]
    _   = (-1) * ( - (2 * M) * (r * f M r + M) / (r^4 * (f M r)^2) ) := by
            rw [deriv_Γ_t_tr_at M r hr hf]
    _   = (2 * M) * (r * f M r + M) / (r^4 * (f M r)^2) := by ring

/-- `d/dr Γ^r_{tt}(r)` in closed form. Γ^r_{tt} = M * (f / r^2) -/
@[simp] lemma deriv_Γ_r_tt_at
  (M r : ℝ) (hr : r ≠ 0) :
  deriv (fun s => Γ_r_tt M s) r
    = - (2 * M) * (r - 3 * M) / r^4 := by
  classical
  -- Write Γ^r_{tt} as M * (f / r^2) = M * ((s^2)⁻¹ * f)
  have hΓ :
      (fun s => Γ_r_tt M s)
        = (fun s => M * ((f M s) * ((s^2)⁻¹))) := by
    funext s; simp [Γ_r_tt, div_eq_mul_inv]; ring

  -- Derivatives we need
  have hdf : deriv (fun s => f M s) r = 2 * M / r^2 := by
    simpa using (f_hasDerivAt M r hr).deriv
  have hd_sq : DifferentiableAt ℝ (fun s => s^2) r :=
    (differentiable_pow 2).differentiableAt
  have hpow_ne : r^2 ≠ 0 := pow_ne_zero 2 hr
  have hd_inv_sq :
      deriv (fun s => (s^2)⁻¹) r = - (2 * r) / (r^2)^2 := by
    -- general reciprocal rule for v(s) = (s^2)⁻¹
    simpa using deriv_inv_general (fun s => s^2) r hpow_ne hd_sq

  -- Product rule for (f * (s^2)⁻¹), then constant M out
  have hprod :
      deriv (fun s => (f M s) * ((s^2)⁻¹)) r
        = (2 * M / r^2) * (r^2)⁻¹ + (f M r) * ( - (2 * r) / (r^2)^2 ) := by
    have hF  : DifferentiableAt ℝ (fun s => f M s) r :=
      (contDiffAt_f M r hr).differentiableAt le_top
    have hG  : DifferentiableAt ℝ (fun s => (s^2)⁻¹) r :=
      (hd_sq.inv hpow_ne)
    have h := deriv_mul hF hG
    simpa [hdf, hd_inv_sq] using h

  -- Put everything together and clean up
  calc
    deriv (fun s => Γ_r_tt M s) r
        = deriv (fun s => M * ((f M s) * ((s^2)⁻¹))) r := by
            simpa [hΓ]
    _   = M * deriv (fun s => (f M s) * ((s^2)⁻¹)) r := by
            simpa [deriv_const_mul]
    _   = M * ( (2 * M / r^2) * (r^2)⁻¹ + (f M r) * ( - (2 * r) / (r^2)^2 ) ) := by
            simpa [hprod]
    _   = - (2 * M) * (r - 3 * M) / r^4 := by
            -- Expand f = 1 - 2M/r and simplify
            simp only [f]
            field_simp [hr, pow_two]
            ring

/-- `d/dθ Γ^φ_{θφ}(θ) = - csc² θ` (i.e. `- 1/(sin θ)^2`). -/
@[simp] lemma deriv_Γ_φ_θφ_at
  (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
  deriv (fun t => Γ_φ_θφ t) θ = - 1 / (Real.sin θ)^2 := by
  classical
  -- csc′ via reciprocal rule
  have h_sin_diff : DifferentiableAt ℝ Real.sin θ := Real.differentiableAt_sin
  have h_inv :
      deriv (fun t => (Real.sin t)⁻¹) θ
        = - Real.cos θ / (Real.sin θ)^2 := by
    simpa using deriv_inv_general Real.sin θ hθ h_sin_diff
  have hcos' : deriv (fun t => Real.cos t) θ = - Real.sin θ := by
    simpa using (Real.hasDerivAt_cos θ).deriv
  -- product rule for cos * csc
  have hd_cos : DifferentiableAt ℝ (fun t => Real.cos t) θ :=
    Real.differentiable_cos.differentiableAt
  have hd_csc : DifferentiableAt ℝ (fun t => (Real.sin t)⁻¹) θ :=
    (Real.differentiable_sin.differentiableAt).inv hθ
  have h_mul :
      deriv (fun t => Real.cos t * (Real.sin t)⁻¹) θ
        = (- Real.sin θ) * (Real.sin θ)⁻¹
          + Real.cos θ * ( - Real.cos θ / (Real.sin θ)^2 ) := by
    have hm := deriv_mul hd_cos hd_csc
    simpa [hcos', h_inv] using hm
  -- cleanup: (-sin)*csc + cos*(-cos/sin^2) = - 1 / sin^2
  have h1 : (- Real.sin θ) * (Real.sin θ)⁻¹ = -1 := by
    field_simp [hθ]
  have h2 : Real.cos θ * ( - Real.cos θ / (Real.sin θ)^2 )
              = - (Real.cos θ)^2 / (Real.sin θ)^2 := by
    field_simp [hθ, pow_two]
  have trig : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := by
    simpa [pow_two] using Real.sin_sq_add_cos_sq θ
  calc
    deriv (fun t => Γ_φ_θφ t) θ
        = deriv (fun t => Real.cos t * (Real.sin t)⁻¹) θ := by
            simp [Γ_φ_θφ, div_eq_mul_inv]
    _   = (- Real.sin θ) * (Real.sin θ)⁻¹
          + Real.cos θ * ( - Real.cos θ / (Real.sin θ)^2 ) := h_mul
    _   = -1 - (Real.cos θ)^2 / (Real.sin θ)^2 := by
            rw [h1, h2]; ring
    _   = - ((Real.sin θ)^2 + (Real.cos θ)^2) / (Real.sin θ)^2 := by
            field_simp [hθ, pow_two]; ring
    _   = - 1 / (Real.sin θ)^2 := by
            simpa [trig, one_div]

/-- `d/dθ Γ^θ_{φφ}(θ) = sin² θ − cos² θ`. -/
@[simp] lemma deriv_Γ_θ_φφ_at (θ : ℝ) :
  deriv (fun t => Γ_θ_φφ t) θ = (Real.sin θ)^2 - (Real.cos θ)^2 := by
  classical
  have h1 : deriv (fun t => Real.sin t) θ = Real.cos θ := by
    simpa using (Real.hasDerivAt_sin θ).deriv
  have h2 : deriv (fun t => Real.cos t) θ = - Real.sin θ := by
    simpa using (Real.hasDerivAt_cos θ).deriv
  -- Differentiability data for product rule
  have hd_sin : DifferentiableAt ℝ (fun t => Real.sin t) θ :=
    Real.differentiable_sin.differentiableAt
  have hd_cos : DifferentiableAt ℝ (fun t => Real.cos t) θ :=
    Real.differentiable_cos.differentiableAt
  have hprod := deriv_mul hd_sin hd_cos
  -- `deriv(sin·cos) = cos·cos + sin·(-sin)`
  have hmul :
      deriv (fun t => Real.sin t * Real.cos t) θ
        = Real.cos θ * Real.cos θ + Real.sin θ * (- Real.sin θ) := by
    simpa [h1, h2, mul_comm, mul_left_comm, mul_assoc] using hprod
  -- Now use Γ_θ_φφ = -(sin·cos)
  calc
    deriv (fun t => Γ_θ_φφ t) θ
        = deriv (fun t => - (Real.sin t * Real.cos t)) θ := by
            simp [Γ_θ_φφ]
    _   = - deriv (fun t => Real.sin t * Real.cos t) θ := by simp
    _   = - (Real.cos θ * Real.cos θ + Real.sin θ * (- Real.sin θ)) := by
            rw [hmul]
    _   = (Real.sin θ)^2 - (Real.cos θ)^2 := by
            ring

/-- Off-axis product identity: `Γ^θ_{φφ}(θ) * Γ^φ_{θφ}(θ) = - (cos θ)^2`,
    valid under the natural hypothesis `sin θ ≠ 0` (away from the axis). -/
@[simp] lemma Γ_θ_φφ_mul_Γ_φ_θφ (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
  Γ_θ_φφ θ * Γ_φ_θφ θ = - (Real.cos θ)^2 := by
  classical
  -- `Γ_θ_φφ = -(sin θ)*(cos θ)`, `Γ_φ_θφ = (cos θ)/(sin θ)`
  -- Multiply and clear the denominator using `hθ : sin θ ≠ 0`.
  simp only [Γ_θ_φφ, Γ_φ_θφ, pow_two]
  field_simp [hθ]

/-- On the axis (`sin θ = 0`) the product is `0`.  Useful to split cases when needed. -/
lemma Γ_θ_φφ_mul_Γ_φ_θφ_onAxis (θ : ℝ) (hθ0 : Real.sin θ = 0) :
  Γ_θ_φφ θ * Γ_φ_θφ θ = 0 := by
  classical
  -- Here `Γ_θ_φφ θ = 0`, while `Γ_φ_θφ θ = cos θ / 0 = 0` in this snapshot (inv 0 = 0),
  -- so the product is definitionally `0`.
  simp [Γ_θ_φφ, Γ_φ_θφ, hθ0]

-- Minimal SimpSetup after dCoord definitions
section SimpSetup
  -- dCoord lemmas now defined above
  attribute [local simp] dCoord_t dCoord_r dCoord_θ dCoord_φ deriv_const

  -- From Schwarzschild (already @[simp] there)
  -- deriv_pow_two_at deriv_sin_sq_at are already simp in Schwarzschild

  -- Abstract-sum algebra from Schwarzschild
  attribute [local simp] sumIdx_expand sumIdx2_expand

  -- Nonzero Γtot projections from Schwarzschild
  attribute [local simp]
    Γtot_t_tr Γtot_t_rt Γtot_r_tt Γtot_r_rr Γtot_r_θθ Γtot_r_φφ
    Γtot_θ_rθ Γtot_θ_θr Γtot_φ_rφ Γtot_φ_φr Γtot_θ_φφ Γtot_φ_θφ Γtot_φ_φθ
end SimpSetup

/-- A convenient `dCoord` form of the θ-derivative of Γ^r_{φφ} for use inside `RiemannUp`. -/
@[simp] lemma dCoord_θ_Γ_r_φφ (M r θ : ℝ) :
  dCoord Idx.θ (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ
    = -2 * (r - 2*M) * Real.sin θ * Real.cos θ := by
  classical
  -- `dCoord_θ` is literally the θ-derivative of that slot.
  simp [dCoord_θ, Γtot, deriv_Γ_r_φφ_θ]

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

/-- Antisymmetry of `RiemannUp` in the last two indices. -/
lemma RiemannUp_swap_mu_nu
    (M r θ : ℝ) (ρ σ μ ν : Idx) :
  RiemannUp M r θ ρ σ μ ν = - RiemannUp M r θ ρ σ ν μ := by
  classical
  unfold RiemannUp
  -- Note: dCoord_add/sub removed - simp uses @[simp] _of_diff versions automatically
  simp [sumIdx, Finset.sum_sub_distrib,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]

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

/-! ### Covariant derivative framework for first-pair antisymmetry -/

/-- Covariant derivative of the metric: components `(∇_c g)_{ab}` in coordinates. -/
noncomputable def nabla_g (M r θ : ℝ) (c a b : Idx) : ℝ :=
  dCoord c (fun r θ => g M a b r θ) r θ
  - sumIdx (fun e => Γtot M r θ e c a * g M e b r θ)
  - sumIdx (fun e => Γtot M r θ e c b * g M a e r θ)

/-- Collapse `∑_e Γ^e_{x a} g_{e b}` using diagonality of `g`. -/
@[simp] lemma sumIdx_Γ_g_left
    (M r θ : ℝ) (x a b : Idx) :
  sumIdx (fun e => Γtot M r θ e x a * g M e b r θ)
    = Γtot M r θ b x a * g M b b r θ := by
  classical
  cases b <;>
    simp [sumIdx_expand, g, Γtot, mul_comm, mul_left_comm, mul_assoc]

/-- Collapse `∑_e Γ^e_{x b} g_{a e}` using diagonality of `g`. -/
@[simp] lemma sumIdx_Γ_g_right
    (M r θ : ℝ) (x a b : Idx) :
  sumIdx (fun e => Γtot M r θ e x b * g M a e r θ)
    = Γtot M r θ a x b * g M a a r θ := by
  classical
  cases a <;>
    simp [sumIdx_expand, g, Γtot, mul_comm, mul_left_comm, mul_assoc]

/-- Collapse a metric-weighted right contraction over the index `k`:
    `∑_k F k · g_{k b} = F b · g_{b b}` (diagonal metric). -/
@[simp] lemma sumIdx_mul_g_right
    (M : ℝ) (r θ : ℝ) (b : Idx) (F : Idx → ℝ) :
  sumIdx (fun k => F k * g M k b r θ) = F b * g M b b r θ := by
  classical
  cases b <;>
    simp [sumIdx_expand, g, mul_comm, mul_left_comm, mul_assoc]

/-- Collapse a metric-weighted left contraction over the index `k`:
    `∑_k g_{a k} · F k = g_{a a} · F a` (diagonal metric). -/
@[simp] lemma sumIdx_mul_g_left
    (M : ℝ) (r θ : ℝ) (a : Idx) (F : Idx → ℝ) :
  sumIdx (fun k => g M a k r θ * F k) = g M a a r θ * F a := by
  classical
  cases a <;>
    simp [sumIdx_expand, g, mul_comm, mul_left_comm, mul_assoc]

/-- With the two collapses, `nabla_g` has a tiny normal form. -/
@[simp] lemma nabla_g_shape (M r θ : ℝ) (x a b : Idx) :
  nabla_g M r θ x a b
    =
    dCoord x (fun r θ => g M a b r θ) r θ
    - Γtot M r θ b x a * g M b b r θ
    - Γtot M r θ a x b * g M a a r θ := by
  simp only [nabla_g, sumIdx_Γ_g_left, sumIdx_Γ_g_right]

/-! #### Calculus helpers and compatibility lemmas for nabla_g_zero -/

open Real

/-- Linearity of double sum under multiplication by a constant. -/
@[simp] lemma sumIdx2_mul_const (c : ℝ) (f : Idx → Idx → ℝ) :
  sumIdx2 (fun i j => c * f i j) = c * sumIdx2 f := by
  classical
  simp only [sumIdx2, sumIdx]  -- Use simp only instead of unfold
  simp_rw [Finset.mul_sum]


/-! #### Torsion-freeness of the Levi-Civita connection -/

/-- The Christoffel symbols are symmetric in their lower indices (torsion-free). -/
lemma Γtot_symmetry (M r θ : ℝ) (i j k : Idx) :
  Γtot M r θ i j k = Γtot M r θ i k j := by
  -- Optimized sequential splitting using projection lemmas
  cases i
  case t => cases j <;> cases k <;> simp only [Γtot_t_tr, Γtot_t_rt, Γtot_t_tt, Γtot_t_θθ, Γtot_t_φφ, Γtot_t_rθ, Γtot_t_θr, Γtot_t_rφ, Γtot_t_φr, Γtot_t_θφ, Γtot_t_φθ, Γtot]
  case r => cases j <;> cases k <;> simp only [Γtot_r_tt, Γtot_r_rr, Γtot_r_θθ, Γtot_r_φφ, Γtot_r_tr, Γtot_r_rt, Γtot_r_tθ, Γtot_r_θt, Γtot_r_tφ, Γtot_r_φt, Γtot_r_θφ, Γtot_r_φθ, Γtot]
  case θ => cases j <;> cases k <;> simp only [Γtot_θ_rθ, Γtot_θ_θr, Γtot_θ_φφ, Γtot_θ_tt, Γtot_θ_rr, Γtot_θ_tr, Γtot_θ_rt, Γtot_θ_tφ, Γtot_θ_φt, Γtot_θ_rφ, Γtot_θ_φr, Γtot_θ_θθ, Γtot_θ_tθ, Γtot_θ_θt, Γtot_θ_θφ, Γtot_θ_φθ, Γtot]
  case φ => cases j <;> cases k <;> simp only [Γtot_φ_rφ, Γtot_φ_φr, Γtot_φ_θφ, Γtot_φ_φθ, Γtot_φ_tt, Γtot_φ_rr, Γtot_φ_tr, Γtot_φ_rt, Γtot_φ_tθ, Γtot_φ_θt, Γtot_φ_rθ, Γtot_φ_θr, Γtot_φ_θθ, Γtot_φ_tφ, Γtot_φ_φt, Γtot_φ_φφ, Γtot]

/-! #### Algebraic compat equalities (no `f` calculus) -/

/-- ∂_r g_{θθ} = 2 Γ^θ_{r θ} g_{θθ}. -/
lemma compat_r_θθ (M r θ : ℝ) :
  dCoord Idx.r (fun r θ => g M Idx.θ Idx.θ r θ) r θ
    = 2 * Γtot M r θ Idx.θ Idx.r Idx.θ * g M Idx.θ Idx.θ r θ := by
  classical
  dsimp only [g]  -- KEY: Reduces g M Idx.θ Idx.θ x θ → x² under binder
  simp only [dCoord_r, Γtot_θ_rθ, Γ_θ_rθ, deriv_pow_two_at]
  field_simp

/-- ∂_r g_{φφ} = 2 Γ^φ_{r φ} g_{φφ}. -/
lemma compat_r_φφ (M r θ : ℝ) :
  dCoord Idx.r (fun r θ => g M Idx.φ Idx.φ r θ) r θ
    = 2 * Γtot M r θ Idx.φ Idx.r Idx.φ * g M Idx.φ Idx.φ r θ := by
  classical
  dsimp only [g]
  simp only [dCoord_r, Γtot_φ_rφ, Γ_φ_rφ, deriv_mul_const, deriv_pow_two_at]
  field_simp

/-- ∂_θ g_{φφ} = 2 Γ^φ_{θ φ} g_{φφ}. -/
lemma compat_θ_φφ (M r θ : ℝ) :
  dCoord Idx.θ (fun r θ => g M Idx.φ Idx.φ r θ) r θ
    = 2 * Γtot M r θ Idx.φ Idx.θ Idx.φ * g M Idx.φ Idx.φ r θ := by
  classical
  dsimp only [g]
  simp only [dCoord_θ, Γtot_φ_θφ, Γ_φ_θφ, deriv_const_mul, deriv_sin_sq_at]
  field_simp

/-! #### Targeted Exterior Domain Compatibility Lemmas

The following lemmas prove specific cases of metric compatibility on the Exterior Domain
with minimal, case-specific simp sets to avoid timeout. Each lemma uses the REPP pattern.
-/

/-- ∂_r g_{θθ} = Σ_k Γ^k_{rθ} g_{kθ} + Σ_k Γ^k_{rθ} g_{θk} on Exterior Domain.
    Refactored to match unified lemma structure. -/
@[simp] lemma compat_r_θθ_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.θ Idx.θ r θ) r θ =
    sumIdx (fun k => Γtot M r θ k Idx.r Idx.θ * g M k Idx.θ r θ) +
    sumIdx (fun k => Γtot M r θ k Idx.r Idx.θ * g M Idx.θ k r θ) := by
  classical
  -- 1. Preparation
  have hr_ne := Exterior.r_ne_zero h_ext
  -- 2. Normalize RHS Structure (expand sums and use diagonality)
  simp only [sumIdx_expand, g]
  -- RHS is now (Γ θ r θ * r²) + (Γ θ r θ * r²)
  -- 3. Simplify LHS
  simp only [dCoord_r, Γtot_θ_rθ, Γ_θ_rθ, deriv_pow_two_at]
  -- 4. Algebraic Closure
  field_simp [hr_ne, pow_two]
  ring

/-- ∂_r g_{φφ} = Σ_k Γ^k_{rφ} g_{kφ} + Σ_k Γ^k_{rφ} g_{φk} on Exterior Domain.
    Refactored to match unified lemma structure. -/
@[simp] lemma compat_r_φφ_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.φ Idx.φ r θ) r θ =
    sumIdx (fun k => Γtot M r θ k Idx.r Idx.φ * g M k Idx.φ r θ) +
    sumIdx (fun k => Γtot M r θ k Idx.r Idx.φ * g M Idx.φ k r θ) := by
  classical
  -- 1. Preparation
  have hr_ne := Exterior.r_ne_zero h_ext
  -- 2. Normalize RHS Structure (expand sums and use diagonality)
  simp only [sumIdx_expand, g]
  -- 3. Simplify LHS
  simp only [dCoord_r, Γtot_φ_rφ, Γ_φ_rφ, deriv_mul_const, deriv_pow_two_at]
  -- 4. Algebraic Closure
  field_simp [hr_ne, pow_two]
  ring

/-- ∂_θ g_{φφ} = Σ_k Γ^k_{θφ} g_{kφ} + Σ_k Γ^k_{θφ} g_{φk} on Exterior Domain.
    Refactored to match unified lemma structure. -/
@[simp] lemma compat_θ_φφ_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.θ (fun r θ => g M Idx.φ Idx.φ r θ) r θ =
    sumIdx (fun k => Γtot M r θ k Idx.θ Idx.φ * g M k Idx.φ r θ) +
    sumIdx (fun k => Γtot M r θ k Idx.θ Idx.φ * g M Idx.φ k r θ) := by
  classical
  -- 1. Preparation
  have hr_ne := Exterior.r_ne_zero h_ext
  -- 2. Normalize RHS Structure (expand sums and use diagonality)
  simp only [sumIdx_expand, g]
  -- 3. Simplify LHS
  simp only [dCoord_θ, Γtot_φ_θφ, Γ_φ_θφ, deriv_const_mul, deriv_sin_sq_at]
  -- 4. Algebraic Closure
  field_simp [hr_ne, pow_two, sq]
  ring

/-- ∂_r g_{tt} = Σ_k Γ^k_{rt} g_{kt} + Σ_k Γ^k_{rt} g_{tk} on the Exterior Domain.
    Refactored to match unified lemma structure. -/
@[simp] lemma compat_r_tt_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.t Idx.t r θ) r θ =
    sumIdx (fun k => Γtot M r θ k Idx.r Idx.t * g M k Idx.t r θ) +
    sumIdx (fun k => Γtot M r θ k Idx.r Idx.t * g M Idx.t k r θ) := by
  classical
  -- 1. Preparation
  have hr_ne := Exterior.r_ne_zero h_ext
  have hf_ne := Exterior.f_ne_zero h_ext
  -- 2. Normalize RHS Structure (CRITICAL STEP: expand sums and use diagonality)
  simp only [sumIdx_expand, g]
  -- RHS is now (Γ t r t * (-f)) + (Γ t r t * (-f))
  -- 3. Sequenced Simplification (LHS)
  have hf' := f_hasDerivAt M r hr_ne
  have h_deriv : deriv (fun s => -f M s) r = -(2 * M / r^2) := by
    simpa using (hf'.neg).deriv
  simp only [dCoord_r, Γtot_t_rt, Γ_t_tr]
  rw [h_deriv]
  -- 4. Algebraic Closure
  field_simp [hr_ne, hf_ne, pow_two, sq]
  ring

/-- ∂_r g_{rr} = Σ_k Γ^k_{rr} g_{kr} + Σ_k Γ^k_{rr} g_{rk} on the Exterior Domain.
    Refactored to match unified lemma structure. -/
@[simp] lemma compat_r_rr_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.r (fun r θ => g M Idx.r Idx.r r θ) r θ =
    sumIdx (fun k => Γtot M r θ k Idx.r Idx.r * g M k Idx.r r θ) +
    sumIdx (fun k => Γtot M r θ k Idx.r Idx.r * g M Idx.r k r θ) := by
  classical
  -- 1. Preparation
  have hr_ne := Exterior.r_ne_zero h_ext
  have hf_ne := Exterior.f_ne_zero h_ext
  -- 2. Normalize RHS Structure (expand sums and use diagonality)
  simp only [sumIdx_expand, g]
  -- 3. Sequenced Simplification (LHS)
  have hf' := f_hasDerivAt M r hr_ne
  have h_deriv : deriv (fun s => (f M s)⁻¹) r = -(2 * M / r^2) / (f M r)^2 := by
    simpa using (hf'.inv hf_ne).deriv
  simp only [dCoord_r, Γtot_r_rr, Γ_r_rr]
  rw [h_deriv]
  -- 4. Algebraic Closure
  field_simp [hr_ne, hf_ne, pow_two, sq]
  ring

/-! #### Off-Diagonal Cancellation Lemmas

Schwarzschild metric is diagonal, so g_tr = g_tθ = g_tφ = g_rθ = g_rφ = g_θφ = 0.
Therefore ∂_x g_ab = 0 for off-diagonal components, and the RHS Christoffel products
must cancel to 0.
-/

/-- Off-diagonal cancellation: ∂_t g_tr = 0 = RHS on Exterior Domain.
    Covers cases like x=t, a=t, b=r. -/
@[simp] lemma compat_t_tr_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.t (fun r θ => g M Idx.t Idx.r r θ) r θ =
    sumIdx (fun k => Γtot M r θ k Idx.t Idx.t * g M k Idx.r r θ) +
    sumIdx (fun k => Γtot M r θ k Idx.t Idx.r * g M Idx.t k r θ) := by
  classical
  have hr_ne := Exterior.r_ne_zero h_ext
  have hf_ne := Exterior.f_ne_zero h_ext
  -- LHS: deriv of g_tr = deriv of 0 = 0
  simp only [sumIdx_expand, g, dCoord_t, deriv_const]
  -- RHS: Christoffel cancellation
  simp only [Γtot_r_tt, Γ_r_tt, Γtot_t_tr, Γ_t_tr]
  field_simp [hr_ne, hf_ne]
  ring

/-- Off-diagonal cancellation: ∂_θ g_rθ = 0 = RHS on Exterior Domain. -/
@[simp] lemma compat_θ_rθ_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.θ (fun r θ => g M Idx.r Idx.θ r θ) r θ =
    sumIdx (fun k => Γtot M r θ k Idx.θ Idx.r * g M k Idx.θ r θ) +
    sumIdx (fun k => Γtot M r θ k Idx.θ Idx.θ * g M Idx.r k r θ) := by
  classical
  have hr_ne := Exterior.r_ne_zero h_ext
  have hf_ne := Exterior.f_ne_zero h_ext
  simp only [sumIdx_expand, g, dCoord_θ, deriv_const]
  simp only [Γtot_θ_rθ, Γ_θ_rθ, Γtot_r_θθ, Γ_r_θθ, Γtot_θ_θr, f]
  have h_sub_ne : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
  field_simp [hr_ne, hf_ne, h_sub_ne, pow_two]
  ring

/-- Off-diagonal cancellation: ∂_φ g_rφ = 0 = RHS on Exterior Domain. -/
@[simp] lemma compat_φ_rφ_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.φ (fun r θ => g M Idx.r Idx.φ r θ) r θ =
    sumIdx (fun k => Γtot M r θ k Idx.φ Idx.r * g M k Idx.φ r θ) +
    sumIdx (fun k => Γtot M r θ k Idx.φ Idx.φ * g M Idx.r k r θ) := by
  classical
  have hr_ne := Exterior.r_ne_zero h_ext
  have hf_ne := Exterior.f_ne_zero h_ext
  simp only [sumIdx_expand, g, dCoord_φ, deriv_const]
  simp only [Γtot_φ_rφ, Γ_φ_rφ, Γtot_r_φφ, Γ_r_φφ, Γtot_φ_φr, f]
  have h_sub_ne : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]
  field_simp [hr_ne, hf_ne, h_sub_ne, pow_two]
  ring

/-- Off-diagonal cancellation: ∂_φ g_θφ = 0 = RHS on Exterior Domain. -/
@[simp] lemma compat_φ_θφ_ext (M r θ : ℝ) (h_ext : Exterior M r θ) :
  dCoord Idx.φ (fun r θ => g M Idx.θ Idx.φ r θ) r θ =
    sumIdx (fun k => Γtot M r θ k Idx.φ Idx.θ * g M k Idx.φ r θ) +
    sumIdx (fun k => Γtot M r θ k Idx.φ Idx.φ * g M Idx.θ k r θ) := by
  classical
  have hr_ne := Exterior.r_ne_zero h_ext
  have hf_ne := Exterior.f_ne_zero h_ext
  simp only [sumIdx_expand, g, dCoord_φ, deriv_const]
  simp only [Γtot_φ_θφ, Γ_φ_θφ, Γtot_θ_φφ, Γ_θ_φφ, Γtot_φ_φθ, f]
  field_simp [hr_ne, hf_ne]
  ring

/-! #### Unified Exterior Domain Compatibility

The unconditional compatibility lemmas are mathematically unsound at the event horizon
(f(r)=0) due to Lean's convention that 1/0=0. The Christoffel symbols involving f(r)
in the denominator evaluate to 0, making the compatibility equations false.

We must restrict to the Exterior Domain where r > 2M, ensuring both r ≠ 0 and f(r) ≠ 0.

The following unified lemma proves all 64 cases of coordinate metric compatibility
via exhaustive case analysis, delegating to the targeted @[simp] lemmas above.
-/

/-- Unified coordinate derivative identity for the metric on the Exterior Domain.
    Proves ∂_x g_{ab} = Σ_k Γ^k_{xa} g_{kb} + Σ_k Γ^k_{xb} g_{ak} for all index combinations.
    This is the fundamental statement of metric compatibility (∇g = 0) in coordinate form.

    The proof delegates to the targeted @[simp] compat_*_ext lemmas above via contextual simp.
    This keeps the unified lemma small and fast - the heavy lifting is done once per case in
    the individual lemmas.
-/
lemma dCoord_g_via_compat_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ) := by
  classical
  cases x <;> cases a <;> cases b
  all_goals {
    -- Stage 1: Explicit Dispatch (Reliable Application)
    first
    -- Diagonal Cases
    | exact compat_r_tt_ext M r θ h_ext
    | exact compat_r_rr_ext M r θ h_ext
    | exact compat_r_θθ_ext M r θ h_ext
    | exact compat_r_φφ_ext M r θ h_ext
    | exact compat_θ_φφ_ext M r θ h_ext
    -- Off-Diagonal Cancellation Cases
    | exact compat_t_tr_ext M r θ h_ext
    | exact compat_θ_rθ_ext M r θ h_ext
    | exact compat_φ_rφ_ext M r θ h_ext
    | exact compat_φ_θφ_ext M r θ h_ext

    -- Stage 2: Automated Fallback (Trivial Zeros + Symmetry)
    | {
        -- Extract nonzero hypotheses for field operations
        have hr_ne := Exterior.r_ne_zero h_ext
        have hf_ne := Exterior.f_ne_zero h_ext
        have h_sub_ne : r - 2*M ≠ 0 := by linarith [h_ext.hr_ex]

        -- LHS expansion (dCoord x (g a b) -> 0)
        dsimp only [g] -- Simplify binder (e.g., g t θ -> 0)
        simp only [dCoord_t, dCoord_r, dCoord_θ, dCoord_φ, deriv_const]

        -- RHS expansion (sumIdx + sumIdx -> 0)
        simp only [sumIdx_expand, g]
        simp only [Γtot, Γ_t_tr, Γ_r_tt, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ, f]

        -- Final closure (0=0 or Christoffel cancellations)
        try { field_simp [hr_ne, hf_ne, h_sub_ne, pow_two]; ring }
      }
  }

/-- Metric compatibility (∇g = 0) on the Exterior Domain.
    This is the key identity that the unified dCoord_g_via_compat_ext proves. -/
lemma nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (c a b : Idx) :
  nabla_g M r θ c a b = 0 := by
  simp only [nabla_g]
  rw [dCoord_g_via_compat_ext M r θ h_ext]
  -- The terms cancel exactly by definition of nabla_g
  abel

/-- **PRIORITY 1.2-1.4: Derivative of nabla_g is zero on Exterior**

    The coordinate derivative of nabla_g is zero on the Exterior domain.

    This eliminates the need for AX_nabla_g_zero by using:
    - nabla_g_zero_ext: nabla_g = 0 on Exterior
    - Exterior.isOpen_exterior_set: Exterior is an open set
    - Exterior.deriv_zero_of_locally_zero: derivative of locally constant function is zero

    This lemma will replace AX_nabla_g_zero in Riemann_swap_a_b and dCoord_g_via_compat.
-/
lemma dCoord_nabla_g_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ)
    (μ c a b : Idx) :
    dCoord μ (fun r θ => nabla_g M r θ c a b) r θ = 0 := by
  cases μ

  -- ===== Case: μ = t (trivial) =====
  case t =>
    simp [dCoord_t]

  -- ===== Case: μ = φ (trivial) =====
  case φ =>
    simp [dCoord_φ]

  -- ===== Case: μ = r (requires topology) =====
  case r =>
    simp only [dCoord_r]
    -- Goal: deriv (fun r' => nabla_g M r' θ c a b) r = 0

    -- Define the open set U = {r' : ℝ | 2 * M < r'}
    let U := {r' : ℝ | 2 * M < r'}

    -- U is open (it's the open interval (2M, ∞))
    have hU_open : IsOpen U := isOpen_Ioi

    -- (r, θ) ∈ Exterior means r ∈ U
    have hx : r ∈ U := h_ext.hr_ex

    -- Apply the general lemma
    apply Exterior.deriv_zero_of_locally_zero hU_open hx

    -- Prove that nabla_g is zero on U
    intro r' hr'_ex
    -- For any r' > 2M, we can construct Exterior M r' θ
    have hM_pos := h_ext.hM
    have h_ext' : Exterior M r' θ := { hM := hM_pos, hr_ex := hr'_ex }
    -- nabla_g_zero_ext tells us nabla_g = 0 on Exterior
    exact nabla_g_zero_ext M r' θ h_ext' c a b

  -- ===== Case: μ = θ (requires topology) =====
  case θ =>
    simp only [dCoord_θ]
    -- Goal: deriv (fun θ' => nabla_g M r θ' c a b) θ = 0

    -- The Exterior condition is independent of θ (only depends on r > 2M)
    -- So nabla_g = 0 for ALL θ, which means U = ℝ (the universal set)
    let U : Set ℝ := Set.univ

    -- The universal set is always open
    have hU_open : IsOpen U := isOpen_univ

    -- θ is in the universal set
    have hx : θ ∈ U := Set.mem_univ θ

    -- Apply the general lemma
    apply Exterior.deriv_zero_of_locally_zero hU_open hx

    -- Prove that nabla_g is zero on U (for all θ')
    intro θ' _
    -- The Exterior hypothesis for (r, θ') can be constructed from h_ext
    -- because Exterior only depends on r > 2M and M > 0, not on θ
    have h_ext' : Exterior M r θ' := { hM := h_ext.hM, hr_ex := h_ext.hr_ex }
    exact nabla_g_zero_ext M r θ' h_ext' c a b

/-! #### Legacy Compatibility Lemmas (θ-φ sector only)

The following lemma remains valid unconditionally because it involves only r² and sin²θ terms,
with no f(r) dependence. This is kept for backwards compatibility with existing proofs.
-/

/-- Off-diagonal compatibility: Γ^θ_{φφ} g_{θθ} + Γ^φ_{θφ} g_{φφ} = 0 -/
@[simp] lemma compat_φ_θφ (M r θ : ℝ) :
  (Γtot M r θ Idx.θ Idx.φ Idx.φ * g M Idx.θ Idx.θ r θ) +
  (Γtot M r θ Idx.φ Idx.θ Idx.φ * g M Idx.φ Idx.φ r θ) = 0 := by
  classical
  simp only [Γtot_θ_φφ, Γtot_φ_θφ, Γ_θ_φφ, Γ_φ_θφ, g]
  by_cases hsin : Real.sin θ = 0
  · simp [hsin]
  field_simp [hsin, pow_two]
  ring

/-! ## ✅ AX_nabla_g_zero ELIMINATED (Level 3 Priority 1 - 2025-09-30)

The axiom AX_nabla_g_zero has been successfully eliminated from the codebase.

**Replacement:**
- Sound version: `nabla_g_zero_ext` (line 1055) with explicit Exterior hypothesis
- Uses topology infrastructure: `isOpen_exterior_set` from Level 2.5

**Downstream refactored:**
- `dCoord_g_via_compat` → `dCoord_g_via_compat_ext` (line 1017, from Level 2.5)
- `Riemann_swap_a_b` → `Riemann_swap_a_b_ext` (line 3195)
- `Riemann_sq_swap_a_b` → `Riemann_sq_swap_a_b_ext` (line 3220)
- `Riemann_first_equal_zero` → `Riemann_first_equal_zero_ext` (line 3228)

**Status:** Level 3 Priority 1 COMPLETE ✅
-/

-- Removed duplicate: sumIdx_sub is already defined in Schwarzschild.lean

/-! ### Structured proof infrastructure for the Ricci identity -/

noncomputable section RicciInfrastructure

/-- The contraction term C_dab = Σ_e (Γ^e_da g_eb + Γ^e_db g_ae).
    This represents the terms involving Christoffel symbols in ∇_d g_ab. -/
def ContractionC (M r θ : ℝ) (d a b : Idx) : ℝ :=
  sumIdx (fun e => Γtot M r θ e d a * g M e b r θ + Γtot M r θ e d b * g M a e r θ)

/-
-- Namespace wrapper to avoid naming conflicts when upstream definitions arrive
namespace DraftRiemann

/-- Riemann tensor with one index raised (mixed form).
    R^a_{bcd} = ∂_c Γ^a_{db} - ∂_d Γ^a_{cb} + Γ^a_{cλ} Γ^λ_{db} - Γ^a_{dλ} Γ^λ_{cb} -/
def RiemannUp (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  dCoord c (fun r θ => Γtot M r θ a d b) r θ
  - dCoord d (fun r θ => Γtot M r θ a c b) r θ
  + sumIdx (fun e => Γtot M r θ a c e * Γtot M r θ e d b)
  - sumIdx (fun e => Γtot M r θ a d e * Γtot M r θ e c b)

/-- Riemann tensor with all indices lowered.
    R_{abcd} = g_{aμ} R^μ_{bcd} -/
def Riemann (M r θ : ℝ) (a b c d : Idx) : ℝ :=
  sumIdx (fun μ => g M a μ r θ * RiemannUp M r θ μ b c d)

end DraftRiemann
-/

/-- Lemma relating nabla_g and ContractionC. By definition: ∇_d g_ab = ∂_d g_ab - C_dab. -/
lemma nabla_g_eq_dCoord_sub_C (M r θ : ℝ) (d a b : Idx) :
  nabla_g M r θ d a b = dCoord d (fun r θ => g M a b r θ) r θ - ContractionC M r θ d a b := by
  unfold nabla_g ContractionC
  simp [sumIdx_add]
  ring

/-- Helper: dCoord (partial derivative) of a constant function is zero. -/
lemma dCoord_const (μ : Idx) (c : ℝ) (r θ : ℝ) :
  dCoord μ (fun _ _ => c) r θ = 0 := by
  cases μ <;> simp [dCoord, deriv_const]

/-! ### Clairaut's Theorem for Schwarzschild Metric (Specialized Lemmas)

The general `dCoord_commute` for arbitrary functions requires C² smoothness infrastructure.
Instead, we prove commutativity specifically for the metric components via explicit calculation.
-/

/-- Mixed partial derivatives commute for the metric: ∂r∂θ g = ∂θ∂r g.
    Proven by explicit calculation for each metric component. -/
lemma dCoord_r_θ_commute_for_g (M r θ : ℝ) (a b : Idx) :
  dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ =
  dCoord Idx.θ (fun r θ => dCoord Idx.r (fun r θ => g M a b r θ) r θ) r θ := by
  cases a <;> cases b
  all_goals {
    -- 1. Binder Penetration + Expand Coordinate Derivatives
    simp only [g, dCoord_r, dCoord_θ]

    -- 2. Calculate Iterated Derivatives
    -- Most cases: g is constant in one variable → deriv = 0
    -- Non-trivial cases: g_θθ = r², g_φφ = r²sin²θ
    simp only [deriv_const, deriv_const_mul, deriv_mul_const,
               deriv_pow_two_at, deriv_sin_sq_at, deriv_mul]

    -- 3. Algebraic Closure
    try { ring }
  }

-- ========== C2 Smoothness Lemmas (Second-Order Differentiability) ==========
-- These are now MOVED to after C1 lemmas (after line 1722) to satisfy dependencies

/-
DEFERRED: C² smoothness lemmas (not needed for Ricci vacuum proof)

These lemmas establish second-order differentiability (∂(∂g)), which would be required
for higher-order curvature computations but are not on the critical path for proving
that the Schwarzschild spacetime is a vacuum solution (Ricci tensor = 0).

/-- The first derivative of g (wrt any coordinate) is itself differentiable in r (C2 smoothness).
    Note: This is about the partially-applied function (dCoord μ g) as a function of (r,θ). -/
@[simp]
lemma dCoord_g_differentiable_r (M r θ : ℝ) (μ a b : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  DifferentiableAt_r (dCoord μ (fun r θ => g M a b r θ)) r θ := by
  -- Hybrid Strategy: Case analysis FIRST, then apply appropriate strategy per case
  cases μ <;> cases a <;> cases b
  all_goals {
    -- Strategy dispatch based on case type:
    -- 1. Trivial cases (staticity, axisymmetry, off-diagonal): simp → constant derivative
    -- 2. Matching direction (e.g., ∂²_r g): Use C^k framework abstraction
    -- 3. Mismatching direction (e.g., ∂_r∂_θ g): Explicit calculation via separation of variables
    try {
      simp only [DifferentiableAt_r, dCoord_r, dCoord_t, dCoord_θ, dCoord_φ, g, deriv_const]
      exact differentiableAt_const 0
    }
  }

  -- Non-trivial cases require specific handling

  -- === μ=r cases (matching direction - use C^k abstraction) ===

  case r.t.t =>
    -- g_tt = -f(r), ∂_r g_tt = -f'(r)
    -- Goal: DifferentiableAt_r (deriv (fun s => -f M s))
    simp only [DifferentiableAt_r, dCoord_r, g]
    have h_neg_f_Cinf := contDiff_f.contDiffAt.neg
    exact h_neg_f_Cinf.differentiable_deriv_of_ge_two (by norm_num)

  case r.r.r =>
    -- g_rr = 1/f(r), ∂_r g_rr involves f'
    -- Goal: DifferentiableAt_r (deriv (fun s => (f M s)⁻¹))
    simp only [DifferentiableAt_r, dCoord_r, g]
    -- f is C^∞ on Exterior, f ≠ 0 on Exterior
    have hf_pos : 0 < f M r := f_pos M r hM h_ext
    have hf_nz : f M r ≠ 0 := ne_of_gt hf_pos
    have h_inv_f_Cinf := contDiff_f.contDiffAt.inv hf_nz
    exact h_inv_f_Cinf.differentiable_deriv_of_ge_two (by norm_num)

  case r.θ.θ =>
    -- g_θθ = r² (CORRECTED: matching direction)
    simp only [DifferentiableAt_r, dCoord_r, g]
    -- Use C^k framework: r² is C^∞
    have h_pow_Cinf := contDiffAt_pow 2
    exact h_pow_Cinf.differentiable_deriv_of_ge_two (by norm_num)

  case r.φ.φ =>
    -- g_φφ = r² sin²θ (CORRECTED)
    simp only [DifferentiableAt_r, dCoord_r, g]
    -- Use Ck framework (Matching direction).
    have h_pow_Cinf := contDiffAt_pow 2
    -- r² * const is C^∞.
    have h_gpp_Cinf := h_pow_Cinf.mul_const ((Real.sin θ)^2)
    exact h_gpp_Cinf.differentiable_deriv_of_ge_two (by norm_num)

  -- === μ=θ cases (mismatching direction for non-constant g - use explicit calculation) ===

  case θ.t.t | θ.r.r =>
    -- g_tt = -f(r), g_rr = 1/f(r) are constant in θ
    -- ∂_θ g = 0 → ∂_r (∂_θ g) = ∂_r 0 = 0 (differentiable)
    simp only [DifferentiableAt_r, dCoord_θ, g, deriv_const]
    exact differentiableAt_const 0

  case θ.θ.θ =>
    -- g_θθ = r² is constant in θ
    -- ∂_θ g_θθ = 0 → ∂_r (∂_θ g_θθ) = ∂_r 0 = 0 (differentiable)
    simp only [DifferentiableAt_r, dCoord_θ, g, deriv_const]
    exact differentiableAt_const 0

  case θ.φ.φ =>
    -- g_φφ = r² sin²θ separates: ∂_θ g_φφ = r² (2 sin θ cos θ)
    -- Goal: DifferentiableAt_r (r² · 2 sin θ cos θ) = differentiability of r² as function of r
    simp only [DifferentiableAt_r, dCoord_θ, g, deriv_const_mul, deriv_sin_sq_at]
    -- r² is differentiable in r
    exact DifferentiableAt.mul_const (differentiableAt_pow 2 r) (2 * Real.sin θ * Real.cos θ)

/-- The first derivative of g (wrt any coordinate) is itself differentiable in θ (C2 smoothness).
    Note: This is about the partially-applied function (dCoord μ g) as a function of (r,θ). -/
@[simp]
lemma dCoord_g_differentiable_θ (M r θ : ℝ) (μ a b : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  DifferentiableAt_θ (dCoord μ (fun r θ => g M a b r θ)) r θ := by
  -- Hybrid Strategy: Case analysis FIRST, then apply appropriate strategy per case
  cases μ <;> cases a <;> cases b
  all_goals {
    -- Strategy dispatch based on case type:
    -- 1. Trivial cases (staticity, axisymmetry, off-diagonal): simp → constant derivative
    -- 2. Matching direction (e.g., ∂²_θ g): Use C^k framework abstraction
    -- 3. Mismatching direction (e.g., ∂_θ∂_r g): Explicit calculation via separation of variables
    try {
      simp only [DifferentiableAt_θ, dCoord_r, dCoord_t, dCoord_θ, dCoord_φ, g, deriv_const]
      exact differentiableAt_const 0
    }
  }

  -- Non-trivial cases require specific handling

  -- === μ=θ cases (matching direction - use C^k abstraction) ===

  case θ.φ.φ =>
    -- g_φφ = r² sin²θ (CORRECTED)
    -- Use Ck framework (Matching direction). Remove explicit derivative lemmas from simp.
    simp only [DifferentiableAt_θ, dCoord_θ, g]
    have h_sin_sq_Cinf := contDiffAt_sin_sq θ
    -- const * sin²θ is C^∞.
    have h_gpp_Cinf := h_sin_sq_Cinf.const_mul (r^2)
    exact h_gpp_Cinf.differentiable_deriv_of_ge_two (by norm_num)

  -- === μ=r cases (mismatching direction for non-constant g - use explicit calculation) ===

  case r.θ.θ =>
    -- g_θθ = r² separates: ∂_r g_θθ = 2r
    -- Goal: DifferentiableAt_θ (2r) = differentiability of constant in θ
    simp only [DifferentiableAt_θ, dCoord_r, g, deriv_pow_two_at]
    exact differentiableAt_const (2 * r)

  case r.φ.φ =>
    -- g_φφ = r² sin²θ separates: ∂_r g_φφ = 2r sin²θ
    -- Goal: DifferentiableAt_θ (2r sin²θ) = differentiability of sin²θ as function of θ
    simp only [DifferentiableAt_θ, dCoord_r, g, deriv_mul_const, deriv_pow_two_at]
    -- sin²θ is differentiable in θ
    exact DifferentiableAt.const_mul (differentiableAt_sin_sq θ) (2 * r)
-/

-- ========== C1 Smoothness Lemmas (Γtot Differentiability) ==========
-- Required for alternation_dC_eq_Riem proof (Phase 3.2a per professor's guidance)

-- Note: Individual Christoffel symbol differentiability lemmas exist in Schwarzschild.lean
-- (differentiableAt_Γ_r_θθ_r, differentiableAt_Γ_θ_rθ_r, etc.)

/-- Christoffel symbols are differentiable in r in the Exterior domain.
Uses Definition Localization Pattern: case analysis FIRST, then expand Γtot locally in each case. -/
@[simp]
lemma Γtot_differentiable_r (M r θ : ℝ) (i j k : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  DifferentiableAt_r (fun r θ => Γtot M r θ i j k) r θ := by
  -- Definition Localization Pattern: case analysis FIRST (before expanding DifferentiableAt_r)
  cases i <;> cases j <;> cases k
  -- Handle all 64 cases explicitly (51 zero + 13 nonzero)
  case t.t.r => simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_Γ_t_tr_r M r hM h_ext
  case t.r.t => simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_Γ_t_tr_r M r hM h_ext
  case r.t.t => simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_Γ_r_tt_r M r hM h_ext
  case r.r.r => simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_Γ_r_rr_r M r hM h_ext
  case r.θ.θ => simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_Γ_r_θθ_r M r
  case r.φ.φ => simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_Γ_r_φφ_r M r θ
  case θ.r.θ =>
    simp only [DifferentiableAt_r, Γtot]
    have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM h_ext
    exact differentiableAt_Γ_θ_rθ_r r hr0
  case θ.θ.r =>
    simp only [DifferentiableAt_r, Γtot]
    have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM h_ext
    exact differentiableAt_Γ_θ_rθ_r r hr0
  case θ.φ.φ => simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_const _  -- Constant in r
  case φ.r.φ =>
    simp only [DifferentiableAt_r, Γtot]
    have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM h_ext
    exact differentiableAt_Γ_φ_rφ_r r hr0
  case φ.φ.r =>
    simp only [DifferentiableAt_r, Γtot]
    have hr0 : r ≠ 0 := r_ne_zero_of_exterior M r hM h_ext
    exact differentiableAt_Γ_φ_rφ_r r hr0
  case φ.θ.φ => simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_const _  -- Constant in r
  case φ.φ.θ => simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_const _  -- Constant in r
  -- All remaining 51 cases are zero (Γtot = 0), handle with differentiableAt_const
  all_goals { simp only [DifferentiableAt_r, Γtot]; exact differentiableAt_const _ }

/-- Christoffel symbols are differentiable in θ in the Exterior domain.
Uses Definition Localization Pattern: case analysis FIRST, then expand Γtot locally in each case. -/
@[simp]
lemma Γtot_differentiable_θ (M r θ : ℝ) (i j k : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  DifferentiableAt_θ (fun r θ => Γtot M r θ i j k) r θ := by
  -- Definition Localization Pattern: case analysis FIRST (before expanding DifferentiableAt_θ)
  cases i <;> cases j <;> cases k
  -- Handle all 64 cases explicitly (51 zero + 13 nonzero)
  case t.t.r => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _  -- Constant in θ
  case t.r.t => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _  -- Constant in θ
  case r.t.t => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _  -- Constant in θ
  case r.r.r => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _  -- Constant in θ
  case r.θ.θ => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _  -- Constant in θ
  case r.φ.φ => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_Γ_r_φφ_θ M r θ
  case θ.r.θ => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _  -- Constant in θ
  case θ.θ.r => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _  -- Constant in θ
  case θ.φ.φ => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_Γ_θ_φφ_θ θ
  case φ.r.φ => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _  -- Constant in θ
  case φ.φ.r => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _  -- Constant in θ
  case φ.θ.φ => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_Γ_φ_θφ_θ θ h_sin_nz
  case φ.φ.θ => simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_Γ_φ_θφ_θ θ h_sin_nz
  -- All remaining 51 cases are zero (Γtot = 0), handle with differentiableAt_const
  all_goals { simp only [DifferentiableAt_θ, Γtot]; exact differentiableAt_const _ }

/-- Metric tensor components are differentiable in r in the Exterior domain. -/
@[simp]
lemma g_differentiable_r (M r θ : ℝ) (i j : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  DifferentiableAt_r (fun r θ => g M i j r θ) r θ := by
  -- Case analysis on metric components (g is diagonal)
  cases i <;> cases j
  · -- g_tt: -f(r) requires Exterior for differentiability of f
    have h : Exterior M r θ := ⟨hM, h_ext⟩
    exact differentiableAt_g_tt_r M r θ h
  · -- Off-diagonal: 0 is trivially differentiable
    simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · -- g_rr: 1/f(r) requires Exterior for differentiability of f
    have h : Exterior M r θ := ⟨hM, h_ext⟩
    exact differentiableAt_g_rr_r M r θ h
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · -- g_θθ: r² is differentiable everywhere
    exact differentiableAt_g_θθ_r M r θ
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_r, g]; exact differentiableAt_const _
  · -- g_φφ: r²sin²θ is differentiable in r everywhere
    exact differentiableAt_g_φφ_r M r θ

/-- Metric tensor components are differentiable in θ in the Exterior domain. -/
@[simp]
lemma g_differentiable_θ (M r θ : ℝ) (i j : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  DifferentiableAt_θ (fun r θ => g M i j r θ) r θ := by
  -- Case analysis on metric components (g is diagonal)
  cases i <;> cases j
  · -- g_tt: -f(r) doesn't depend on θ
    simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · -- Off-diagonal: 0 is trivially differentiable
    simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · -- g_rr: 1/f(r) doesn't depend on θ
    simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · -- g_θθ: r² doesn't depend on θ
    simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · simp only [DifferentiableAt_θ, g]; exact differentiableAt_const _
  · -- g_φφ: r²sin²θ is differentiable in θ everywhere
    exact differentiableAt_g_φφ_θ M r θ

-- ========== Product Condition Localization (Phase 3.2a) ==========
-- Multiplicative analogue of additive Condition Localization from Priority 2

/-- Helper lemma for product differentiability using Condition Localization (r-direction).
    Proves that if A and B are differentiable (or μ ≠ r), then A*B is differentiable (or μ ≠ r). -/
lemma DifferentiableAt_r_mul_of_cond (A B : ℝ → ℝ → ℝ) (r θ : ℝ) (μ : Idx)
    (hA : DifferentiableAt_r A r θ ∨ μ ≠ Idx.r)
    (hB : DifferentiableAt_r B r θ ∨ μ ≠ Idx.r) :
    DifferentiableAt_r (fun r θ => A r θ * B r θ) r θ ∨ μ ≠ Idx.r := by
  by_cases h_coord : μ = Idx.r  -- Condition Localization
  · left   -- Case 1: μ = Idx.r, prove differentiability
    have hA_diff := hA.resolve_right (by simp [h_coord])
    have hB_diff := hB.resolve_right (by simp [h_coord])
    unfold DifferentiableAt_r at *
    exact DifferentiableAt.mul hA_diff hB_diff
  · right  -- Case 2: μ ≠ Idx.r, trivially true
    exact h_coord

/-- Helper lemma for product differentiability (θ-direction). -/
lemma DifferentiableAt_θ_mul_of_cond (A B : ℝ → ℝ → ℝ) (r θ : ℝ) (μ : Idx)
    (hA : DifferentiableAt_θ A r θ ∨ μ ≠ Idx.θ)
    (hB : DifferentiableAt_θ B r θ ∨ μ ≠ Idx.θ) :
    DifferentiableAt_θ (fun r θ => A r θ * B r θ) r θ ∨ μ ≠ Idx.θ := by
  by_cases h_coord : μ = Idx.θ  -- Condition Localization
  · left   -- Case 1: μ = Idx.θ, prove differentiability
    have hA_diff := hA.resolve_right (by simp [h_coord])
    have hB_diff := hB.resolve_right (by simp [h_coord])
    unfold DifferentiableAt_θ at *
    exact DifferentiableAt.mul hA_diff hB_diff
  · right  -- Case 2: μ ≠ Idx.θ, trivially true
    exact h_coord

-- ========== C2 Smoothness: ContractionC Differentiability ==========
-- NOW PROVEN using manual 4-term expansion (Professor's guidance)

/-- ContractionC is differentiable in r (sum of products of differentiable functions). -/
@[simp]
lemma ContractionC_differentiable_r (M r θ : ℝ) (a b c : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  DifferentiableAt_r (fun r θ => ContractionC M r θ a b c) r θ := by
  -- ContractionC = ∑ e∈{t,r,θ,φ}, (Γ(e,c,a)·g(e,b) + Γ(e,c,b)·g(a,e))
  -- Manual 4-term expansion, then apply DifferentiableAt.add/mul
  unfold ContractionC DifferentiableAt_r
  simp only [sumIdx_expand_gen]
  -- Now: DifferentiableAt ℝ (fun r => [t-term] + [r-term] + [θ-term] + [φ-term]) r
  -- Chain DifferentiableAt.add for 3 + operations (creates 4 goals)
  apply DifferentiableAt.add; apply DifferentiableAt.add; apply DifferentiableAt.add
  -- Each goal: (Γ·g + Γ·g) for index e ∈ {t,r,θ,φ}
  all_goals {
    apply DifferentiableAt.add
    · apply DifferentiableAt.mul
      · apply Γtot_differentiable_r; assumption; assumption; assumption
      · apply g_differentiable_r; assumption; assumption; assumption
    · apply DifferentiableAt.mul
      · apply Γtot_differentiable_r; assumption; assumption; assumption
      · apply g_differentiable_r; assumption; assumption; assumption
  }

/-- ContractionC is differentiable in θ. -/
@[simp]
lemma ContractionC_differentiable_θ (M r θ : ℝ) (a b c : Idx)
    (hM : 0 < M) (h_ext : 2 * M < r) (h_sin_nz : Real.sin θ ≠ 0) :
  DifferentiableAt_θ (fun r θ => ContractionC M r θ a b c) r θ := by
  -- ContractionC = ∑ e∈{t,r,θ,φ}, (Γ(e,c,a)·g(e,b) + Γ(e,c,b)·g(a,e))
  -- Manual 4-term expansion, then apply DifferentiableAt.add/mul
  unfold ContractionC DifferentiableAt_θ
  simp only [sumIdx_expand_gen]
  -- Now: DifferentiableAt ℝ (fun θ => [t-term] + [r-term] + [θ-term] + [φ-term]) θ
  -- Chain DifferentiableAt.add for 3 + operations (creates 4 goals)
  apply DifferentiableAt.add; apply DifferentiableAt.add; apply DifferentiableAt.add
  -- Each goal: (Γ·g + Γ·g) for index e ∈ {t,r,θ,φ}
  all_goals {
    apply DifferentiableAt.add
    · apply DifferentiableAt.mul
      · apply Γtot_differentiable_θ; assumption; assumption; assumption
      · apply g_differentiable_θ; assumption; assumption; assumption
    · apply DifferentiableAt.mul
      · apply Γtot_differentiable_θ; assumption; assumption; assumption
      · apply g_differentiable_θ; assumption; assumption; assumption
  }

/- =====================================================================
   COMPONENT LEMMAS: Explicit Riemann tensor components for Schwarzschild

   The following lemmas prove the explicit non-zero values of RiemannUp M r θ ρ σ μ ν
   for the Schwarzschild metric in the exterior region (r > 2M).

   Mathematical Note:
   - The claim R^a_{cad} = 0 (when first and third indices equal) is FALSE
   - Components are NON-ZERO but algebraically cancel when summed in Ricci tensor
   - Example: R^t_{rtr} = 2M/(r²(r-2M)) ≠ 0
   - Verified by Senior Mathematics Professor (Oct 6, 2025)

   Proof strategy (from Junior Tactics Professor):
   1. unfold RiemannUp
   2. simp [dCoord, sumIdx_expand, Γtot]  -- Does most of the work!
   3. Apply small identity lemmas (e.g., Γ_r_rr = -Γ_t_tr)
   4. Use existing derivative lemmas (e.g., deriv_Γ_t_tr_at)
   5. field_simp + ring to finish
   ===================================================================== -/

/-- R^t_{rtr} = 2M/(r²(r-2M)) for Schwarzschild exterior region -/
lemma RiemannUp_t_rtr_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.t Idx.r Idx.t Idx.r = 2 * M / (r^2 * (r - 2*M)) := by
  sorry  -- TODO: Complete using Junior Tactics Professor's pattern

/-- R^θ_{rθr} = -M/(r²(r-2M)) for Schwarzschild exterior region -/
lemma RiemannUp_θ_rθr_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.θ Idx.r Idx.θ Idx.r = - M / (r^2 * (r - 2*M)) := by
  sorry  -- TODO: Complete using Junior Tactics Professor's pattern

/-- R^φ_{rφr} = -M/(r²(r-2M)) for Schwarzschild exterior region -/
lemma RiemannUp_φ_rφr_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.φ Idx.r Idx.φ Idx.r = - M / (r^2 * (r - 2*M)) := by
  sorry

-- All 7 Schwarzschild component lemmas: shield heavy simp locally.
section ComponentLemmas

/-! Freeze any lemma that can cause global shape or large rewrites. -/
attribute [-simp]
  -- Riemann/compat infrastructure (never needed while shaping components):
  RiemannUp_mu_eq_nu

  -- θ–φ sector helpers that can trigger large trig rewrites:
  Γ_θ_φφ_mul_Γ_φ_θφ

  -- Derivative calculators: we insert them explicitly (don't let `simp` guess):
  deriv_Γ_t_tr_at deriv_Γ_r_rr_at deriv_Γ_r_tt_at
  deriv_Γ_φ_θφ_at deriv_Γ_θ_φφ_at

/-! ### Normalization helpers for post-shape algebra (no attributes) -/

-- Normalize f to (r - 2M)/r under r ≠ 0
lemma f_alt (M r : ℝ) (hr : r ≠ 0) : f M r = (r - 2*M) / r := by
  unfold f
  field_simp [hr]

-- Normalize (2*M - r) to -(r - 2*M) everywhere
lemma twoM_sub_r (M r : ℝ) : 2*M - r = -(r - 2*M) := by ring

-- Normalize (-(M*2) + r) to (r - 2*M)
lemma inv_sub_flip (M r : ℝ) : (-(M*2) + r) = (r - 2*M) := by ring

/-- Collapse `M*r*f` to a polynomial in `M` and `r` (keep `f` symbolic elsewhere). -/
lemma Mr_f_collapse (M r : ℝ) (hr : r ≠ 0) :
  M * r * f M r = M * r - 2 * M ^ 2 := by
  unfold f
  field_simp [hr]

/-- Linearized form that is perfect for your final equality steps:
    `-(M*r*f)*k` becomes `-(M*r)*k + (M^2)*(2*k)`. -/
lemma Mr_f_linearize (M r k : ℝ) (hr : r ≠ 0) :
  -(M * r * f M r * k) = -(M * r * k) + M ^ 2 * (2 * k) := by
  have hcollapse : M * r * f M r = M * r - 2 * M ^ 2 := Mr_f_collapse M r hr
  calc
    -(M * r * f M r * k)
        = -((M * r - 2 * M ^ 2) * k) := by simpa [hcollapse]
    _   = -(M * r * k) + (2 * M ^ 2) * k := by ring
    _   = -(M * r * k) + M ^ 2 * (2 * k) := by ring

/-- Symmetric version (handles r * f * M). -/
lemma Mr_f_linearize_sym (M r k : ℝ) (hr : r ≠ 0) :
  -(r * f M r * M * k) = -(M * r * k) + M ^ 2 * (2 * k) := by
  have h := Mr_f_linearize M r k hr
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- Collapser for the φφ diagonal cases. After your algebra you often get
    `((-(M*r) + 2*M^2) * k) * (r - 2*M)⁻¹`. This lemma turns it into `-(M*k)`. -/
lemma collapse_r_sub_2M (M r k : ℝ) (hsub : r - 2 * M ≠ 0) :
  ((-(M * r) + 2 * M ^ 2) * k) * (r - 2 * M)⁻¹ = -(M * k) := by
  have hsub' : r - M * 2 ≠ 0 := by convert hsub using 2; ring
  field_simp [hsub']
  ring

/-! ### t.t diagonal component lemmas -/

/-- R^r_{trt} = -2M·f(r)/r³ for Schwarzschild exterior region -/
lemma RiemannUp_r_trt_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.r Idx.t Idx.r Idx.t = -(2*M) * f M r / r^3 := by
  classical
  -- Exterior nonzero facts
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  have hf : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  -- Shape (keep Γ-symbolic; no expansion of `f`)
  have shape :
      RiemannUp M r θ Idx.r Idx.t Idx.r Idx.t
        = deriv (fun s => Γ_r_tt M s) r
            - Γ_r_tt M r * Γ_t_tr M r + Γ_r_tt M r * Γ_r_rr M r := by
    unfold RiemannUp
    simp only [dCoord_r, dCoord_t, sumIdx_expand, Γtot,
      Γtot_r_tt, Γtot_t_rt, Γtot_r_rr, Γtot_t_tr]
    ring

  -- Closed form derivative and Γ^r_{rr} = - Γ^t_{tr}
  have hder' :
      deriv (fun s => Γ_r_tt M s) r
        = - (2 * M) * (r - 3 * M) / r^4 := by
    simpa using deriv_Γ_r_tt_at M r hr
  have hrel : Γ_r_rr M r = - Γ_t_tr M r := by
    simp [Γ_r_rr, Γ_t_tr]; ring

  -- Substitute and finish by algebra (keep f symbolic!)
  rw [shape, hder', hrel]
  simp only [Γ_r_tt, Γ_t_tr, div_eq_mul_inv]
  field_simp [hr, hf, pow_two]
  ring
  have h := Mr_f_linearize M r 2 hr
  rw [h]; ring

/-- R^θ_{tθt} = M·f(r)/r³ for Schwarzschild exterior region -/
lemma RiemannUp_θ_tθt_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.θ Idx.t Idx.θ Idx.t = M * f M r / r^3 := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  unfold RiemannUp
  simp [dCoord, sumIdx_expand, Γtot, Γ_θ_rθ, Γ_r_tt, Γ_t_tr, Γ_r_rr]
  field_simp [hr, f]

/-- R^φ_{tφt} = M·f(r)/r³ for Schwarzschild exterior region -/
lemma RiemannUp_φ_tφt_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.φ Idx.t Idx.φ Idx.t = M * f M r / r^3 := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  unfold RiemannUp
  simp [dCoord, sumIdx_expand, Γtot, Γ_φ_rφ, Γ_r_tt, Γ_t_tr, Γ_r_rr]
  field_simp [hr, f]

/-! ### θθ diagonal component lemmas -/

/-- R^t_{θtθ} = -M/r for Schwarzschild exterior region -/
lemma RiemannUp_t_θtθ_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.t Idx.θ Idx.t Idx.θ = -M / r := by
  classical
  -- Exterior nonzero facts
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  have hf : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  -- Shape: only one product survives
  have shape :
      RiemannUp M r θ Idx.t Idx.θ Idx.t Idx.θ
        = Γ_t_tr M r * Γ_r_θθ M r := by
    unfold RiemannUp
    -- ∂_t Γ^t_{θθ} = 0, ∂_θ Γ^t_{tθ} = 0 (use adapter zeros + deriv_const)
    simp only [dCoord_t, dCoord_θ, sumIdx_expand, Γtot,
      Γtot_t_tr, Γtot_r_θθ, Γtot_t_θθ, deriv_const]
    ring

  -- Substitute and close with exact algebra
  rw [shape]
  simp only [Γ_t_tr, Γ_r_θθ, div_eq_mul_inv]
  field_simp [hr, hf, pow_two]
  ring
  have := Mr_f_linearize M r 1 hr
  simp at this
  exact this.symm

/-- R^r_{θrθ} = -M/r for Schwarzschild exterior region -/
lemma RiemannUp_r_θrθ_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.r Idx.θ Idx.r Idx.θ = -M / r := by
  classical
  -- Exterior nonzero facts
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  have hf : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  -- Shape: ∂_r Γ^r_{θθ} plus two products; ∂_θ Γ^r_{rθ} = 0
  have shape :
      RiemannUp M r θ Idx.r Idx.θ Idx.r Idx.θ
        = deriv (fun s => Γ_r_θθ M s) r
            + Γ_r_rr M r * Γ_r_θθ M r
            - Γ_r_θθ M r * Γ_θ_rθ r := by
    unfold RiemannUp
    simp only [dCoord_r, dCoord_θ, sumIdx_expand, Γtot,
      Γtot_r_θθ, Γtot_r_rr, Γtot_θ_rθ, deriv_const]
    ring

  -- Compute d/dr Γ^r_{θθ} = d/dr (-(r - 2M)) = -1
  have hderθθ : deriv (fun s => Γ_r_θθ M s) r = -1 := by
    -- Γ_r_θθ M s = -(s - 2*M)
    have : (fun s => Γ_r_θθ M s) = (fun s => -(s - 2*M)) := by
      funext s; simp [Γ_r_θθ]
    -- derivative of -(id - const) is -1
    simpa [this, deriv_neg, deriv_sub, deriv_const] using (deriv_id (x := r))

  -- Substitute and finish by algebra
  rw [shape, hderθθ]
  simp only [Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, div_eq_mul_inv]
  field_simp [hr, hf, pow_two]
  ring
  have h1 := Mr_f_linearize_sym M r 2 hr
  have h2 := Mr_f_linearize_sym M r 1 hr
  simp at h1 h2
  rw [h1, h2]
  ring

/-- R^φ_{θφθ} = 2M/r on the Schwarzschild exterior (off–axis) -/
lemma RiemannUp_φ_θφθ_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.φ Idx.θ Idx.φ Idx.θ = (2*M) / r := by
  classical
  -- exterior nonzero
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext

  -- shape: ∂_φ Γ^φ_{θθ} = 0; only one derivative and two products survive
  have shape :
      RiemannUp M r θ Idx.φ Idx.θ Idx.φ Idx.θ
        = -(deriv (fun t => Γ_φ_θφ t) θ)
          + Γ_φ_rφ r * Γ_r_θθ M r
          - (Γ_φ_θφ θ) * (Γ_φ_θφ θ) := by
    unfold RiemannUp
    simp only [dCoord_φ, dCoord_θ, sumIdx_expand, Γtot,
               Γtot_φ_θθ, Γtot_φ_φθ, Γtot_φ_rφ, Γtot_r_θθ, deriv_const]
    ring

  -- substitute closed forms and finish: (1/sin²) − (cos²/sin²) = 1, remaining term is −(r−2M)/r
  rw [shape]
  -- Expand Γ-terms, but do NOT rewrite the derivative yet
  simp only [Γ_φ_rφ, Γ_r_θθ, Γ_φ_θφ, div_eq_mul_inv]

  -- Clear the (r) and (sin θ)^2 denominators first; this produces the "r·sin²θ" factors you saw
  field_simp [hr, h_sin_nz, pow_two]

  -- Now replace the derivative of cot with the closed form  - 1/(sin θ)^2.
  have hdcot :
    deriv (fun t => Real.cos t / Real.sin t) θ
      = - 1 / (Real.sin θ)^2 := by
    -- This is just `deriv_Γ_φ_θφ_at` with `Γ_φ_θφ = cos/sin`.
    simpa [Γ_φ_θφ] using deriv_Γ_φ_θφ_at θ h_sin_nz
  rw [hdcot]

  -- Work with the factored shape produced by the earlier `field_simp`.
  -- Goal (after the previous steps):
  --   (-(- 1 / (Real.sin θ)^2 * r) + -(r - 2*M)) * (Real.sin θ)^2 - r * (Real.cos θ)^2
  --   = 2 * M * (Real.sin θ)^2

  -- 1) Distribute the product so the csc²·sin² cancellation is an atomic step.
  have hsplit :
      (-(- 1 / (Real.sin θ)^2 * r) + -(r - 2*M)) * (Real.sin θ)^2 - r * (Real.cos θ)^2
        = (-(- 1 / (Real.sin θ)^2 * r) * (Real.sin θ)^2)
          + (-(r - 2*M) * (Real.sin θ)^2) - r * (Real.cos θ)^2 := by
    ring

  -- 2) Cancel csc²·sin² -> 1 in the first product. Needs sin θ ≠ 0.
  have hA : -(- 1 / (Real.sin θ)^2 * r) * (Real.sin θ)^2 = r := by
    field_simp [h_sin_nz, pow_two]

  -- 3) Pythagorean identity in the polynomial form we need.
  have trig : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := by
    simpa [pow_two] using Real.sin_sq_add_cos_sq θ

  -- 4) Finish with a short calc (no global rewriting; only ring and trig).
  have hfinish :
      (-(- 1 / (Real.sin θ)^2 * r) + -(r - 2*M)) * (Real.sin θ)^2 - r * (Real.cos θ)^2
        = 2 * M * (Real.sin θ)^2 := by
    calc
      (-(- 1 / (Real.sin θ)^2 * r) + -(r - 2*M)) * (Real.sin θ)^2 - r * (Real.cos θ)^2
          = r + (-(r - 2*M) * (Real.sin θ)^2) - r * (Real.cos θ)^2 := by
            rw [hsplit, hA]
      _   = r - r * ((Real.sin θ)^2 + (Real.cos θ)^2) + 2 * M * (Real.sin θ)^2 := by
            ring
      _   = r - r * 1 + 2 * M * (Real.sin θ)^2 := by
            rw [trig]
      _   = 2 * M * (Real.sin θ)^2 := by
            ring

  -- 5) `simpa` takes care of harmless associativity/commutativity differences
  --     (e.g. `M * sin² * 2` vs `2 * M * sin²`).
  simpa [mul_comm, mul_left_comm, mul_assoc] using hfinish

/-! ### φφ diagonal component lemmas -/

/-- R^t_{φtφ} = -M·sin²θ / r on the Schwarzschild exterior -/
lemma RiemannUp_t_φtφ_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.t Idx.φ Idx.t Idx.φ = -(M * Real.sin θ ^ 2) / r := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  have hf : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  -- shape: only λ = r contributes in the product sums; both derivatives are 0
  have shape :
      RiemannUp M r θ Idx.t Idx.φ Idx.t Idx.φ
        = Γ_t_tr M r * Γ_r_φφ M r θ := by
    unfold RiemannUp
    simp only [dCoord_t, dCoord_φ, sumIdx_expand, Γtot,
               Γtot_t_tr, Γtot_r_φφ, deriv_const]
    ring

  rw [shape]  -- your shape reduces to Γ_t_tr * Γ_r_φφ
  simp only [Γ_t_tr, Γ_r_φφ, div_eq_mul_inv]
  field_simp [hr, hf, pow_two]
  ring
  have := Mr_f_linearize M r 1 hr
  simp at this
  have : -(M * r * sin θ ^ 2) + M ^ 2 * sin θ ^ 2 * 2 = -(M * r * sin θ ^ 2 * f M r) := by
    have h := this
    calc -(M * r * sin θ ^ 2) + M ^ 2 * sin θ ^ 2 * 2
        = sin θ ^ 2 * (-(M * r) + M ^ 2 * 2) := by ring
    _   = sin θ ^ 2 * (-(M * r * f M r)) := by rw [← h]
    _   = -(M * r * sin θ ^ 2 * f M r) := by ring
  exact this

/-- R^r_{φrφ} = -M·sin²θ / r on the Schwarzschild exterior -/
lemma RiemannUp_r_φrφ_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.r Idx.φ Idx.r Idx.φ = -(M * Real.sin θ ^ 2) / r := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  have hf : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  -- shape: derivative of Γ^r_{φφ} and two products; ∂_φ Γ^r_{rφ} = 0
  have shape :
      RiemannUp M r θ Idx.r Idx.φ Idx.r Idx.φ
        = deriv (fun s => Γ_r_φφ M s θ) r
            + Γ_r_rr M r * Γ_r_φφ M r θ
            - Γ_r_φφ M r θ * Γ_φ_rφ r := by
    unfold RiemannUp
    simp only [dCoord_r, dCoord_φ, sumIdx_expand, Γtot,
               Γtot_r_φφ, Γtot_r_rr, Γtot_φ_rφ, deriv_const]
    ring

  -- compute ∂_r [Γ^r_{φφ}(M, s, θ)] = ∂_r[-(s - 2M)·sin²θ] = -sin²θ
  have hderφφ : deriv (fun s => Γ_r_φφ M s θ) r = -(Real.sin θ)^2 := by
    have h1 : deriv (fun s : ℝ => s - 2 * M) r = 1 := by
      simpa using deriv_sub (differentiableAt_id r) (differentiableAt_const (2 * M))
    have : deriv (fun s : ℝ => -(s - 2 * M) * (Real.sin θ)^2) r = -(Real.sin θ)^2 := by
      simp [deriv_mul_const, deriv_neg, h1]
    simpa [Γ_r_φφ] using this

  rw [shape, hderφφ]  -- your shape reduces to Γ_r_rr * Γ_r_φφ - Γ_r_φφ * Γ_φ_rφ (with the signs you've fixed)
  simp only [Γ_r_rr, Γ_r_φφ, Γ_φ_rφ, div_eq_mul_inv]
  field_simp [hr, hf, pow_two]
  ring
  have h1 := Mr_f_linearize_sym M r 2 hr
  have h2 := Mr_f_linearize_sym M r 1 hr
  simp at h1 h2
  -- Use the linearize lemmas to prove the needed equality
  have : -(sin θ ^ 2 * r * f M r * M * 2) + (sin θ ^ 2 * r * M - sin θ ^ 2 * M ^ 2 * 2) =
         -(sin θ ^ 2 * r * f M r * M) := by
    have key : -(r * f M r * M * 2) + (r * M - M ^ 2 * 2) = -(r * f M r * M) := by
      linarith [h1, h2]
    calc -(sin θ ^ 2 * r * f M r * M * 2) + (sin θ ^ 2 * r * M - sin θ ^ 2 * M ^ 2 * 2)
        = sin θ ^ 2 * (-(r * f M r * M * 2) + (r * M - M ^ 2 * 2)) := by ring
    _   = sin θ ^ 2 * (-(r * f M r * M)) := by rw [key]
    _   = -(sin θ ^ 2 * r * f M r * M) := by ring
  exact this

/-- R^θ_{φθφ} = 2M·sin²θ / r on the Schwarzschild exterior (off–axis) -/
lemma RiemannUp_θ_φθφ_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.θ Idx.φ Idx.θ Idx.φ = (2 * M * Real.sin θ ^ 2) / r := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext

  -- shape: only one derivative and two products survive; ∂_φ Γ^θ_{φφ} = 0
  have shape :
      RiemannUp M r θ Idx.θ Idx.φ Idx.θ Idx.φ
        = deriv (fun t => Γ_θ_φφ t) θ
            + Γ_θ_rθ r * Γ_r_φφ M r θ
            - Γ_θ_φφ θ * Γ_φ_θφ θ := by
    unfold RiemannUp
    simp only [dCoord_θ, dCoord_φ, sumIdx_expand, Γtot,
               Γtot_θ_φφ, Γtot_r_φφ, Γtot_θ_rθ, Γtot_φ_θφ, deriv_const]
    ring

  -- Use your established lemma; no re-derivation
  have hderφφ : deriv (fun t => Γ_θ_φφ t) θ = (Real.sin θ)^2 - (Real.cos θ)^2 := by
    simpa using deriv_Γ_θ_φφ_at θ

  rw [shape, hderφφ]
  simp only [Γ_θ_rθ, Γ_r_φφ, Γ_θ_φφ, Γ_φ_θφ, div_eq_mul_inv]
  -- Everything is polynomial/trigonometric; no f, no denominators except r in Γ_θ_rθ/Γ_φ_rφ
  field_simp [hr, pow_two]  -- (no hr/hf needed here if no 1/r appears; include hr if you simplified to 1/r)
  ring

end ComponentLemmas

/- Zero component lemmas: When μ = ν, antisymmetry forces R^ρ_{σμμ} = 0 -/

@[simp] lemma RiemannUp_r_rrr_ext (M r θ : ℝ) :
  RiemannUp M r θ Idx.r Idx.r Idx.r Idx.r = 0 := by
  simpa using RiemannUp_mu_eq_nu M r θ Idx.r Idx.r Idx.r

@[simp] lemma RiemannUp_t_ttt_ext (M r θ : ℝ) :
  RiemannUp M r θ Idx.t Idx.t Idx.t Idx.t = 0 := by
  simpa using RiemannUp_mu_eq_nu M r θ Idx.t Idx.t Idx.t

@[simp] lemma RiemannUp_θ_θθθ_ext (M r θ : ℝ) :
  RiemannUp M r θ Idx.θ Idx.θ Idx.θ Idx.θ = 0 := by
  simpa using RiemannUp_mu_eq_nu M r θ Idx.θ Idx.θ Idx.θ

@[simp] lemma RiemannUp_φ_φφφ_ext (M r θ : ℝ) :
  RiemannUp M r θ Idx.φ Idx.φ Idx.φ Idx.φ = 0 := by
  simpa using RiemannUp_mu_eq_nu M r θ Idx.φ Idx.φ Idx.φ

/-! ### Diagonal Ricci cancellation lemmas -/

/-- Cancellation for R_rr: Component values sum to zero -/
lemma Ricci_rr_cancellation
  (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.t Idx.r Idx.t Idx.r +
  RiemannUp M r θ Idx.r Idx.r Idx.r Idx.r +
  RiemannUp M r θ Idx.θ Idx.r Idx.θ Idx.r +
  RiemannUp M r θ Idx.φ Idx.r Idx.φ Idx.r = 0 := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  simp [RiemannUp_mu_eq_nu,
        RiemannUp_t_rtr_ext M r θ h_ext h_sin_nz,
        RiemannUp_θ_rθr_ext M r θ h_ext h_sin_nz,
        RiemannUp_φ_rφr_ext M r θ h_ext h_sin_nz]
  field_simp [hr]; ring

/-- Cancellation for R_tt: Component values sum to zero -/
lemma Ricci_tt_cancellation
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.t Idx.t Idx.t Idx.t +
  RiemannUp M r θ Idx.r Idx.t Idx.r Idx.t +
  RiemannUp M r θ Idx.θ Idx.t Idx.θ Idx.t +
  RiemannUp M r θ Idx.φ Idx.t Idx.φ Idx.t = 0 := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  simp [RiemannUp_mu_eq_nu]  -- drops R^t_{ttt}
  -- Substitute the three component lemmas:
  simp [RiemannUp_r_trt_ext M r θ h_ext,
        RiemannUp_θ_tθt_ext M r θ h_ext,
        RiemannUp_φ_tφt_ext M r θ h_ext]
  -- Now it's pure algebra:
  field_simp [hr, f]; ring

/-- Cancellation for R_θθ: Component values sum to zero -/
lemma Ricci_θθ_cancellation
  (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.t Idx.θ Idx.t Idx.θ +
  RiemannUp M r θ Idx.r Idx.θ Idx.r Idx.θ +
  RiemannUp M r θ Idx.θ Idx.θ Idx.θ Idx.θ +
  RiemannUp M r θ Idx.φ Idx.θ Idx.φ Idx.θ = 0 := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  simp [RiemannUp_mu_eq_nu,
        RiemannUp_t_θtθ_ext M r θ h_ext,
        RiemannUp_r_θrθ_ext M r θ h_ext,
        RiemannUp_φ_θφθ_ext M r θ h_ext h_sin_nz]
  field_simp [hr]; ring

/-- Cancellation for R_φφ: Component values sum to zero -/
lemma Ricci_φφ_cancellation
  (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
  RiemannUp M r θ Idx.t Idx.φ Idx.t Idx.φ +
  RiemannUp M r θ Idx.r Idx.φ Idx.r Idx.φ +
  RiemannUp M r θ Idx.θ Idx.φ Idx.θ Idx.φ +
  RiemannUp M r θ Idx.φ Idx.φ Idx.φ Idx.φ = 0 := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  simp [RiemannUp_mu_eq_nu,
        RiemannUp_t_φtφ_ext M r θ h_ext,
        RiemannUp_r_φrφ_ext M r θ h_ext,
        RiemannUp_θ_φθφ_ext M r θ h_ext h_sin_nz]
  field_simp [hr]; ring

/-- Squared symmetry in the last pair. Safer for simp. -/
lemma Riemann_sq_swap_c_d (M r θ : ℝ) (a b c d : Idx) :
  (Riemann M r θ a b d c)^2 = (Riemann M r θ a b c d)^2 := by
  rw [Riemann_swap_c_d, sq_neg]

/-! ### New: vanishing lemmas for equal indices -/

/-- If the last two indices are equal, the fully-lowered component vanishes. -/
@[simp] lemma Riemann_last_equal_zero (M r θ : ℝ) (a b c : Idx) :
  Riemann M r θ a b c c = 0 := by
  classical
  -- From antisymmetry in (c,d): R_{abcc} = - R_{abcc} ⇒ 2⋅R_{abcc} = 0 ⇒ R_{abcc} = 0.
  have h := Riemann_swap_c_d M r θ a b c c
  -- h : Riemann … a b c c = - Riemann … a b c c
  have : (2 : ℝ) * Riemann M r θ a b c c = 0 := by
    -- add R_{abcc} to both sides of h
    simpa [two_mul, add_comm] using congrArg (fun t => t + Riemann M r θ a b c c) h
  -- In ℝ, 2 ≠ 0
  have two_ne : (2 : ℝ) ≠ 0 := two_ne_zero
  -- Cancel the nonzero factor
  exact (mul_eq_zero.mp this).resolve_left two_ne

/-- A squared form that is often simpler to use under sums. -/
@[simp] lemma Riemann_sq_last_equal_zero (M r θ : ℝ) (a b c : Idx) :
  (Riemann M r θ a b c c)^2 = 0 := by
  simp

/-! ### Off-block vanishing lemmas for structural decomposition -/

/-- Representative off-block vanishing: R_{tr tθ} = 0 -/
@[simp] lemma R_tr_tθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.t Idx.θ = 0 := by
  classical
  -- Contract the first index (only ρ = t contributes by diagonality of g).
  rw [Riemann_contract_first]
  -- Expand the mixed-index Riemann and use staticity/axisymmetry + Christoffel sparsity.
  unfold RiemannUp
  -- `∂_t` pieces vanish; θ-derivative hits a θ-constant term here; Γ-combinations are sparse.
  simp only [dCoord_t, dCoord_θ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tr θt} = 0 -/
@[simp] lemma R_tr_θt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.θ Idx.t = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tr_tθ_zero M r θ)

/-- Off-block: R_{tr tφ} = 0 -/
@[simp] lemma R_tr_tφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.t Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By antisymmetry: R_{tr φt} = 0 -/
@[simp] lemma R_tr_φt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.φ Idx.t = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tr_tφ_zero M r θ)

/-- Off-block: R_{tr rθ} = 0 -/
@[simp] lemma R_tr_rθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.r Idx.θ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_r, dCoord_θ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By antisymmetry: R_{tr θr} = 0 -/
@[simp] lemma R_tr_θr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.θ Idx.r = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tr_rθ_zero M r θ)

/-- Off-block: R_{tr rφ} = 0. -/
@[simp] lemma R_tr_rφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.r Idx.φ = 0 := by
  classical
  -- Contract first index and expand the mixed-index definition.
  rw [Riemann_contract_first]
  unfold RiemannUp
  -- Staticity/axisymmetry and Γ-sparsity kill all terms.
  simp only [dCoord_r, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tr φr} = 0. (No `[simp]` to avoid loops.) -/
lemma R_tr_φr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.φ Idx.r = 0 := by
  -- R_{tr φ r} = - R_{tr r φ} = 0
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tr_rφ_zero M r θ)

/-- Off-block: R_{tr θφ} = 0. -/
@[simp] lemma R_tr_θφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.θ Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_θ, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tr φθ} = 0. (No `[simp]` to avoid loops.) -/
lemma R_tr_φθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.r Idx.φ Idx.θ = 0 := by
  -- R_{tr φ θ} = - R_{tr θ φ} = 0
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tr_θφ_zero M r θ)

/-! ### Off-block vanishing for the (t,θ) outer pair -/

/-- Off-block: R_{tθ tr} = 0. -/
@[simp] lemma R_tθ_tr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.t Idx.r = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tθ rt} = 0. (No `[simp]` to avoid loops.) -/
lemma R_tθ_rt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.r Idx.t = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tθ_tr_zero M r θ)

/-- Off-block: R_{tθ tφ} = 0. -/
@[simp] lemma R_tθ_tφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.t Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tθ φt} = 0. (No `[simp]` to avoid loops.) -/
lemma R_tθ_φt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.φ Idx.t = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tθ_tφ_zero M r θ)

/-! ### Complete the remaining off-blocks for the (t,θ) outer pair -/

/-- Off-block: R_{tθ rθ} = 0. -/
@[simp] lemma R_tθ_rθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.r Idx.θ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_r, dCoord_θ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tθ θr} = 0. (No `[simp]` to avoid loops.) -/
lemma R_tθ_θr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.θ Idx.r = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tθ_rθ_zero M r θ)

/-- Off-block: R_{tθ rφ} = 0. -/
@[simp] lemma R_tθ_rφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.r Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_r, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tθ φr} = 0. (No `[simp]` to avoid loops.) -/
lemma R_tθ_φr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.φ Idx.r = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tθ_rφ_zero M r θ)

/-- Off-block: R_{tθ θφ} = 0. -/
@[simp] lemma R_tθ_θφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.θ Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_θ, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tθ φθ} = 0. (No `[simp]` to avoid loops.) -/
lemma R_tθ_φθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.θ Idx.φ Idx.θ = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tθ_θφ_zero M r θ)

/-! ### Full off-block set for the (t,φ) outer pair -/

/-- Off-block: R_{tφ tr} = 0. -/
@[simp] lemma R_tφ_tr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.t Idx.r = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tφ rt} = 0. -/
lemma R_tφ_rt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.r Idx.t = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tφ_tr_zero M r θ)

/-- Off-block: R_{tφ tθ} = 0. -/
@[simp] lemma R_tφ_tθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.t Idx.θ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_θ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tφ θt} = 0. -/
lemma R_tφ_θt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.θ Idx.t = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tφ_tθ_zero M r θ)

/-- Off-block: R_{tφ rφ} = 0. -/
@[simp] lemma R_tφ_rφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.r Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_r, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tφ φr} = 0. -/
lemma R_tφ_φr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.φ Idx.r = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tφ_rφ_zero M r θ)

/-- Off-block: R_{tφ rθ} = 0. -/
@[simp] lemma R_tφ_rθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.r Idx.θ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_r, dCoord_θ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{tφ θr} = 0. -/
lemma R_tφ_θr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.θ Idx.r = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tφ_rθ_zero M r θ)

/-- Off-block: R_{tφ θφ} = 0. -/
@[simp] lemma R_tφ_θφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.θ Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp [dCoord_θ, dCoord_φ, Γtot,
        Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ]

/-- By last-pair antisymmetry: R_{tφ φθ} = 0. -/
lemma R_tφ_φθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.t Idx.φ Idx.φ Idx.θ = 0 := by
  rw [Riemann_swap_c_d]
  exact neg_eq_zero.mpr (R_tφ_θφ_zero M r θ)

/-! ---------------------------------------------------------------------------
    Off-block vanishing for the (r,θ) outer pair
--------------------------------------------------------------------------- -/

/-- Off-block: R_{rθ tr} = 0. -/
@[simp] lemma R_rθ_tr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.t Idx.r = 0 := by
  classical
  rw [Riemann_contract_first]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_r, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{rθ rt} = 0. -/
lemma R_rθ_rt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.r Idx.t = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rθ_tr_zero M r θ)

/-- Off-block: R_{rθ tθ} = 0. -/
@[simp] lemma R_rθ_tθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.t Idx.θ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp only [dCoord_t, dCoord_θ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{rθ θt} = 0. -/
lemma R_rθ_θt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.θ Idx.t = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rθ_tθ_zero M r θ)

/-- Off-block: R_{rθ tφ} = 0. -/
@[simp] lemma R_rθ_tφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.t Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp only [dCoord_t, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{rθ φt} = 0. -/
lemma R_rθ_φt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.φ Idx.t = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rθ_tφ_zero M r θ)

/-- Off-block: R_{rθ rφ} = 0. -/
@[simp] lemma R_rθ_rφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.r Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp only [dCoord_r, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{rθ φr} = 0. -/
lemma R_rθ_φr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.φ Idx.r = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rθ_rφ_zero M r θ)

/-- Off-block: R_{rθ θφ} = 0. -/
@[simp] lemma R_rθ_θφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.θ Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp only [dCoord_θ, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{rθ φθ} = 0. -/
lemma R_rθ_φθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.θ Idx.φ Idx.θ = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rθ_θφ_zero M r θ)

/-! ---------------------------------------------------------------------------
    Off-block vanishing for the (r,φ) outer pair
--------------------------------------------------------------------------- -/

/-- Off-block: R_{rφ tr} = 0. -/
@[simp] lemma R_rφ_tr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.t Idx.r = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp only [dCoord_t, dCoord_r, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{rφ rt} = 0. -/
lemma R_rφ_rt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.r Idx.t = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rφ_tr_zero M r θ)

/-- Off-block: R_{rφ tθ} = 0. -/
@[simp] lemma R_rφ_tθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.t Idx.θ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp only [dCoord_t, dCoord_θ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{rφ θt} = 0. -/
lemma R_rφ_θt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.θ Idx.t = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rφ_tθ_zero M r θ)

/-- Off-block: R_{rφ tφ} = 0. -/
@[simp] lemma R_rφ_tφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.t Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp only [dCoord_t, dCoord_φ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{rφ φt} = 0. -/
lemma R_rφ_φt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.φ Idx.t = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rφ_tφ_zero M r θ)

/-- Off-block: R_{rφ rθ} = 0. -/
@[simp] lemma R_rφ_rθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.r Idx.θ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp only [dCoord_r, dCoord_θ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{rφ θr} = 0. -/
lemma R_rφ_θr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.θ Idx.r = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rφ_rθ_zero M r θ)

/-! #### Small trig helper used in the shared-φ proofs -/

/-- On the off-axis region `sin θ ≠ 0`, one `sin` cancels in `sin^2 θ · cot θ`. -/
lemma sin_sq_mul_cot_cancel (θ : ℝ) (h : Real.sin θ ≠ 0) :
  (Real.sin θ)^2 * (Real.cos θ / Real.sin θ) = Real.sin θ * Real.cos θ := by
  -- When sin θ ≠ 0, we can cancel one sin θ from sin^2 θ / sin θ
  field_simp [h, pow_two]

/-- Scalar bracket for `R_{rφ θφ}` vanishes (θ‑only algebra; `g` stays out). -/
lemma bracket_rφ_θφ_scalar_zero (M r θ : ℝ) :
  ( dCoord Idx.θ (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ
    - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.r Idx.θ Idx.φ) r θ )
  + ( Γtot M r θ Idx.r Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
      - Γtot M r θ Idx.r Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.φ ) = 0 := by
  classical
  -- ∂_φ Γ^r_{θφ} = 0 (axisymmetry).
  have dφ_rθφ :
      dCoord Idx.φ (fun r θ => Γtot M r θ Idx.r Idx.θ Idx.φ) r θ = 0 := by
    simp [dCoord_φ, Γtot]
  by_cases hsin : Real.sin θ = 0
  ·
    -- On-axis: keep cot folded; sin-factors kill everything.
    simp [Γtot, dCoord_θ_Γ_r_φφ, dCoord_φ,
          Γ_r_θθ, Γ_θ_φφ, Γ_r_φφ, Γ_φ_θφ,
          dφ_rθφ, hsin, pow_two]
  ·
    -- Off-axis: compute contributions explicitly and reduce to a linear combination of t.
    -- θ-derivative term:
    have hθ :
      dCoord Idx.θ (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ
      = (-2 : ℝ) * (r - 2*M) * Real.sin θ * Real.cos θ := by
      simpa [Γtot, dCoord_θ_Γ_r_φφ, mul_comm, mul_left_comm, mul_assoc, pow_two]
    -- λ = θ product:
    have hlambda_theta :
      Γtot M r θ Idx.r Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
      = (-(r - 2*M)) * (- Real.sin θ * Real.cos θ) := by
      simpa [Γtot, Γ_r_θθ, Γ_θ_φφ, mul_comm, mul_left_comm, mul_assoc, pow_two]
    -- λ = φ product (note the bracket has a minus in front of this product):
    have hprod :
      Γtot M r θ Idx.r Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.φ
      = (-(r - 2*M) * (Real.sin θ)^2) * (Real.cos θ / Real.sin θ) := by
      simpa [Γtot, Γ_r_φφ, Γ_φ_θφ, mul_comm, mul_left_comm, mul_assoc, pow_two]
    -- Local cot cancellation, valid off-axis:
    have hcot : (Real.sin θ)^2 * (Real.cos θ / Real.sin θ) = Real.sin θ * Real.cos θ := by
      exact sin_sq_mul_cot_cancel θ hsin
    -- Common θ-factor:
    set t := (r - 2*M) * Real.sin θ * Real.cos θ with ht
    have h2 : (-(r - 2*M)) * (- Real.sin θ * Real.cos θ) = t := by
      simp only [t, neg_mul, mul_neg, neg_neg]
      ring
    have h3 :
      (r - 2*M) * (Real.sin θ)^2 * (Real.cos θ / Real.sin θ) = t := by
      calc (r - 2*M) * (Real.sin θ)^2 * (Real.cos θ / Real.sin θ)
        = (r - 2*M) * ((Real.sin θ)^2 * (Real.cos θ / Real.sin θ)) := by ring
      _ = (r - 2*M) * (Real.sin θ * Real.cos θ) := by rw [hcot]
      _ = (r - 2*M) * Real.sin θ * Real.cos θ := by ring
      _ = t := rfl
    -- Assemble the bracket:
    have :
      ( dCoord Idx.θ (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ
        - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.r Idx.θ Idx.φ) r θ )
      + ( Γtot M r θ Idx.r Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
          - Γtot M r θ Idx.r Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.φ )
      = (-2 : ℝ) * t + t + ((r - 2*M) * (Real.sin θ)^2 * (Real.cos θ / Real.sin θ)) := by
      have hφ : dCoord Idx.φ (fun r θ => Γtot M r θ Idx.r Idx.θ Idx.φ) r θ = 0 := dφ_rθφ
      calc
        _ = (dCoord Idx.θ (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ)
            - 0 
            + (Γtot M r θ Idx.r Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ)
            - (Γtot M r θ Idx.r Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.φ) := by
          rw [hφ]; ring
        _ = (-2 : ℝ) * (r - 2*M) * Real.sin θ * Real.cos θ
            + (-(r - 2*M)) * (- Real.sin θ * Real.cos θ)
            - ( (-(r - 2*M) * (Real.sin θ)^2) * (Real.cos θ / Real.sin θ)) := by
          rw [hθ, hlambda_theta, hprod]
          simp only [sub_eq_add_neg]
          ring
        _ = (-2 : ℝ) * t + t + ((r - 2*M) * (Real.sin θ)^2 * (Real.cos θ / Real.sin θ)) := by
          rw [h2]
          ring
    -- Replace last term by t and close with (-2)+1+1=0.
    have hcoef : ((-2 : ℝ) + 1 + 1) = 0 := by norm_num
    calc
      ( dCoord Idx.θ (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ
        - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.r Idx.θ Idx.φ) r θ )
      + ( Γtot M r θ Idx.r Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
          - Γtot M r θ Idx.r Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.φ )
        = (-2 : ℝ) * t + t + t := by simpa [this, h3]
    _ = 0 := by
      have : (-2 : ℝ) * t + t + t = ((-2 : ℝ) + 1 + 1) * t := by ring
      simpa [hcoef] using this

/-- Scalar bracket for `R_{θφ rφ}` vanishes (θ‑only algebra; `g` stays out). -/
lemma bracket_θφ_rφ_scalar_zero (M r θ : ℝ) :
  ( dCoord Idx.r (fun r θ => Γtot M r θ Idx.θ Idx.φ Idx.φ) r θ
    - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.θ Idx.r Idx.φ) r θ )
  + ( Γtot M r θ Idx.θ Idx.r Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
      - Γtot M r θ Idx.θ Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.r Idx.φ ) = 0 := by
  classical
  -- θ‑only / r‑only dependencies.
  have dr_θφφ :
      dCoord Idx.r (fun r θ => Γtot M r θ Idx.θ Idx.φ Idx.φ) r θ = 0 := by
    simp [dCoord_r, Γtot, Γ_θ_φφ]
  have dφ_θrφ :
      dCoord Idx.φ (fun r θ => Γtot M r θ Idx.θ Idx.r Idx.φ) r θ = 0 := by
    simp [dCoord_φ, Γtot, Γ_θ_rθ]
  -- Only lambda = θ and lambda = φ contribute and they cancel exactly.
  -- Γ^θ_{rθ} Γ^θ_{φφ} - Γ^θ_{φφ} Γ^φ_{rφ} = (1/r)(-sin θ cos θ) - (-sin θ cos θ)(1/r) = 0.
  simp [Γtot, dCoord_r, dCoord_φ, dr_θφφ, dφ_θrφ,
        Γ_θ_rθ, Γ_θ_φφ, Γ_φ_rφ, mul_comm]

/-! ### sumIdx collapse lemmas for shared-φ cases -/

-- Only λ = θ contributes to Σλ Γ^r_{θλ} Γ^λ_{φφ}.
lemma sumIdx_rθφ_left (M r θ : ℝ) :
  sumIdx (fun lam => Γtot M r θ Idx.r Idx.θ lam * Γtot M r θ lam Idx.φ Idx.φ)
  = Γtot M r θ Idx.r Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ := by
  classical
  -- Enumerate lam ∈ {t,r,θ,φ}; all but lam=θ vanish by your Γ facts.
  simp [sumIdx_expand, Γtot, Γ_r_θθ, Γ_θ_φφ,
        Γ_t_tr, Γ_r_rr, Γ_r_φφ, Γ_φ_rφ, Γ_φ_θφ,
        mul_comm, mul_left_comm, mul_assoc]

-- Only λ = φ contributes to Σλ Γ^r_{φλ} Γ^λ_{θφ}.
lemma sumIdx_rφθ_right (M r θ : ℝ) :
  sumIdx (fun lam => Γtot M r θ Idx.r Idx.φ lam * Γtot M r θ lam Idx.θ Idx.φ)
  = Γtot M r θ Idx.r Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.φ := by
  classical
  simp [sumIdx_expand, Γtot, Γ_r_φφ, Γ_φ_θφ,
        Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_θ_φφ, Γ_φ_rφ,
        mul_comm, mul_left_comm, mul_assoc]

-- Only λ = θ contributes to Σλ Γ^θ_{rλ} Γ^λ_{φφ}.
lemma sumIdx_θrφ_left (M r θ : ℝ) :
  sumIdx (fun lam => Γtot M r θ Idx.θ Idx.r lam * Γtot M r θ lam Idx.φ Idx.φ)
  = Γtot M r θ Idx.θ Idx.r Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ := by
  classical
  simp [sumIdx_expand, Γtot, Γ_θ_rθ, Γ_θ_φφ,
        Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_r_φφ, Γ_φ_rφ, Γ_φ_θφ,
        mul_comm, mul_left_comm, mul_assoc]

-- Only λ = φ contributes to Σλ Γ^θ_{φλ} Γ^λ_{rφ}.
lemma sumIdx_θφr_right (M r θ : ℝ) :
  sumIdx (fun lam => Γtot M r θ Idx.θ Idx.φ lam * Γtot M r θ lam Idx.r Idx.φ)
  = Γtot M r θ Idx.θ Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.r Idx.φ := by
  classical
  simp [sumIdx_expand, Γtot, Γ_θ_φφ, Γ_φ_rφ,
        Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_r_φφ, Γ_θ_rθ, Γ_φ_θφ,
        mul_comm, mul_left_comm, mul_assoc]

/-- Normalize `RiemannUp r φ θ φ` to the scalar bracket form you proved. -/
lemma RiemannUp_rφ_θφ_as_bracket (M r θ : ℝ) :
  RiemannUp M r θ Idx.r Idx.φ Idx.θ Idx.φ
    =
    ( dCoord Idx.θ (fun r θ => Γtot M r θ Idx.r Idx.φ Idx.φ) r θ
      - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.r Idx.θ Idx.φ) r θ )
    +
    ( Γtot M r θ Idx.r Idx.θ Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
      - Γtot M r θ Idx.r Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.θ Idx.φ ) := by
  classical
  -- Turn Σ (a - b) into (Σ a) - (Σ b), then collapse both Σ to the single survivor.
  simp only [RiemannUp, sumIdx_sub, sumIdx_rθφ_left, sumIdx_rφθ_right]

/-- Normalize `RiemannUp θ φ r φ` to the scalar bracket form you proved. -/
lemma RiemannUp_θφ_rφ_as_bracket (M r θ : ℝ) :
  RiemannUp M r θ Idx.θ Idx.φ Idx.r Idx.φ
    =
    ( dCoord Idx.r (fun r θ => Γtot M r θ Idx.θ Idx.φ Idx.φ) r θ
      - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.θ Idx.r Idx.φ) r θ )
    +
    ( sumIdx (fun lam => Γtot M r θ Idx.θ Idx.r lam * Γtot M r θ lam Idx.φ Idx.φ)
      - sumIdx (fun lam => Γtot M r θ Idx.θ Idx.φ lam * Γtot M r θ lam Idx.r Idx.φ) ) := by
  classical
  simp only [RiemannUp, sumIdx_sub]

/-- Collapse the two `sumIdx` in `RiemannUp_θφ_rφ_as_bracket` to the single survivors. -/
lemma RiemannUp_θφ_rφ_as_bracket_collapsed (M r θ : ℝ) :
  RiemannUp M r θ Idx.θ Idx.φ Idx.r Idx.φ
    =
    ( dCoord Idx.r (fun r θ => Γtot M r θ Idx.θ Idx.φ Idx.φ) r θ
      - dCoord Idx.φ (fun r θ => Γtot M r θ Idx.θ Idx.r Idx.φ) r θ )
    +
    ( Γtot M r θ Idx.θ Idx.r Idx.θ * Γtot M r θ Idx.θ Idx.φ Idx.φ
      - Γtot M r θ Idx.θ Idx.φ Idx.φ * Γtot M r θ Idx.φ Idx.r Idx.φ ) := by
  classical
  rw [RiemannUp_θφ_rφ_as_bracket]
  simp only [sumIdx_θrφ_left, sumIdx_θφr_right]

/-- Off‑block but shared‑φ: `R_{rφ θφ} = 0`. -/
@[simp] lemma R_rφ_θφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.θ Idx.φ = 0 := by
  classical
  -- Convert `RiemannUp` to your scalar bracket and use the bracket lemma.
  have hup0 :
      RiemannUp M r θ Idx.r Idx.φ Idx.θ Idx.φ = 0 := by
    rw [RiemannUp_rφ_θφ_as_bracket]
    exact bracket_rφ_θφ_scalar_zero M r θ
  -- Multiply by `g_rr` and finish.
  simp only [Riemann_contract_first, hup0, mul_zero]

/-- By last-pair antisymmetry: R_{rφ φθ} = 0. -/
lemma R_rφ_φθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.r Idx.φ Idx.φ Idx.θ = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_rφ_θφ_zero M r θ)

/-! ---------------------------------------------------------------------------
    Off-block vanishing for the (θ,φ) outer pair
--------------------------------------------------------------------------- -/

/-- Off-block: R_{θφ tr} = 0. -/
@[simp] lemma R_θφ_tr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.t Idx.r = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp [dCoord_t, dCoord_r, Γtot,
        Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ]

/-- By last-pair antisymmetry: R_{θφ rt} = 0. -/
lemma R_θφ_rt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.r Idx.t = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_θφ_tr_zero M r θ)

/-- Off-block: R_{θφ tθ} = 0. -/
@[simp] lemma R_θφ_tθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.t Idx.θ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp [dCoord_t, dCoord_θ, Γtot,
        Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ]

/-- By last-pair antisymmetry: R_{θφ θt} = 0. -/
lemma R_θφ_θt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.t = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_θφ_tθ_zero M r θ)

/-- Off-block: R_{θφ tφ} = 0. -/
@[simp] lemma R_θφ_tφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.t Idx.φ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp [dCoord_t, dCoord_φ, Γtot,
        Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ]

/-- By last-pair antisymmetry: R_{θφ φt} = 0. -/
lemma R_θφ_φt_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.φ Idx.t = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_θφ_tφ_zero M r θ)

/-- Off-block: R_{θφ rθ} = 0. -/
@[simp] lemma R_θφ_rθ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.r Idx.θ = 0 := by
  classical
  rw [Riemann_contract_first]; unfold RiemannUp
  simp only [dCoord_r, dCoord_θ, Γtot,
             Γ_t_tr, Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, Γ_r_φφ, Γ_φ_rφ, Γ_θ_φφ, Γ_φ_θφ,
             sumIdx_expand, g, deriv_const]
  norm_num

/-- By last-pair antisymmetry: R_{θφ θr} = 0. -/
lemma R_θφ_θr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.r = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_θφ_rθ_zero M r θ)

/-- The paired view is the same cancellation: `R_{θφ rφ} = 0`. -/
@[simp] lemma R_θφ_rφ_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.r Idx.φ = 0 := by
  classical
  have hup0 :
      RiemannUp M r θ Idx.θ Idx.φ Idx.r Idx.φ = 0 := by
    rw [RiemannUp_θφ_rφ_as_bracket_collapsed]
    exact bracket_θφ_rφ_scalar_zero M r θ
  simp only [Riemann_contract_first, hup0, mul_zero]

/-- By last-pair antisymmetry: R_{θφ φr} = 0. -/
lemma R_θφ_φr_zero (M r θ : ℝ) :
  Riemann M r θ Idx.θ Idx.φ Idx.φ Idx.r = 0 := by
  rw [Riemann_swap_c_d]; exact neg_eq_zero.mpr (R_θφ_rφ_zero M r θ)

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
  simp [Riemann, RiemannUp]
  -- Expand sumIdx_expand and evaluate each index
  simp [sumIdx_expand]
  -- Most terms vanish due to zero Christoffel symbols
  simp [Γtot, mul_eq_zero]
  -- The only non-zero contribution is from λ = r
  simp [g_tt, Γ_t_tr, Γ_r_φφ]
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
  simp only [sumIdx, Finset.mul_sum]

/-- Helper lemma for pulling a constant factor out of sumIdx2. -/
lemma sumIdx2_mul_left' (c : ℝ) (f : Idx → Idx → ℝ) :
    sumIdx2 (fun i j => c * f i j) = c * sumIdx2 f := by
  -- This follows directly from the robust implementation of sumIdx2_mul_const.
  -- Using 'exact' avoids the tactical issues encountered with 'rw' and 'simp only'.
  exact sumIdx2_mul_const c f

-- The _mul_left' versions already exist and work fine

/-- The inverse metric is diagonal for Schwarzschild spacetime. -/
lemma gInv_off_diagonal (M r θ : ℝ) (a b : Idx) (hab : a ≠ b) :
  gInv M a b r θ = 0 := by
  cases a <;> cases b <;> simp [gInv] at hab ⊢

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
  simp only [sumIdx2_expand]
  -- Expand and use diagonal structure of gInv
  cases a <;> cases b <;> simp [sumIdx_expand, gInv]
  <;> ring

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

/-! ### Ricci Contraction and Vanishing Theorem -/

/-- The Ricci tensor contraction: R_ab = ∑_ρ R^ρ_aρb -/
-- Ricci tensor: R_ab = Σ_ρ R^ρ_aρb (contraction of mixed Riemann)
noncomputable def RicciContraction (M r θ : ℝ) (a b : Idx) : ℝ :=
  sumIdx (fun ρ => RiemannUp M r θ ρ a ρ b)

/-! ### Off-diagonal Ricci: first=third pattern collapses by `simp` -/
section OffDiagonalRicci
open Idx

-- R_tr: expand over ρ, contract first index instantly, kill each mixed term locally
@[simp] lemma Ricci_offdiag_sum_tr (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.t ρ Idx.r) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]


-- R_tθ
@[simp] lemma Ricci_offdiag_sum_tθ (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.t ρ Idx.θ) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]


-- R_tφ
@[simp] lemma Ricci_offdiag_sum_tφ (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.t ρ Idx.φ) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]


-- R_rθ
@[simp] lemma Ricci_offdiag_sum_rθ (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.r ρ Idx.θ) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]


-- R_rφ
@[simp] lemma Ricci_offdiag_sum_rφ (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.r ρ Idx.φ) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]


-- R_θφ
@[simp] lemma Ricci_offdiag_sum_θφ (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.θ ρ Idx.φ) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]


end OffDiagonalRicci

/-! ### Mirror off-diagonal Ricci lemmas (swapped a ↔ b) -/
section OffDiagonalRicciMirror
open Idx

@[simp] lemma Ricci_offdiag_sum_rt (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.r ρ Idx.t) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]


@[simp] lemma Ricci_offdiag_sum_θt (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.θ ρ Idx.t) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]


@[simp] lemma Ricci_offdiag_sum_φt (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.φ ρ Idx.t) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]


@[simp] lemma Ricci_offdiag_sum_θr (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.θ ρ Idx.r) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]
  ring

@[simp] lemma Ricci_offdiag_sum_φr (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.φ ρ Idx.r) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]

@[simp] lemma Ricci_offdiag_sum_φθ (M r θ : ℝ) :
  sumIdx (fun ρ => RiemannUp M r θ ρ Idx.φ ρ Idx.θ) = 0 := by
  classical
  simp [sumIdx_expand]
  unfold RiemannUp dCoord Γtot
  simp [sumIdx_expand, g, dCoord_t, dCoord_φ, Γ_θ_rθ, Γ_φ_rφ, Γ_φ_θφ, Γ_θ_φφ, Γ_r_φφ, Γ_r_θθ, Γ_r_rr, Γ_r_tt]

end OffDiagonalRicciMirror

/-! ### Phase 1: Helper lemmas for component proofs -/

lemma r_mul_f (M r : ℝ) (hr_nz : r ≠ 0) : r * f M r = r - 2 * M := by
  unfold f
  field_simp [hr_nz]

lemma one_minus_f (M r : ℝ) : 1 - f M r = 2 * M / r := by
  unfold f
  ring

lemma sub_twoM_ne_zero_of_exterior (M r : ℝ) (hr_ex : 2 * M < r) : r - M * 2 ≠ 0 := by
  linarith

/-! ### Phase 2: Schwarzschild Riemann component lemmas -/

/-- Component: R_trtr = -2M/r³ -/
lemma Riemann_trtr_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.r Idx.t Idx.r = -2 * M / r ^ 3 := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)
  have hsub_nz : r - 2 * M ≠ 0 := by
    have : 0 < r - 2 * M := sub_pos.mpr hr_ex
    exact ne_of_gt this

  -- Contract first index and expand (only case needing derivative calculators)
  rw [Riemann_contract_first M r θ Idx.t Idx.r Idx.t Idx.r]
  unfold RiemannUp
  simp [g, dCoord_t, dCoord_r, sumIdx_expand, Γtot]

  -- Apply derivative calculators
  have hder_tr := deriv_Γ_t_tr_at M r hr_nz hf_nz
  have hder_rr := deriv_Γ_r_rr_at M r hr_nz hf_nz
  simp [hder_tr, hder_rr]

  -- Expand the Γ symbols (keep f unexpanded)
  simp [Γ_t_tr, Γ_r_rr, g]

  -- Simplify directly with field_simp - the hsub_nz hypothesis lets it clear (r-2M)⁻¹ terms
  field_simp [hr_nz, hsub_nz]
  ring

/-- Component: R_tθtθ = M·f(r)/r -/
lemma Riemann_tθtθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M * f M r / r := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  -- Step 1: Structural Expansion
  rw [Riemann_contract_first M r θ Idx.t Idx.θ Idx.t Idx.θ]
  unfold RiemannUp
  simp only [dCoord_t, dCoord_θ, sumIdx_expand, Γtot, g]

  -- Step 2: Handle derivatives
  simp only [deriv_const']

  -- Step 3: Expand Γ symbols
  simp only [Γ_t_tr, Γ_r_θθ]

  -- Step 4: Algebraic closure using Junior Prof's 3-step pattern (Plan D)
  -- Nonzero of r - 2M in the exterior
  have hsub_nz : r - 2 * M ≠ 0 := by
    have : 0 < r - 2 * M := sub_pos.mpr hr_ex
    exact ne_of_gt this

  -- Step D1: Factor one denominator
  have hfactor :
    -(r * M ^ 2 * (r - 2 * M)⁻¹ * 4)
    + r ^ 2 * M * (r - 2 * M)⁻¹
    + M ^ 3 * (r - 2 * M)⁻¹ * 4
    =
    (r - 2 * M)⁻¹ * (r ^ 2 * M - 4 * r * M ^ 2 + 4 * M ^ 3) := by
    ring

  -- Step D2: Numerator factorization
  have hpoly :
    r ^ 2 * M - 4 * r * M ^ 2 + 4 * M ^ 3
      = (r * M - 2 * M ^ 2) * (r - 2 * M) := by
    ring

  -- Step D3: Cancel (r - 2M) with its inverse
  have hcancel :
    (r - 2 * M)⁻¹ * ((r * M - 2 * M ^ 2) * (r - 2 * M))
      = (r * M - 2 * M ^ 2) := by
    field_simp [hsub_nz]

  -- Combine and close
  have :
    -(r * M ^ 2 * (r - 2 * M)⁻¹ * 4)
    + r ^ 2 * M * (r - 2 * M)⁻¹
    + M ^ 3 * (r - 2 * M)⁻¹ * 4
    = r * M - 2 * M ^ 2 := by
    calc
      -(r * M ^ 2 * (r - 2 * M)⁻¹ * 4)
        + r ^ 2 * M * (r - 2 * M)⁻¹
        + M ^ 3 * (r - 2 * M)⁻¹ * 4
          = (r - 2 * M)⁻¹ * (r ^ 2 * M - 4 * r * M ^ 2 + 4 * M ^ 3) := hfactor
      _   = (r - 2 * M)⁻¹ * ((r * M - 2 * M ^ 2) * (r - 2 * M)) := by
              rw [hpoly]
      _   = (r * M - 2 * M ^ 2) := hcancel

  -- Final cleanup to match RHS form (M * f M r / r)
  simp only [f, div_eq_mul_inv]
  field_simp [hr_nz]
  simpa using this

/-- Component: R_tφtφ = M·f(r)·sin²θ/r -/
lemma Riemann_tφtφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ = M * f M r * Real.sin θ ^ 2 / r := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)

  -- Contract and expand (no derivatives)
  rw [Riemann_contract_first M r θ Idx.t Idx.φ Idx.t Idx.φ]
  unfold RiemannUp
  simp [g, dCoord_t, dCoord_φ, sumIdx_expand, Γtot]

  -- Expand Γ symbols (keep f unexpanded)
  simp [Γ_t_tr, Γ_r_φφ, Γ_r_rr, g]

  -- Clear denominators directly - hsub_nz lets field_simp handle (r-2M)⁻¹ terms
  have hsub_nz : r - 2 * M ≠ 0 := by
    have : 0 < r - 2 * M := sub_pos.mpr hr_ex
    exact ne_of_gt this
  field_simp [hr_nz, hsub_nz]
  simp only [f]
  field_simp [hr_nz]
  ring

/-- Component: R_rθrθ = -M/(r·f(r)) -/
lemma Riemann_rθrθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.r Idx.θ Idx.r Idx.θ = -M / (r * f M r) := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)
  have hsub_nz := sub_twoM_ne_zero_of_exterior M r hr_ex

  -- Contract and expand (∂ᵣΓʳ_θθ is just -1, no calculator needed)
  rw [Riemann_contract_first M r θ Idx.r Idx.θ Idx.r Idx.θ]
  unfold RiemannUp
  simp [g, dCoord_r, dCoord_θ, sumIdx_expand, Γtot]

  -- Expand Γ symbols (keep f unexpanded)
  simp [Γ_r_θθ, Γ_r_rr, Γ_θ_rθ, g]

  -- Clear denominators directly
  have hsub_nz : r - 2 * M ≠ 0 := by
    have : 0 < r - 2 * M := sub_pos.mpr hr_ex
    exact ne_of_gt this
  field_simp [hr_nz, hsub_nz]
  simp only [f]
  field_simp [hr_nz]
  ring

/-- Component: R_rφrφ = -M·sin²θ/(r·f(r)) -/
lemma Riemann_rφrφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    Riemann M r θ Idx.r Idx.φ Idx.r Idx.φ = -M * Real.sin θ ^ 2 / (r * f M r) := by
  classical
  have hr_nz : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex
  have hf_nz : f M r ≠ 0 := ne_of_gt (f_pos_of_hr M r hM hr_ex)
  have hsub_nz := sub_twoM_ne_zero_of_exterior M r hr_ex

  -- Contract and expand (∂ᵣΓʳ_φφ is just -sin²θ, no calculator needed)
  rw [Riemann_contract_first M r θ Idx.r Idx.φ Idx.r Idx.φ]
  unfold RiemannUp
  simp [g, dCoord_r, dCoord_φ, sumIdx_expand, Γtot]

  -- Expand Γ symbols (keep f unexpanded)
  simp [Γ_r_φφ, Γ_r_rr, Γ_φ_rφ, g]

  -- Clear denominators directly
  have hsub_nz : r - 2 * M ≠ 0 := by
    have : 0 < r - 2 * M := sub_pos.mpr hr_ex
    exact ne_of_gt this
  field_simp [hr_nz, hsub_nz]
  simp only [f]
  field_simp [hr_nz]
  ring

/-- Cross-multiplied identity: valid at all angles including poles.
    Avoids evaluating Γ^φ_θφ = cot θ at θ = 0, π by using metric compatibility. -/
lemma Riemann_θφθφ_cross (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
    g M Idx.φ Idx.φ r θ * Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.φ
    =
    (2 * M * r * Real.sin θ ^ 2) * g M Idx.φ Idx.φ r θ := by
  classical
  have hr_ne : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex

  -- Contract first index (ρ = θ only survives), then expand RiemannUp for (θ,φ,θ,φ)
  -- and push the scalar g_{φφ} inside.
  simp [Riemann_contract_first, RiemannUp, g, Γtot, sumIdx_expand]

  -- Expand Christoffel symbols (but not Γ_φ_θφ yet - it's singular!)
  simp [Γ_θ_rθ, Γ_r_φφ, Γ_θ_φφ, deriv_Γ_θ_φφ_at]

  -- Clear r⁻¹ terms
  field_simp [hr_ne]

  -- Expand Γ_φ_θφ = cosθ/sinθ
  -- The product Γ_θ_φφ · Γ_φ_θφ = (-sin θ·cos θ)·(cos θ/sin θ) = -cos²θ cancels properly
  simp only [Γ_φ_θφ]

  -- Handle both cases: sinθ = 0 (both sides = 0) and sinθ ≠ 0 (cancel division)
  by_cases hs : Real.sin θ = 0
  · -- On axis: g_φφ = r²·sin²θ = 0, so both sides = 0
    simp [hs, pow_two]
  · -- Off axis: can cancel sin θ⁻¹
    field_simp [hs]
    ring

/-- Component: R_θφθφ = 2Mr·sin²θ (off-axis, where sin θ ≠ 0). -/
lemma Riemann_θφθφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) (hsin : Real.sin θ ≠ 0) :
    Riemann M r θ Idx.θ Idx.φ Idx.θ Idx.φ = 2 * M * r * Real.sin θ ^ 2 := by
  classical
  have hr_ne : r ≠ 0 := r_ne_zero_of_exterior M r hM hr_ex

  -- Use the cross-multiplied identity and cancel g_φφ (which is nonzero off-axis)
  have hgφφ_ne : g M Idx.φ Idx.φ r θ ≠ 0 := by
    simp [g, pow_two, hsin, hr_ne]

  have H := Riemann_θφθφ_cross M r θ hM hr_ex

  -- Rearrange and cancel
  exact mul_left_cancel₀ hgφφ_ne (by simpa [mul_comm, mul_left_comm, mul_assoc] using H)

/-- Main theorem: Ricci tensor vanishes in the Schwarzschild exterior -/
theorem Ricci_zero_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (h_sin_nz : Real.sin θ ≠ 0) :
    ∀ a b, RicciContraction M r θ a b = 0 := by
  intro a b
  unfold RicciContraction

  -- Extract hypotheses
  have hM := h_ext.hM
  have hr_ex := h_ext.hr_ex
  have hr_nz : r ≠ 0 := by linarith [hM, hr_ex]

  -- Case split on 16 Ricci components
  cases a <;> cases b

  -- Off-diagonal cases (12 cases)
  case t.r => exact Ricci_offdiag_sum_tr M r θ
  case t.θ => exact Ricci_offdiag_sum_tθ M r θ
  case t.φ => exact Ricci_offdiag_sum_tφ M r θ

  case r.t => exact Ricci_offdiag_sum_rt M r θ
  case r.θ => exact Ricci_offdiag_sum_rθ M r θ
  case r.φ => exact Ricci_offdiag_sum_rφ M r θ

  case θ.t => exact Ricci_offdiag_sum_θt M r θ
  case θ.r => exact Ricci_offdiag_sum_θr M r θ
  case θ.φ => exact Ricci_offdiag_sum_θφ M r θ

  case φ.t => exact Ricci_offdiag_sum_φt M r θ
  case φ.r => exact Ricci_offdiag_sum_φr M r θ
  case φ.θ => exact Ricci_offdiag_sum_φθ M r θ

  -- Diagonal cases (4 cases) - Component cancellation
  -- Components are NON-ZERO but algebraically cancel when summed
  case t.t =>
    convert Ricci_tt_cancellation M r θ h_ext using 2
    simp [sumIdx_expand]
  case r.r =>
    convert Ricci_rr_cancellation M r θ h_ext h_sin_nz using 2
    simp [sumIdx_expand]
  case θ.θ =>
    convert Ricci_θθ_cancellation M r θ h_ext h_sin_nz using 2
    simp [sumIdx_expand]
  case φ.φ =>
    convert Ricci_φφ_cancellation M r θ h_ext h_sin_nz using 2
    simp [sumIdx_expand]

end RicciInfrastructure

end Schwarzschild
end Papers.P5_GeneralRelativity
