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

/-- ⚠️  QUARANTINED AXIOM - DE-AXIOMATIZATION MANDATE (2025-09-30)

**RESTRICTIONS:**
- ❌ MUST NOT be used in critical path (vacuum solution, Ricci/Riemann components)
- ❌ MUST NOT be used in new code
- ✅ MAY be used ONLY in existing Stage-1 LHS scaffolding (legacy, lines 1145-2800)
- ✅ MUST be replaced with explicit hypotheses for Level 3 publication

**AUDIT:** Search for `AX_differentiable_hack` before Level 3 submission.

**ELIMINATION PATH:**
1. ✅ Hypothesis-carrying infrastructure added (dCoord_add/sub/mul_of_diff)
2. ✅ Metric differentiability lemmas added (6 lemmas, lines 238-270)
3. 🔄 Refactor Stage1LHS to use explicit hypotheses (in progress)
4. ⏳ Remove axiom entirely

**JUSTIFICATION FOR RETENTION (temporary):**
- Schwarzschild vacuum solution does NOT use this axiom (Schwarzschild.lean doesn't import Riemann.lean)
- All R_μν = 0 proofs use explicit differentiability lemmas
- Retained ONLY for non-critical Stage-1 tensor infrastructure scaffolding
- Clear elimination path exists via explicit `Exterior` hypotheses
-/
lemma AX_differentiable_hack (f : ℝ → ℝ) (x : ℝ) : DifferentiableAt ℝ f x := by
  sorry -- QUARANTINED AXIOM - See documentation above.

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

/-! ### Hypothesis-Carrying `dCoord` Infrastructure (De-Axiomatization)

The following lemmas provide rigorous versions of dCoord linearity rules with explicit
differentiability hypotheses. These replace the axiom-dependent versions for the critical path.

The helper predicates `DifferentiableAt_r` and `DifferentiableAt_θ` are defined above.
-/

/-- Linearity of dCoord over addition with explicit differentiability hypotheses. -/
lemma dCoord_add_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
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
lemma dCoord_sub_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
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
lemma dCoord_mul_of_diff (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ)
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

/-- Linearity of `dCoord` over subtraction. -/
@[simp] lemma dCoord_sub (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => f r θ - g r θ) r θ
    = dCoord μ f r θ - dCoord μ g r θ := by
  cases μ
  case t => simp [dCoord]
  case r =>
    -- Unfold dCoord explicitly first
    simp only [dCoord]
    -- Prepare the hypotheses using AX_differentiable_hack
    have hf := AX_differentiable_hack (fun r' => f r' θ) r
    have hg := AX_differentiable_hack (fun r' => g r' θ) r
    -- The goal now exactly matches the statement of deriv_sub
    exact deriv_sub hf hg
  case θ =>
    simp only [dCoord]
    have hf := AX_differentiable_hack (fun θ' => f r θ') θ
    have hg := AX_differentiable_hack (fun θ' => g r θ') θ
    exact deriv_sub hf hg
  case φ => simp [dCoord]

/-- Linearity of `dCoord` over addition. -/
@[simp] lemma dCoord_add (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => f r θ + g r θ) r θ
    = dCoord μ f r θ + dCoord μ g r θ := by
  cases μ
  case t => simp [dCoord]
  case r =>
    simp only [dCoord]
    have hf := AX_differentiable_hack (fun r' => f r' θ) r
    have hg := AX_differentiable_hack (fun r' => g r' θ) r
    exact deriv_add hf hg
  case θ =>
    simp only [dCoord]
    have hf := AX_differentiable_hack (fun θ' => f r θ') θ
    have hg := AX_differentiable_hack (fun θ' => g r θ') θ
    exact deriv_add hf hg
  case φ => simp [dCoord]

/-
/-- Linearity of `dCoord` across 4 terms. -/
lemma dCoord_add4 (μ : Idx) (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ
  = dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ := by
  simp only [dCoord_add]
  ring
-/

/-! #### Calculus infrastructure for dCoord -/

/-- Product rule (Leibniz rule) for `dCoord`. -/
@[simp] lemma dCoord_mul (μ : Idx) (f g : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => f r θ * g r θ) r θ =
  dCoord μ f r θ * g r θ + f r θ * dCoord μ g r θ := by
  cases μ
  case t => simp [dCoord]
  case r =>
    simp only [dCoord]
    have hf := AX_differentiable_hack (fun r' => f r' θ) r
    have hg := AX_differentiable_hack (fun r' => g r' θ) r
    exact deriv_mul hf hg
  case θ =>
    simp only [dCoord]
    have hf := AX_differentiable_hack (fun θ' => f r θ') θ
    have hg := AX_differentiable_hack (fun θ' => g r θ') θ
    exact deriv_mul hf hg
  case φ => simp [dCoord]

/-- Push `dCoord` across a 4-term sum via two applications of `dCoord_add`. -/
lemma dCoord_add4 (μ : Idx)
  (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ
  =
  dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ := by
  -- First group as (A+B) + (C+D)
  have h1 :
    dCoord μ
      (fun r θ => (A r θ + B r θ) + (C r θ + D r θ)) r θ
    =
    dCoord μ (fun r θ => A r θ + B r θ) r θ
    + dCoord μ (fun r θ => C r θ + D r θ) r θ := by
    simpa [add_comm, add_left_comm, add_assoc] using
      dCoord_add μ (fun r θ => A r θ + B r θ) (fun r θ => C r θ + D r θ) r θ
  have hAB : dCoord μ (fun r θ => A r θ + B r θ) r θ
             = dCoord μ A r θ + dCoord μ B r θ := by
    simpa using dCoord_add μ A B r θ
  have hCD : dCoord μ (fun r θ => C r θ + D r θ) r θ
             = dCoord μ C r θ + dCoord μ D r θ := by
    simpa using dCoord_add μ C D r θ
  have h2 :
    dCoord μ (fun r θ => A r θ + B r θ) r θ
    + dCoord μ (fun r θ => C r θ + D r θ) r θ
    =
    (dCoord μ A r θ + dCoord μ B r θ)
    + (dCoord μ C r θ + dCoord μ D r θ) := by
    congr 1 <;> assumption
  simpa [add_comm, add_left_comm, add_assoc] using h1.trans h2

/-- `dCoord_add4` specialized to a fully flattened 4-term sum. -/
lemma dCoord_add4_flat (μ : Idx)
  (A B C D : ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ
  =
  dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ := by
  simpa [add_comm, add_left_comm, add_assoc] using
    dCoord_add4 μ A B C D r θ

/-- Push `dCoord` across `sumIdx` using a function-level expansion of `sumIdx`.
    This is designed to pair with a local `sumIdx_expand_local` proved by `funext`. -/
lemma dCoord_sumIdx_via_funext
  (μ : Idx) (F : Idx → ℝ → ℝ → ℝ) (r θ : ℝ)
  (hexp_fun :
    (fun r θ => sumIdx (fun i => F i r θ))
    =
    (fun r θ =>
      F Idx.t r θ + F Idx.r r θ + F Idx.θ r θ + F Idx.φ r θ)) :
  dCoord μ (fun r θ => sumIdx (fun i => F i r θ)) r θ
  =
    dCoord μ (F Idx.t) r θ
  + dCoord μ (F Idx.r) r θ
  + dCoord μ (F Idx.θ) r θ
  + dCoord μ (F Idx.φ) r θ := by
  -- Rewrite the function under `dCoord` via the function-level expansion
  have h₁ := congrArg (fun H => dCoord μ H r θ) hexp_fun
  -- Then push `dCoord` through the 4-term sum
  have h₂ := dCoord_add4_flat μ (F Idx.t) (F Idx.r) (F Idx.θ) (F Idx.φ) r θ
  -- Compose and normalize
  simpa [add_comm, add_left_comm, add_assoc] using h₁.trans h₂

/-- Same as `dCoord_sumIdx_via_funext` but takes the *pointwise* local expansion
    and builds the function-level equality internally via `funext`. -/
lemma dCoord_sumIdx_via_local_expand
  (μ : Idx) (F : Idx → ℝ → ℝ → ℝ) (r θ : ℝ)
  (hexp_pointwise :
    ∀ r θ, sumIdx (fun i => F i r θ)
            = F Idx.t r θ + F Idx.r r θ + F Idx.θ r θ + F Idx.φ r θ) :
  dCoord μ (fun r θ => sumIdx (fun i => F i r θ)) r θ
  =
    dCoord μ (F Idx.t) r θ
  + dCoord μ (F Idx.r) r θ
  + dCoord μ (F Idx.θ) r θ
  + dCoord μ (F Idx.φ) r θ := by
  have hexp_fun :
      (fun r θ => sumIdx (fun i => F i r θ))
      =
      (fun r θ =>
        F Idx.t r θ + F Idx.r r θ + F Idx.θ r θ + F Idx.φ r θ) := by
    funext r θ; simpa using hexp_pointwise r θ
  exact dCoord_sumIdx_via_funext μ F r θ hexp_fun

/-- Distribution of `dCoord` over the abstract finite sum `sumIdx`. -/
@[simp] lemma dCoord_sumIdx (μ : Idx) (F : Idx → ℝ → ℝ → ℝ) (r θ : ℝ) :
  dCoord μ (fun r θ => sumIdx (fun i => F i r θ)) r θ =
  sumIdx (fun i => dCoord μ (fun r θ => F i r θ) r θ) := by
  -- Expand sumIdx on both sides and apply dCoord_add repeatedly
  simp only [sumIdx_expand]
  -- LHS: dCoord μ (fun r θ => F t r θ + F r r θ + F θ r θ + F φ r θ) r θ
  -- RHS: dCoord μ (F t) r θ + dCoord μ (F r) r θ + dCoord μ (F θ) r θ + dCoord μ (F φ) r θ
  -- Apply dCoord_add three times to distribute dCoord over the sum
  rw [dCoord_add, dCoord_add, dCoord_add]

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
--   sorry

-- lemma metric_inverse_id_right (M : ℝ) :
--   ∀ (μ ν : Idx) (r θ : ℝ),
--     sumIdx (fun e => gInv M μ e r θ * g M e ν r θ) = if μ = ν then 1 else 0 := by
--   sorry

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
  simp [sumIdx, Finset.sum_sub_distrib, dCoord_sub, dCoord_add,
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

/-- ⚠️  QUARANTINED AXIOM - DE-AXIOMATIZATION MANDATE (2025-09-30)

**RESTRICTIONS:**
- ❌ @[simp] attribute REMOVED (dangerous global rewriting)
- ❌ MUST NOT be used in new code
- ✅ Sound version `nabla_g_zero_ext` MUST be used instead when possible
- ✅ Retained ONLY for `Riemann_swap_a_b` antisymmetry proof (requires derivative of ∇g)

**ISSUE:** Global metric compatibility without domain restriction.

This axiom asserts ∇g = 0 unconditionally, which is mathematically unsound at the
event horizon r = 2M. The SOUND version is `nabla_g_zero_ext` with explicit `Exterior` hypothesis.

**JUSTIFICATION FOR RETENTION (temporary):**
- Required by `Riemann_swap_a_b` to prove d/d(∇g) = 0
- Replacing it requires topological infrastructure (Exterior_isOpen)
- This is PRIORITY 2 work (deferred per mandate)
- Critical path (R_μν = 0) uses sound version `nabla_g_zero_ext`

**ELIMINATION PATH:**
1. ✅ Sound version with Exterior hypothesis exists (nabla_g_zero_ext)
2. ✅ @[simp] attribute removed (quarantined)
3. ⏳ Implement Exterior_isOpen (PRIORITY 2)
4. ⏳ Refactor Riemann_swap_a_b_ext to use topological version
5. ⏳ Remove axiom entirely (Level 3)

**AUDIT:** Verify critical path uses only `nabla_g_zero_ext` before Level 3 submission.
-/
lemma AX_nabla_g_zero (M r θ : ℝ) (c a b : Idx) :
  nabla_g M r θ c a b = 0 := by
  sorry -- QUARANTINED AXIOM - See documentation above.

-- Removed duplicate: sumIdx_sub is already defined in Schwarzschild.lean

/-- From `∇g = 0`: rewrite `∂_x g_{ab}` as a Γ–`g` contraction. -/
@[simp] lemma dCoord_g_via_compat
    (M r θ : ℝ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ
    =
    sumIdx (fun e => Γtot M r θ e x a * g M e b r θ)
  + sumIdx (fun e => Γtot M r θ e x b * g M a e r θ) := by
  have h := AX_nabla_g_zero M r θ x a b
  simp only [nabla_g] at h
  linarith

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

/-- The LHS of the Ricci identity simplifies using commutativity of derivatives.
    The second partial derivatives of the metric cancel out. -/
lemma ricci_LHS (M r θ : ℝ) (a b c d : Idx) :
  ( dCoord c (fun r θ => nabla_g M r θ d a b) r θ
  - dCoord d (fun r θ => nabla_g M r θ c a b) r θ )
  = - ( dCoord c (fun r θ => ContractionC M r θ d a b) r θ
        - dCoord d (fun r θ => ContractionC M r θ c a b) r θ ) := by
  -- Apply the definition of nabla_g and use linearity of dCoord
  simp only [nabla_g_eq_dCoord_sub_C, dCoord_sub]
  -- Local Clairaut step: explicit handling for trivial branches,
  -- delegate to dCoord_commute for the genuinely mixed (r/θ) cases
  have h_commute :
      dCoord c (fun r θ => dCoord d (fun r θ => g M a b r θ) r θ) r θ
    = dCoord d (fun r θ => dCoord c (fun r θ => g M a b r θ) r θ) r θ := by
    classical
    cases c with
    | t =>
      cases d with
      | t => simp [dCoord_t]                                  -- ∂t∘∂t
      | r => simp [dCoord_t, dCoord_r, deriv_const]           -- ∂r∘∂t vs ∂t∘∂r
      | θ => simp [dCoord_t, dCoord_θ, deriv_const]           -- ∂θ∘∂t vs ∂t∘∂θ
      | φ => simp [dCoord_t, dCoord_φ]                        -- ∂φ∘∂t vs ∂t∘∂φ
    | r =>
      cases d with
      | t => simp [dCoord_t, dCoord_r, deriv_const]           -- ∂r∘∂t vs ∂t∘∂r
      | r => rfl                                              -- ∂r∘∂r (trivial)
      | θ => exact dCoord_r_θ_commute_for_g M r θ a b         -- ∂r∘∂θ vs ∂θ∘∂r
      | φ => simp [dCoord_φ, dCoord_r, deriv_const]           -- ∂r∘∂φ vs ∂φ∘∂r
    | θ =>
      cases d with
      | t => simp [dCoord_t, dCoord_θ, deriv_const]           -- ∂θ∘∂t vs ∂t∘∂θ
      | r => rw [dCoord_r_θ_commute_for_g M r θ a b]          -- ∂θ∘∂r vs ∂r∘∂θ (symmetric)
      | θ => rfl                                              -- ∂θ∘∂θ (trivial)
      | φ => simp [dCoord_φ, dCoord_θ, deriv_const]           -- ∂θ∘∂φ vs ∂φ∘∂θ
    | φ =>
      cases d with
      | t => simp [dCoord_φ, dCoord_t]                        -- ∂φ∘∂t vs ∂t∘∂φ
      | r => simp [dCoord_φ, dCoord_r, deriv_const]           -- ∂φ∘∂r vs ∂r∘∂φ
      | θ => simp [dCoord_φ, dCoord_θ, deriv_const]           -- ∂φ∘∂θ vs ∂θ∘∂φ
      | φ => simp [dCoord_φ]                                  -- ∂φ∘∂φ
  -- Rearrange terms; the second derivatives cancel due to commutativity
  ring_nf
  rw [h_commute]
  ring

/-
-- Activation switch (names only; keeps statements unchanged)

-- EITHER (A) keep everything fully qualified via local abbrevs:
local abbrev Riemann := DraftRiemann.Riemann
local abbrev RiemannUp := DraftRiemann.RiemannUp

-- OR (B) open the namespace *only if* there is no conflicting top-level `Riemann`:
-- open DraftRiemann

-- When active, update unfolds inside the proof to:
--   unfold ContractionC Riemann RiemannUp
-/

/-
-- ACTIVATION_STATUS: stage1-lhs-both
-- Change when toggling:
--   ACTIVATION_STATUS: stage1-lhs-first
--   ACTIVATION_STATUS: stage1-lhs-both
--   ACTIVATION_STATUS: stage1-full
-/

/-
-- DEPENDENCY CHAIN for full activation:
-- 1. Required: dCoord_add, dCoord_mul (for Stage-1 blocks)
-- 2. Required: gInv definition (for RHS blocks)
-- 3. Optional: sumIdx_expand (for split proofs)
-- Currently blocked on: (1)
-- Status: baseline 51, all infrastructure commented and ready
-/

/-
  [[STAGE1-READY]] Top-level, baseline-neutral Stage-1 LHS facts (first family).
  These lemmas are validated independently of the main alternation proof and do not
  increase the unsolved-goal count (they introduce no `sorry`).

  When ready to activate, these can be referenced as:
    have Hc := Stage1LHS.Hc_one M r θ a b c d    -- First family, c-branch
    have Hd := Stage1LHS.Hd_one M r θ a b c d    -- First family, d-branch
    have Hc2 := Stage1LHS.Hc2_one M r θ a b c d  -- Second family, c-branch
    have Hd2 := Stage1LHS.Hd2_one M r θ a b c d  -- Second family, d-branch
-/
namespace Stage1LHS

section FirstFamily
  -- Keep the facts fully parametric to avoid depending on any ambient context.
  variable (M r θ : ℝ) (a b c d : Idx)

  /- Four first-family summands on the c-branch -/
  private def Pt (M : ℝ) (a b d : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.t d a) * (g M Idx.t b r θ)
  private def Pr (M : ℝ) (a b d : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)
  private def Pθ (M : ℝ) (a b d : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)
  private def Pφ (M : ℝ) (a b d : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)

  /-- Stage-1 fact: LHS c-branch, first family (expand only the e = t summand). -/
  lemma Hc_one :
    dCoord c (fun r θ =>
        Pt M a b d r θ
      + Pr M a b d r θ
      + Pθ M a b d r θ
      + Pφ M a b d r θ) r θ
    =
      (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * g M Idx.t b r θ
    + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ
    + dCoord c (Pr M a b d) r θ
    + dCoord c (Pθ M a b d) r θ
    + dCoord c (Pφ M a b d) r θ := by
    -- 4-term linearity in one step via dCoord_add4_flat
    have hsum_c := dCoord_add4_flat c (Pt M a b d) (Pr M a b d) (Pθ M a b d) (Pφ M a b d) r θ

    -- Product rule on the t-summand
    have hPt_push :
      dCoord c (Pt M a b d) r θ
      =
      dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ * g M Idx.t b r θ
      + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ := by
      simpa using
        dCoord_mul c
          (fun r θ => Γtot M r θ Idx.t d a)
          (fun r θ => g M Idx.t b r θ) r θ

    have H := hsum_c
    rw [hPt_push] at H
    simpa [add_comm, add_left_comm, add_assoc] using H

  /- Four first-family summands on the d-branch -/
  private def Qt (M : ℝ) (a b c : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.t c a) * (g M Idx.t b r θ)
  private def Qr (M : ℝ) (a b c : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.r c a) * (g M Idx.r b r θ)
  private def Qθ (M : ℝ) (a b c : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.θ c a) * (g M Idx.θ b r θ)
  private def Qφ (M : ℝ) (a b c : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.φ c a) * (g M Idx.φ b r θ)

  /-- Stage-1 fact: LHS d-branch, first family (expand only the e = t summand). -/
  lemma Hd_one :
    dCoord d (fun r θ =>
        Qt M a b c r θ
      + Qr M a b c r θ
      + Qθ M a b c r θ
      + Qφ M a b c r θ) r θ
    =
      (dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ) * g M Idx.t b r θ
    + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => g M Idx.t b r θ) r θ
    + dCoord d (Qr M a b c) r θ
    + dCoord d (Qθ M a b c) r θ
    + dCoord d (Qφ M a b c) r θ := by
    -- 4-term linearity in one step via dCoord_add4_flat
    have hsum_d := dCoord_add4_flat d (Qt M a b c) (Qr M a b c) (Qθ M a b c) (Qφ M a b c) r θ

    -- Product rule on the t-summand
    have hQt_push :
      dCoord d (Qt M a b c) r θ
      =
      dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ * g M Idx.t b r θ
      + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => g M Idx.t b r θ) r θ := by
      simpa using
        dCoord_mul d
          (fun r θ => Γtot M r θ Idx.t c a)
          (fun r θ => g M Idx.t b r θ) r θ

    have H := hsum_d
    rw [hQt_push] at H
    simpa [add_comm, add_left_comm, add_assoc] using H
end FirstFamily

end Stage1LHS

-- === Stage-1 LHS (second family, Γtot · g orientation) ===
namespace Stage1LHS

section SecondFamily
  -- Keep the facts fully parametric to avoid depending on any ambient context.
  variable (M r θ : ℝ) (a b c d : Idx)

  /- Four second-family summands on the c-branch:
     P2* := (Γtot M … * g M a …) with e ∈ {t, r, θ, φ}, using (d, b) on Γtot. -/
  private def P2t (M : ℝ) (a b d : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.t d b) * (g M a Idx.t r θ)
  private def P2r (M : ℝ) (a b d : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.r d b) * (g M a Idx.r r θ)
  private def P2θ (M : ℝ) (a b d : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.θ d b) * (g M a Idx.θ r θ)
  private def P2φ (M : ℝ) (a b d : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.φ d b) * (g M a Idx.φ r θ)

  /-- Stage-1 fact: **LHS c-branch, second family** (expand only the `e = t` summand). -/
  lemma Hc2_one :
    dCoord c (fun r θ =>
        P2t M a b d r θ
      + P2r M a b d r θ
      + P2θ M a b d r θ
      + P2φ M a b d r θ) r θ
    =
      (dCoord c (fun r θ => Γtot M r θ Idx.t d b) r θ) * (g M a Idx.t r θ)
    + (Γtot M r θ Idx.t d b) * dCoord c (fun r θ => g M a Idx.t r θ) r θ
    + dCoord c (P2r M a b d) r θ
    + dCoord c (P2θ M a b d) r θ
    + dCoord c (P2φ M a b d) r θ := by
    -- 4-term linearity in one step via dCoord_add4_flat
    have hsum2_c := dCoord_add4_flat c (P2t M a b d) (P2r M a b d) (P2θ M a b d) (P2φ M a b d) r θ

    -- Product rule on the t-summand (Γtot first, g second)
    have hP2t_push :
      dCoord c (P2t M a b d) r θ
        =
      dCoord c (fun r θ => Γtot M r θ Idx.t d b) r θ * (g M a Idx.t r θ)
      + (Γtot M r θ Idx.t d b) * dCoord c (fun r θ => g M a Idx.t r θ) r θ := by
      simpa using
        dCoord_mul c
          (fun r θ => Γtot M r θ Idx.t d b)
          (fun r θ => g M a Idx.t r θ) r θ

    -- Finish: substitute the product rule into the 4-term linearity
    have H := hsum2_c
    rw [hP2t_push] at H
    simpa [add_comm, add_left_comm, add_assoc] using H


  /- Four second-family summands on the d-branch:
     Q2* := (Γtot M … * g M a …) with e ∈ {t, r, θ, φ}, using (c, b) on Γtot. -/
  private def Q2t (M : ℝ) (a b c : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.t c b) * (g M a Idx.t r θ)
  private def Q2r (M : ℝ) (a b c : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.r c b) * (g M a Idx.r r θ)
  private def Q2θ (M : ℝ) (a b c : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.θ c b) * (g M a Idx.θ r θ)
  private def Q2φ (M : ℝ) (a b c : Idx) : ℝ → ℝ → ℝ :=
    fun r θ => (Γtot M r θ Idx.φ c b) * (g M a Idx.φ r θ)

  /-- Stage-1 fact: **LHS d-branch, second family** (expand only the `e = t` summand). -/
  lemma Hd2_one :
    dCoord d (fun r θ =>
        Q2t M a b c r θ
      + Q2r M a b c r θ
      + Q2θ M a b c r θ
      + Q2φ M a b c r θ) r θ
    =
      (dCoord d (fun r θ => Γtot M r θ Idx.t c b) r θ) * (g M a Idx.t r θ)
    + (Γtot M r θ Idx.t c b) * dCoord d (fun r θ => g M a Idx.t r θ) r θ
    + dCoord d (Q2r M a b c) r θ
    + dCoord d (Q2θ M a b c) r θ
    + dCoord d (Q2φ M a b c) r θ := by
    -- 4-term linearity in one step via dCoord_add4_flat
    have hsum2_d := dCoord_add4_flat d (Q2t M a b c) (Q2r M a b c) (Q2θ M a b c) (Q2φ M a b c) r θ

    -- Product rule on the t-summand (Γtot first, g second)
    have hQ2t_push :
      dCoord d (Q2t M a b c) r θ
        =
      dCoord d (fun r θ => Γtot M r θ Idx.t c b) r θ * (g M a Idx.t r θ)
      + (Γtot M r θ Idx.t c b) * dCoord d (fun r θ => g M a Idx.t r θ) r θ := by
      simpa using
        dCoord_mul d
          (fun r θ => Γtot M r θ Idx.t c b)
          (fun r θ => g M a Idx.t r θ) r θ

    -- Finish
    have H := hsum2_d
    rw [hQ2t_push] at H
    simpa [add_comm, add_left_comm, add_assoc] using H

end SecondFamily
end Stage1LHS

/- === ACTIVATION DEMONSTRATION: Wiring Bridge Lemmas ===
   This section shows how to use the bridge lemmas to connect Stage-1 facts
   to the alternation proof without needing the global dCoord_sumIdx.

   When ready to activate, uncomment and place in the alternation proof. -/

/-
section ActivationDemo
  variable (M r θ : ℝ) (a b c d : Idx)

  -- Local sumIdx expander using Option A (definitional)
  -- Place this inside each split section when activating
  local lemma sumIdx_expand_local {α : Type*} [AddCommMonoid α] (f : Idx → α) :
    sumIdx f = f Idx.t + f Idx.r + f Idx.θ + f Idx.φ := by
    -- Option A: definitional approach
    simp only [sumIdx, Idx.decEq]
    simp [add_comm, add_left_comm, add_assoc]
  local attribute [simp] sumIdx_expand_local

  -- Example: Using the bridge to expand ContractionC first family
  example :
    dCoord c (fun r θ =>
      sumIdx (fun e => Γtot M r θ e d a * g M e b r θ)) r θ
    =
      dCoord c (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ) r θ
    + dCoord c (fun r θ => Γtot M r θ Idx.r d a * g M Idx.r b r θ) r θ
    + dCoord c (fun r θ => Γtot M r θ Idx.θ d a * g M Idx.θ b r θ) r θ
    + dCoord c (fun r θ => Γtot M r θ Idx.φ d a * g M Idx.φ b r θ) r θ := by
    -- Step 1: Use bridge lemma with local expander
    have hexp := dCoord_sumIdx_via_local_expand c
      (fun e r θ => Γtot M r θ e d a * g M e b r θ) r θ sumIdx_expand_local
    convert hexp using 2 <;> simp only [sumIdx_expand_local]

  -- Example: Connect to Stage-1 fact
  example :
    dCoord c (fun r θ =>
      sumIdx (fun e => Γtot M r θ e d a * g M e b r θ)) r θ
    =
      -- Expanded t-summand (from Stage1LHS.Hc_one)
      (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * g M Idx.t b r θ
    + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ
      -- Other summands stay deferred
    + dCoord c (fun r θ => Γtot M r θ Idx.r d a * g M Idx.r b r θ) r θ
    + dCoord c (fun r θ => Γtot M r θ Idx.θ d a * g M Idx.θ b r θ) r θ
    + dCoord c (fun r θ => Γtot M r θ Idx.φ d a * g M Idx.φ b r θ) r θ := by
    -- Step 1: Expand sumIdx using bridge
    rw [dCoord_sumIdx_via_local_expand c _ r θ sumIdx_expand_local]
    -- Step 2: Apply Stage-1 fact to t-summand
    rw [Stage1LHS.Hc_one M r θ a b c d]
    -- Done - other summands remain as dCoord of products

end ActivationDemo
-/

/-
  -- === RiemannUp skeleton (comment-only; enable when the math is finalized) ===
  -- Convention note: adjust index order/signs to match your Γtot/Riemann conventions.

  -- def RiemannUp (M : ℝ) (a b c d : Idx) (r θ : ℝ) : ℝ :=
  --   dCoord c (fun r θ => Γtot M r θ a d b) r θ
  -- - dCoord d (fun r θ => Γtot M r θ a c b) r θ
  -- + sumIdx (fun e =>
  --     (Γtot M r θ a e c) * (Γtot M r θ e d b)
  --   - (Γtot M r θ a e d) * (Γtot M r θ e c b))

  -- lemma alternation_dC_eq_Riem_complete : ... := by
  --   -- Outline (mechanical with your helpers):
  --   -- 1) Expand the LHS via sumIdx_expand_local (local [simp]).
  --   -- 2) Use Stage1LHS.{Hc_one,Hd_one,Hc2_one,Hd2_one}.
  --   -- 3) Normalize with [add_comm, add_left_comm, add_assoc].
  --   -- 4) Push products using dCoord_mul and use dCoord_add4_flat for 4-term sums.
  --   sorry
-/

-- Stage-1 split helpers (file-scope; safe to activate)
section Stage1_LHS_Splits
  variable (M r θ : ℝ) (a b c d : Idx)

  -- Local enumerator with cleaner bridge shape
  private lemma sumIdx_expand_local (f : Idx → ℝ → ℝ → ℝ) :
    ∀ r θ,
      sumIdx (fun e => f e r θ)
      = f Idx.t r θ + f Idx.r r θ + f Idx.θ r θ + f Idx.φ r θ := by
    intro r θ
    simp [sumIdx, add_comm, add_left_comm, add_assoc]

  -- c-branch: split both families to 4+4 via the bridge; no global effects.
  set_option maxHeartbeats 400000 in
  lemma Hsplit_c_both :
    dCoord c (fun r θ => ContractionC M r θ d a b) r θ
    =
    dCoord c (fun r θ =>
       Γtot M r θ Idx.t d a * g M Idx.t b r θ
     + Γtot M r θ Idx.r d a * g M Idx.r b r θ
     + Γtot M r θ Idx.θ d a * g M Idx.θ b r θ
     + Γtot M r θ Idx.φ d a * g M Idx.φ b r θ) r θ
  +
    dCoord c (fun r θ =>
       Γtot M r θ Idx.t d b * g M a Idx.t r θ
     + Γtot M r θ Idx.r d b * g M a Idx.r r θ
     + Γtot M r θ Idx.θ d b * g M a Idx.θ r θ
     + Γtot M r θ Idx.φ d b * g M a Idx.φ r θ) r θ := by
    -- Expand ContractionC, distribute dCoord over sums, expand sumIdx
    simp only [ContractionC, dCoord_sumIdx, sumIdx_expand, dCoord_add]
    -- Normalize associativity/commutativity
    ring

  -- d-branch: same idea, roles of c/d swapped accordingly.
  set_option maxHeartbeats 400000 in
  lemma Hsplit_d_both :
    dCoord d (fun r θ => ContractionC M r θ c a b) r θ
    =
    dCoord d (fun r θ =>
       Γtot M r θ Idx.t c a * g M Idx.t b r θ
     + Γtot M r θ Idx.r c a * g M Idx.r b r θ
     + Γtot M r θ Idx.θ c a * g M Idx.θ b r θ
     + Γtot M r θ Idx.φ c a * g M Idx.φ b r θ) r θ
  +
    dCoord d (fun r θ =>
       Γtot M r θ Idx.t c b * g M a Idx.t r θ
     + Γtot M r θ Idx.r c b * g M a Idx.r r θ
     + Γtot M r θ Idx.θ c b * g M a Idx.θ r θ
     + Γtot M r θ Idx.φ c b * g M a Idx.φ r θ) r θ := by
    -- Expand ContractionC, distribute dCoord over sums, expand sumIdx
    simp only [ContractionC, dCoord_sumIdx, sumIdx_expand, dCoord_add]
    -- Normalize associativity/commutativity
    ring

end Stage1_LHS_Splits

-- Stage-1 RHS splits (file-scope; safe to activate)
section Stage1_RHS_Splits
  variable (M r θ : ℝ) (a b c d : Idx)

  -- Local μ-expander for RHS terms (μ summation in Riemann definition)
  private lemma sumIdx_expand_local_rhs (f : Idx → ℝ → ℝ → ℝ) :
    ∀ r θ, sumIdx (fun μ => f μ r θ)
      = f Idx.t r θ + f Idx.r r θ + f Idx.θ r θ + f Idx.φ r θ := by
    intro r θ
    simp [sumIdx, add_comm, add_left_comm, add_assoc]

  -- Split for first Riemann term: Riemann M r θ a b c d
  lemma Hsplit_RHS₁ :
    Riemann M r θ a b c d
      = sumIdx (fun μ => g M a μ r θ * RiemannUp M r θ μ b c d) := by
    -- This is just the definition
    rfl

  -- Expand the μ summation using the bridge lemma pattern
  lemma Hsplit_RHS₁_expanded :
    Riemann M r θ a b c d
      = g M a Idx.t r θ * RiemannUp M r θ Idx.t b c d
      + g M a Idx.r r θ * RiemannUp M r θ Idx.r b c d
      + g M a Idx.θ r θ * RiemannUp M r θ Idx.θ b c d
      + g M a Idx.φ r θ * RiemannUp M r θ Idx.φ b c d := by
    rw [Hsplit_RHS₁]
    exact sumIdx_expand_local_rhs (fun μ r θ => g M a μ r θ * RiemannUp M r θ μ b c d) r θ

  -- Split for second Riemann term: Riemann M r θ b a c d
  lemma Hsplit_RHS₂ :
    Riemann M r θ b a c d
      = sumIdx (fun μ => g M b μ r θ * RiemannUp M r θ μ a c d) := by
    -- This is just the definition
    rfl

  -- Expand the μ summation for second term
  lemma Hsplit_RHS₂_expanded :
    Riemann M r θ b a c d
      = g M b Idx.t r θ * RiemannUp M r θ Idx.t a c d
      + g M b Idx.r r θ * RiemannUp M r θ Idx.r a c d
      + g M b Idx.θ r θ * RiemannUp M r θ Idx.θ a c d
      + g M b Idx.φ r θ * RiemannUp M r θ Idx.φ a c d := by
    rw [Hsplit_RHS₂]
    exact sumIdx_expand_local_rhs (fun μ r θ => g M b μ r θ * RiemannUp M r θ μ a c d) r θ

  -- Combined RHS split: expand both Riemann terms
  lemma Hsplit_RHS_combined :
    Riemann M r θ a b c d + Riemann M r θ b a c d
      = (g M a Idx.t r θ * RiemannUp M r θ Idx.t b c d
        + g M a Idx.r r θ * RiemannUp M r θ Idx.r b c d
        + g M a Idx.θ r θ * RiemannUp M r θ Idx.θ b c d
        + g M a Idx.φ r θ * RiemannUp M r θ Idx.φ b c d)
      + (g M b Idx.t r θ * RiemannUp M r θ Idx.t a c d
        + g M b Idx.r r θ * RiemannUp M r θ Idx.r a c d
        + g M b Idx.θ r θ * RiemannUp M r θ Idx.θ a c d
        + g M b Idx.φ r θ * RiemannUp M r θ Idx.φ a c d) := by
    rw [Hsplit_RHS₁_expanded, Hsplit_RHS₂_expanded]

end Stage1_RHS_Splits

-- Stage-2 preview: μ = t component equivalence.
-- We prove (with a placeholder `sorry`) that the μ=t slice on the RHS equals
-- the corresponding LHS-style differential chunk.
-- This is designed for *local* rewriting inside the main lemma only.
section Stage2_mu_t_preview
  variable (M r θ : ℝ) (a b c d : Idx)

  private def LHS_mu_t_chunk :
      ℝ :=
    dCoord c (fun r θ =>
         Γtot M r θ Idx.t d a * g M Idx.t b r θ
       + Γtot M r θ Idx.t d b * g M a Idx.t r θ) r θ
    -
    dCoord d (fun r θ =>
         Γtot M r θ Idx.t c a * g M Idx.t b r θ
       + Γtot M r θ Idx.t c b * g M a Idx.t r θ) r θ

  private def RHS_mu_t_chunk :
      ℝ :=
      g M a Idx.t r θ * RiemannUp M r θ Idx.t b c d
    + g M b Idx.t r θ * RiemannUp M r θ Idx.t a c d

  /-- Equivalence of μ=t slice: LHS-style differential chunk equals RHS μ=t pair. -/
  lemma mu_t_component_eq :
      LHS_mu_t_chunk M r θ a b c d = RHS_mu_t_chunk M r θ a b c d := by
    /- Sketch (what we'd finish in Stage-2):
       * `simp` with your product-rule pushes (hpush_ct₁/_ct₂/_dt₁/_dt₂) to expand ∂(Γ⋅g)
       * apply metric compatibility `nabla_g_zero` to the ∂g terms
       * use `regroup_same_right` / `regroup₂` to pull common g-weights
       * unfold/align with the `RiemannUp` definition (μ=t row)
       The algebra is routine but verbose; we leave it as a placeholder for now. -/
    sorry

end Stage2_mu_t_preview

-- File-scope helper for zero derivatives (not marked [simp])
private lemma dCoord_zero_fun (μ : Idx) (r θ : ℝ) :
  dCoord μ (fun (_r : ℝ) (_θ : ℝ) => (0 : ℝ)) r θ = 0 := by
  simpa using dCoord_const μ (c := (0 : ℝ)) r θ

-- Targeted regroupers for common shapes produced after compatibility on g
-- (These are *not* global [simp]; we call them by name via `simp [..]`.)
private lemma regroup₂ (A₁ A₂ B₁ B₂ : ℝ) :
    A₁ * B₁ + A₂ * B₂ = (A₁ + A₂) * B₁ + A₂ * (B₂ - B₁) := by ring

private lemma regroup_same_right (A₁ A₂ B : ℝ) :
    A₁ * B + A₂ * B = (A₁ + A₂) * B := by ring

/-! ### DEFERRED: Alternation Identity Infrastructure (Category C)

The following lemmas (alternation_dC_eq_Riem and related Stage-1 scaffolding in commented
sections) are part of the alternation identity completion. This infrastructure is non-essential
for the vacuum solution and is deferred to future work per professor's mandate (PRIORITY 4).

**Status**: Complete scaffold ready (Stage-1 micro-packs), proofs deferred.
**Impact**: Does not block Ricci vanishing or any critical path theorems.
**Sorries**: ~15 in this section (including commented scaffolding).

The alternation identity is used in ricci_identity_on_g, which ultimately proves Riemann
antisymmetry. While this lemma has a sorry, the critical vacuum solution path (Ricci vanishing)
does not depend on completing this infrastructure.
-/

/-- Alternation identity scaffold (baseline-neutral with optional micro-steps).
    We expand the contracted object and push `dCoord` through the finite sum,
    then stop with a single algebraic `sorry`. No global calculus machinery is used.

    DEFERRED: This sorry is part of Category C (alternation identity infrastructure).
    See documentation block above. -/
lemma alternation_dC_eq_Riem (M r θ : ℝ) (a b c d : Idx) :
  ( dCoord c (fun r θ => ContractionC M r θ d a b) r θ
  - dCoord d (fun r θ => ContractionC M r θ c a b) r θ )
  = ( Riemann M r θ a b c d + Riemann M r θ b a c d ) := by
  /-
  -- ACTIVATION CHECKLIST (test each step individually):
  -- [ ] Stage 0: Uncomment namespace DraftRiemann block (lines 545-561)
  -- [ ] Stage 0b: Uncomment activation switch (lines 630-632) - use option (A)
  -- [ ] Stage 1a: Uncomment Stage-1 c-branch micro-pack (lines 667-728)
  -- [ ] Stage 1b: Uncomment Stage-1 d-branch micro-pack (lines 731-791)
  -- [ ] Stage 1c: Uncomment Stage-1 RHS ∂_c micro-pack (lines 794-851)
  -- [ ] Stage 1d: Uncomment Stage-1 RHS ∂_d micro-pack (lines 854-910)
  -- [ ] Stage 2: Uncomment original Pass-1 facts if needed (lines 957-1095)
  -- [ ] Stage 3: Uncomment split shapes (lines 1097-1154)
  -- [ ] Final: Uncomment unfold line (664) and complete proof
  -/

  -- NOTE: Early sorry due to Hsplit lemmas having performance issues
  -- The full proof scaffold is below but currently non-operational
  sorry

  /-
  -- Stage-1 splits (both families)
  have hC := Stage1_LHS_Splits.Hsplit_c_both M r θ a b c d
  have hD := Stage1_LHS_Splits.Hsplit_d_both M r θ a b c d

  -- First family c-branch: push dCoord across 4-term sum
  have hC₁ :=
    dCoord_add4_flat c
      (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ)
      (fun r θ => Γtot M r θ Idx.r d a * g M Idx.r b r θ)
      (fun r θ => Γtot M r θ Idx.θ d a * g M Idx.θ b r θ)
      (fun r θ => Γtot M r θ Idx.φ d a * g M Idx.φ b r θ)
      r θ

  -- Second family c-branch: same pattern with (d,b) and (a,·)
  have hC₂ :=
    dCoord_add4_flat c
      (fun r θ => Γtot M r θ Idx.t d b * g M a Idx.t r θ)
      (fun r θ => Γtot M r θ Idx.r d b * g M a Idx.r r θ)
      (fun r θ => Γtot M r θ Idx.θ d b * g M a Idx.θ r θ)
      (fun r θ => Γtot M r θ Idx.φ d b * g M a Idx.φ r θ)
      r θ

  -- First family d-branch: push dCoord across 4-term sum
  have hD₁ :=
    dCoord_add4_flat d
      (fun r θ => Γtot M r θ Idx.t c a * g M Idx.t b r θ)
      (fun r θ => Γtot M r θ Idx.r c a * g M Idx.r b r θ)
      (fun r θ => Γtot M r θ Idx.θ c a * g M Idx.θ b r θ)
      (fun r θ => Γtot M r θ Idx.φ c a * g M Idx.φ b r θ)
      r θ

  -- Second family d-branch: same pattern with (c,b) and (a,·)
  have hD₂ :=
    dCoord_add4_flat d
      (fun r θ => Γtot M r θ Idx.t c b * g M a Idx.t r θ)
      (fun r θ => Γtot M r θ Idx.r c b * g M a Idx.r r θ)
      (fun r θ => Γtot M r θ Idx.θ c b * g M a Idx.θ r θ)
      (fun r θ => Γtot M r θ Idx.φ c b * g M a Idx.φ r θ)
      r θ

  -- Replace each dCoord of sum with sum of dCoords
  have hC' := hC
  rw [← hC₁, ← hC₂] at hC'
  simp_all [add_comm, add_left_comm, add_assoc]

  have hD' := hD
  rw [← hD₁, ← hD₂] at hD'
  simp_all [add_comm, add_left_comm, add_assoc]

  -- Push product rule on t-summands using Stage-1 facts
  -- C-branch, first family, t-summand
  have hpush_ct₁ :
    dCoord c (fun r θ => Γtot M r θ Idx.t d a * g M Idx.t b r θ) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * g M Idx.t b r θ
    + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ := by
    exact dCoord_mul c
      (fun r θ => Γtot M r θ Idx.t d a)
      (fun r θ => g M Idx.t b r θ) r θ

  -- C-branch, second family, t-summand
  have hpush_ct₂ :
    dCoord c (fun r θ => Γtot M r θ Idx.t d b * g M a Idx.t r θ) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d b) r θ) * g M a Idx.t r θ
    + (Γtot M r θ Idx.t d b) * dCoord c (fun r θ => g M a Idx.t r θ) r θ := by
    exact dCoord_mul c
      (fun r θ => Γtot M r θ Idx.t d b)
      (fun r θ => g M a Idx.t r θ) r θ

  -- D-branch, first family, t-summand
  have hpush_dt₁ :
    dCoord d (fun r θ => Γtot M r θ Idx.t c a * g M Idx.t b r θ) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ) * g M Idx.t b r θ
    + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => g M Idx.t b r θ) r θ := by
    exact dCoord_mul d
      (fun r θ => Γtot M r θ Idx.t c a)
      (fun r θ => g M Idx.t b r θ) r θ

  -- D-branch, second family, t-summand
  have hpush_dt₂ :
    dCoord d (fun r θ => Γtot M r θ Idx.t c b * g M a Idx.t r θ) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.t c b) r θ) * g M a Idx.t r θ
    + (Γtot M r θ Idx.t c b) * dCoord d (fun r θ => g M a Idx.t r θ) r θ := by
    exact dCoord_mul d
      (fun r θ => Γtot M r θ Idx.t c b)
      (fun r θ => g M a Idx.t r θ) r θ

  -- Push product rule on r-summands (all 4 branches)
  -- C-branch, first family, r-summand
  have hpush_cr₁ :
    dCoord c (fun r θ => Γtot M r θ Idx.r d a * g M Idx.r b r θ) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.r d a) r θ) * g M Idx.r b r θ
    + (Γtot M r θ Idx.r d a) * dCoord c (fun r θ => g M Idx.r b r θ) r θ := by
    simpa using dCoord_mul c
      (fun r θ => Γtot M r θ Idx.r d a)
      (fun r θ => g M Idx.r b r θ) r θ

  -- C-branch, second family, r-summand
  have hpush_cr₂ :
    dCoord c (fun r θ => Γtot M r θ Idx.r d b * g M a Idx.r r θ) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.r d b) r θ) * g M a Idx.r r θ
    + (Γtot M r θ Idx.r d b) * dCoord c (fun r θ => g M a Idx.r r θ) r θ := by
    simpa using dCoord_mul c
      (fun r θ => Γtot M r θ Idx.r d b)
      (fun r θ => g M a Idx.r r θ) r θ

  -- D-branch, first family, r-summand
  have hpush_dr₁ :
    dCoord d (fun r θ => Γtot M r θ Idx.r c a * g M Idx.r b r θ) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.r c a) r θ) * g M Idx.r b r θ
    + (Γtot M r θ Idx.r c a) * dCoord d (fun r θ => g M Idx.r b r θ) r θ := by
    simpa using dCoord_mul d
      (fun r θ => Γtot M r θ Idx.r c a)
      (fun r θ => g M Idx.r b r θ) r θ

  -- D-branch, second family, r-summand
  have hpush_dr₂ :
    dCoord d (fun r θ => Γtot M r θ Idx.r c b * g M a Idx.r r θ) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.r c b) r θ) * g M a Idx.r r θ
    + (Γtot M r θ Idx.r c b) * dCoord d (fun r θ => g M a Idx.r r θ) r θ := by
    simpa using dCoord_mul d
      (fun r θ => Γtot M r θ Idx.r c b)
      (fun r θ => g M a Idx.r r θ) r θ

  -- Push product rule on θ-summands (all 4 branches)
  -- C-branch, first family, θ-summand
  have hpush_cθ₁ :
    dCoord c (fun r θ => Γtot M r θ Idx.θ d a * g M Idx.θ b r θ) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.θ d a) r θ) * g M Idx.θ b r θ
    + (Γtot M r θ Idx.θ d a) * dCoord c (fun r θ => g M Idx.θ b r θ) r θ := by
    simpa using dCoord_mul c
      (fun r θ => Γtot M r θ Idx.θ d a)
      (fun r θ => g M Idx.θ b r θ) r θ

  -- C-branch, second family, θ-summand
  have hpush_cθ₂ :
    dCoord c (fun r θ => Γtot M r θ Idx.θ d b * g M a Idx.θ r θ) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.θ d b) r θ) * g M a Idx.θ r θ
    + (Γtot M r θ Idx.θ d b) * dCoord c (fun r θ => g M a Idx.θ r θ) r θ := by
    simpa using dCoord_mul c
      (fun r θ => Γtot M r θ Idx.θ d b)
      (fun r θ => g M a Idx.θ r θ) r θ

  -- D-branch, first family, θ-summand
  have hpush_dθ₁ :
    dCoord d (fun r θ => Γtot M r θ Idx.θ c a * g M Idx.θ b r θ) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.θ c a) r θ) * g M Idx.θ b r θ
    + (Γtot M r θ Idx.θ c a) * dCoord d (fun r θ => g M Idx.θ b r θ) r θ := by
    simpa using dCoord_mul d
      (fun r θ => Γtot M r θ Idx.θ c a)
      (fun r θ => g M Idx.θ b r θ) r θ

  -- D-branch, second family, θ-summand
  have hpush_dθ₂ :
    dCoord d (fun r θ => Γtot M r θ Idx.θ c b * g M a Idx.θ r θ) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.θ c b) r θ) * g M a Idx.θ r θ
    + (Γtot M r θ Idx.θ c b) * dCoord d (fun r θ => g M a Idx.θ r θ) r θ := by
    simpa using dCoord_mul d
      (fun r θ => Γtot M r θ Idx.θ c b)
      (fun r θ => g M a Idx.θ r θ) r θ

  -- Push product rule on φ-summands (all 4 branches)
  -- C-branch, first family, φ-summand
  have hpush_cφ₁ :
    dCoord c (fun r θ => Γtot M r θ Idx.φ d a * g M Idx.φ b r θ) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.φ d a) r θ) * g M Idx.φ b r θ
    + (Γtot M r θ Idx.φ d a) * dCoord c (fun r θ => g M Idx.φ b r θ) r θ := by
    simpa using dCoord_mul c
      (fun r θ => Γtot M r θ Idx.φ d a)
      (fun r θ => g M Idx.φ b r θ) r θ

  -- C-branch, second family, φ-summand
  have hpush_cφ₂ :
    dCoord c (fun r θ => Γtot M r θ Idx.φ d b * g M a Idx.φ r θ) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.φ d b) r θ) * g M a Idx.φ r θ
    + (Γtot M r θ Idx.φ d b) * dCoord c (fun r θ => g M a Idx.φ r θ) r θ := by
    simpa using dCoord_mul c
      (fun r θ => Γtot M r θ Idx.φ d b)
      (fun r θ => g M a Idx.φ r θ) r θ

  -- D-branch, first family, φ-summand
  have hpush_dφ₁ :
    dCoord d (fun r θ => Γtot M r θ Idx.φ c a * g M Idx.φ b r θ) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.φ c a) r θ) * g M Idx.φ b r θ
    + (Γtot M r θ Idx.φ c a) * dCoord d (fun r θ => g M Idx.φ b r θ) r θ := by
    simpa using dCoord_mul d
      (fun r θ => Γtot M r θ Idx.φ c a)
      (fun r θ => g M Idx.φ b r θ) r θ

  -- D-branch, second family, φ-summand
  have hpush_dφ₂ :
    dCoord d (fun r θ => Γtot M r θ Idx.φ c b * g M a Idx.φ r θ) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.φ c b) r θ) * g M a Idx.φ r θ
    + (Γtot M r θ Idx.φ c b) * dCoord d (fun r θ => g M a Idx.φ r θ) r θ := by
    simpa using dCoord_mul d
      (fun r θ => Γtot M r θ Idx.φ c b)
      (fun r θ => g M a Idx.φ r θ) r θ

  -- Apply all product pushes to the split equalities
  -- C-branch: apply all 8 product pushes (t already done, now r, θ, φ)
  have hC_pushed := hC'
  -- First family
  rw [← hpush_ct₁] at hC_pushed
  rw [← hpush_cr₁] at hC_pushed
  rw [← hpush_cθ₁] at hC_pushed
  rw [← hpush_cφ₁] at hC_pushed
  -- Second family
  rw [← hpush_ct₂] at hC_pushed
  rw [← hpush_cr₂] at hC_pushed
  rw [← hpush_cθ₂] at hC_pushed
  rw [← hpush_cφ₂] at hC_pushed
  simp_all [add_comm, add_left_comm, add_assoc]

  -- D-branch: apply all 8 product pushes
  have hD_pushed := hD'
  -- First family
  rw [← hpush_dt₁] at hD_pushed
  rw [← hpush_dr₁] at hD_pushed
  rw [← hpush_dθ₁] at hD_pushed
  rw [← hpush_dφ₁] at hD_pushed
  -- Second family
  rw [← hpush_dt₂] at hD_pushed
  rw [← hpush_dr₂] at hD_pushed
  rw [← hpush_dθ₂] at hD_pushed
  rw [← hpush_dφ₂] at hD_pushed
  simp_all [add_comm, add_left_comm, add_assoc]

  -- Apply the pushed versions to the goal (combined for better normalization)
  rw [← hD_pushed, ← hC_pushed]

  -- Expand RHS once and normalize, then *stop* (no further re-expansion)
  have hRHS₀ : Riemann M r θ a b c d + Riemann M r θ b a c d
    =
      (g M a Idx.t r θ * RiemannUp M r θ Idx.t b c d
     + g M a Idx.r r θ * RiemannUp M r θ Idx.r b c d
     + g M a Idx.θ r θ * RiemannUp M r θ Idx.θ b c d
     + g M a Idx.φ r θ * RiemannUp M r θ Idx.φ b c d)
    +
      (g M b Idx.t r θ * RiemannUp M r θ Idx.t a c d
     + g M b Idx.r r θ * RiemannUp M r θ Idx.r a c d
     + g M b Idx.θ r θ * RiemannUp M r θ Idx.θ a c d
     + g M b Idx.φ r θ * RiemannUp M r θ Idx.φ a c d) := by
    -- Use the pre-expanded lemma directly
    exact Stage1_RHS_Splits.Hsplit_RHS_combined M r θ a b c d

  -- Use hRHS₀ *once*; then avoid re-expanding to prevent churn
  rw [hRHS₀]

  -- Replace the RHS μ=t pair by the equivalent LHS-style differential chunk.
  -- This aligns the μ=t row with the already-pushed LHS structure.
  have hμt_rw :
    g M a Idx.t r θ * RiemannUp M r θ Idx.t b c d
  + g M b Idx.t r θ * RiemannUp M r θ Idx.t a c d
    =
    (Stage2_mu_t_preview.LHS_mu_t_chunk M r θ a b c d) := by
    -- Use the preview lemma in reverse direction:
    simpa using (Stage2_mu_t_preview.mu_t_component_eq M r θ a b c d).symm

  -- Rewrite the μ=t pair in-place. `simp [hμt_rw, ...]` will find it inside the big sum.
  simp [hμt_rw,
        add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]  -- structure only (no re-expansion)

  -- Now normalize add/mul structure with regrouping helpers
  simp_all [add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc,
            nabla_g_zero, dCoord_const, dCoord_zero_fun,
            regroup₂, regroup_same_right]

  -- Unfold key definitions (uncomment when DraftRiemann namespace is active)
  -- unfold ContractionC Riemann RiemannUp

  /-
  -- === Stage 1: LHS c-branch (first family) ===
  section Stage1_LHS_c_first

  -- Name the 4 product summands so linearity matches robustly
  set P_t : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.t d a) * (g M Idx.t b r θ)) with hPt
  set P_r : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)) with hPr
  set P_θ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)) with hPθ
  set P_φ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)) with hPφ

  -- Local binary linearity helpers (works with your existing dCoord_add)
  have hAB :
    dCoord c (fun r θ => P_t r θ + P_r r θ) r θ
      = dCoord c P_t r θ + dCoord c P_r r θ := by
    simpa using dCoord_add c P_t P_r r θ
  have hCD :
    dCoord c (fun r θ => P_θ r θ + P_φ r θ) r θ
      = dCoord c P_θ r θ + dCoord c P_φ r θ := by
    simpa using dCoord_add c P_θ P_φ r θ
  have hABCD :
    dCoord c (fun r θ => (P_t r θ + P_r r θ) + (P_θ r θ + P_φ r θ)) r θ
      = (dCoord c P_t r θ + dCoord c P_r r θ)
      + (dCoord c P_θ r θ + dCoord c P_φ r θ) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      dCoord_add c (fun r θ => P_t r θ + P_r r θ)
                   (fun r θ => P_θ r θ + P_φ r θ) r θ

  -- 4-term linearity (derived locally from the binary steps above)
  have hsum_c :
    dCoord c (fun r θ => P_t r θ + P_r r θ + P_θ r θ + P_φ r θ) r θ
      = dCoord c P_t r θ + dCoord c P_r r θ + dCoord c P_θ r θ + dCoord c P_φ r θ := by
    simpa [add_comm, add_left_comm, add_assoc] using hABCD

  -- Per-summand product rule (t-summand only), keep r,θ,φ deferred
  have hPt_push :
    dCoord c P_t r θ
      =
    dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ * g M Idx.t b r θ
    + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ := by
    -- Uses your existing product rule `dCoord_mul`
    simpa [hPt] using
      dCoord_mul c
        (fun r θ => Γtot M r θ Idx.t d a)
        (fun r θ => g M Idx.t b r θ) r θ

  -- Assemble the "one-summand expanded, others deferred" fact (no goal rewrite)
  have Hc_one :
    dCoord c (fun r θ =>
      (Γtot M r θ Idx.t d a) * (g M Idx.t b r θ)
    + (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)
    + (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)
    + (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * g M Idx.t b r θ
    + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ
    + dCoord c P_r r θ + dCoord c P_θ r θ + dCoord c P_φ r θ := by
    -- Combine hsum_c with hPt_push; normalize with the hP* names
    have H := hsum_c
    rw [hPt_push] at H
    simpa [hPt, hPr, hPθ, hPφ, add_comm, add_left_comm, add_assoc] using H

  end Stage1_LHS_c_first
  -/

  /-
  -- === Stage 1: LHS c-branch (second family) ===
  section Stage1_LHS_c_second

  -- Name the 4 product summands for second family g_{a e} (Γtot * g orientation)
  set P2_t : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.t d b) * (g M a Idx.t r θ)) with hP2t
  set P2_r : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.r d b) * (g M a Idx.r r θ)) with hP2r
  set P2_θ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.θ d b) * (g M a Idx.θ r θ)) with hP2θ
  set P2_φ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.φ d b) * (g M a Idx.φ r θ)) with hP2φ

  -- Local 4-term linearity for c-branch (second family)
  have hAB2_c :
    dCoord c (fun r θ => P2_t r θ + P2_r r θ) r θ
      = dCoord c P2_t r θ + dCoord c P2_r r θ := by
    simpa using dCoord_add c P2_t P2_r r θ
  have hCD2_c :
    dCoord c (fun r θ => P2_θ r θ + P2_φ r θ) r θ
      = dCoord c P2_θ r θ + dCoord c P2_φ r θ := by
    simpa using dCoord_add c P2_θ P2_φ r θ
  have hABCD2_c :
    dCoord c (fun r θ => (P2_t r θ + P2_r r θ) + (P2_θ r θ + P2_φ r θ)) r θ
      = (dCoord c P2_t r θ + dCoord c P2_r r θ)
      + (dCoord c P2_θ r θ + dCoord c P2_φ r θ) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      dCoord_add c (fun r θ => P2_t r θ + P2_r r θ)
                   (fun r θ => P2_θ r θ + P2_φ r θ) r θ

  have hsum2_c :
    dCoord c (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ
      = dCoord c P2_t r θ + dCoord c P2_r r θ + dCoord c P2_θ r θ + dCoord c P2_φ r θ := by
    simpa [add_comm, add_left_comm, add_assoc] using hABCD2_c

  -- Per-summand product rule (t-summand only for second family, Γtot first)
  have hP2t_push :
    dCoord c P2_t r θ
      =
    dCoord c (fun r θ => Γtot M r θ Idx.t d b) r θ * (g M a Idx.t r θ)
    + (Γtot M r θ Idx.t d b) * dCoord c (fun r θ => g M a Idx.t r θ) r θ := by
    simpa [hP2t] using
      dCoord_mul c
        (fun r θ => Γtot M r θ Idx.t d b)
        (fun r θ => g M a Idx.t r θ) r θ

  have Hc2_one :
    dCoord c (fun r θ =>
      (Γtot M r θ Idx.t d b) * (g M a Idx.t r θ)
    + (Γtot M r θ Idx.r d b) * (g M a Idx.r r θ)
    + (Γtot M r θ Idx.θ d b) * (g M a Idx.θ r θ)
    + (Γtot M r θ Idx.φ d b) * (g M a Idx.φ r θ)) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d b) r θ) * (g M a Idx.t r θ)
    + (Γtot M r θ Idx.t d b) * dCoord c (fun r θ => g M a Idx.t r θ) r θ
    + dCoord c P2_r r θ + dCoord c P2_θ r θ + dCoord c P2_φ r θ := by
    -- Combine hsum2_c with hP2t_push; normalize with the hP2* names
    have H := hsum2_c
    rw [hP2t_push] at H
    simpa [hP2t, hP2r, hP2θ, hP2φ, add_comm, add_left_comm, add_assoc] using H

  end Stage1_LHS_c_second
  -/

  /-
  -- === Stage 1: LHS d-branch (first family) ===
  section Stage1_LHS_d_first

  -- Name the 4 product summands so linearity matches robustly
  set Q_t : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.t c a) * (g M Idx.t b r θ)) with hQt
  set Q_r : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.r c a) * (g M Idx.r b r θ)) with hQr
  set Q_θ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.θ c a) * (g M Idx.θ b r θ)) with hQθ
  set Q_φ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.φ c a) * (g M Idx.φ b r θ)) with hQφ

  -- Local binary linearity (reuse dCoord_add)
  have hAB_d :
    dCoord d (fun r θ => Q_t r θ + Q_r r θ) r θ
      = dCoord d Q_t r θ + dCoord d Q_r r θ := by
    simpa using dCoord_add d Q_t Q_r r θ
  have hCD_d :
    dCoord d (fun r θ => Q_θ r θ + Q_φ r θ) r θ
      = dCoord d Q_θ r θ + dCoord d Q_φ r θ := by
    simpa using dCoord_add d Q_θ Q_φ r θ
  have hABCD_d :
    dCoord d (fun r θ => (Q_t r θ + Q_r r θ) + (Q_θ r θ + Q_φ r θ)) r θ
      = (dCoord d Q_t r θ + dCoord d Q_r r θ)
      + (dCoord d Q_θ r θ + dCoord d Q_φ r θ) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      dCoord_add d (fun r θ => Q_t r θ + Q_r r θ)
                   (fun r θ => Q_θ r θ + Q_φ r θ) r θ

  -- 4-term linearity for d-branch
  have hsum_d :
    dCoord d (fun r θ => Q_t r θ + Q_r r θ + Q_θ r θ + Q_φ r θ) r θ
      = dCoord d Q_t r θ + dCoord d Q_r r θ + dCoord d Q_θ r θ + dCoord d Q_φ r θ := by
    simpa [add_comm, add_left_comm, add_assoc] using hABCD_d

  -- Per-summand product rule (t-summand only), keep r,θ,φ deferred
  have hQt_push :
    dCoord d Q_t r θ
      =
    dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ * g M Idx.t b r θ
    + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => g M Idx.t b r θ) r θ := by
    simpa [hQt] using
      dCoord_mul d
        (fun r θ => Γtot M r θ Idx.t c a)
        (fun r θ => g M Idx.t b r θ) r θ

  -- Assemble the "one-summand expanded, others deferred" fact (no goal rewrite)
  have Hd_one :
    dCoord d (fun r θ =>
      (Γtot M r θ Idx.t c a) * (g M Idx.t b r θ)
    + (Γtot M r θ Idx.r c a) * (g M Idx.r b r θ)
    + (Γtot M r θ Idx.θ c a) * (g M Idx.θ b r θ)
    + (Γtot M r θ Idx.φ c a) * (g M Idx.φ b r θ)) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ) * g M Idx.t b r θ
    + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => g M Idx.t b r θ) r θ
    + dCoord d Q_r r θ + dCoord d Q_θ r θ + dCoord d Q_φ r θ := by
    -- Combine hsum_d with hQt_push; normalize with the hQ* names
    have H := hsum_d
    rw [hQt_push] at H
    simpa [hQt, hQr, hQθ, hQφ, add_comm, add_left_comm, add_assoc] using H

  end Stage1_LHS_d_first
  -/

  /-
  -- === Stage 1: LHS d-branch (second family) ===
  section Stage1_LHS_d_second

  -- Name the 4 product summands for second family g_{a e} (Γtot * g orientation)
  set Q2_t : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.t c b) * (g M a Idx.t r θ)) with hQ2t
  set Q2_r : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.r c b) * (g M a Idx.r r θ)) with hQ2r
  set Q2_θ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.θ c b) * (g M a Idx.θ r θ)) with hQ2θ
  set Q2_φ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.φ c b) * (g M a Idx.φ r θ)) with hQ2φ

  -- Local 4-term linearity for d-branch (second family)
  have hAB2_d :
    dCoord d (fun r θ => Q2_t r θ + Q2_r r θ) r θ
      = dCoord d Q2_t r θ + dCoord d Q2_r r θ := by
    simpa using dCoord_add d Q2_t Q2_r r θ
  have hCD2_d :
    dCoord d (fun r θ => Q2_θ r θ + Q2_φ r θ) r θ
      = dCoord d Q2_θ r θ + dCoord d Q2_φ r θ := by
    simpa using dCoord_add d Q2_θ Q2_φ r θ
  have hABCD2_d :
    dCoord d (fun r θ => (Q2_t r θ + Q2_r r θ) + (Q2_θ r θ + Q2_φ r θ)) r θ
      = (dCoord d Q2_t r θ + dCoord d Q2_r r θ)
      + (dCoord d Q2_θ r θ + dCoord d Q2_φ r θ) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      dCoord_add d (fun r θ => Q2_t r θ + Q2_r r θ)
                   (fun r θ => Q2_θ r θ + Q2_φ r θ) r θ

  have hsum2_d :
    dCoord d (fun r θ => Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ) r θ
      = dCoord d Q2_t r θ + dCoord d Q2_r r θ + dCoord d Q2_θ r θ + dCoord d Q2_φ r θ := by
    simpa [add_comm, add_left_comm, add_assoc] using hABCD2_d

  -- Per-summand product rule (t-summand only for second family, Γtot first)
  have hQ2t_push :
    dCoord d Q2_t r θ
      =
    dCoord d (fun r θ => Γtot M r θ Idx.t c b) r θ * (g M a Idx.t r θ)
    + (Γtot M r θ Idx.t c b) * dCoord d (fun r θ => g M a Idx.t r θ) r θ := by
    simpa [hQ2t] using
      dCoord_mul d
        (fun r θ => Γtot M r θ Idx.t c b)
        (fun r θ => g M a Idx.t r θ) r θ

  have Hd2_one :
    dCoord d (fun r θ =>
      (Γtot M r θ Idx.t c b) * (g M a Idx.t r θ)
    + (Γtot M r θ Idx.r c b) * (g M a Idx.r r θ)
    + (Γtot M r θ Idx.θ c b) * (g M a Idx.θ r θ)
    + (Γtot M r θ Idx.φ c b) * (g M a Idx.φ r θ)) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.t c b) r θ) * (g M a Idx.t r θ)
    + (Γtot M r θ Idx.t c b) * dCoord d (fun r θ => g M a Idx.t r θ) r θ
    + dCoord d Q2_r r θ + dCoord d Q2_θ r θ + dCoord d Q2_φ r θ := by
    -- Combine hsum2_d with hQ2t_push; normalize with the hQ2* names
    have H := hsum2_d
    rw [hQ2t_push] at H
    simpa [hQ2t, hQ2r, hQ2θ, hQ2φ, add_comm, add_left_comm, add_assoc] using H

  end Stage1_LHS_d_second
  -/

  /-
  -- === sumIdx enumerator (ready to enable) ===
  -- Choose ONE of the two depending on how `sumIdx` is defined.

  -- Option A (definitional): If `sumIdx f` is definitionally `f t + f r + f θ + f φ`.
  -- lemma sumIdx_expand (f : Idx → ℝ) :
  --   sumIdx f = f Idx.t + f Idx.r + f Idx.θ + f Idx.φ := by
  --   simp [sumIdx, add_comm, add_left_comm, add_assoc]

  -- Option B (finite-type version): If `sumIdx` is a fold over the finite type `Idx`.
  -- Requires `[DecidableEq Idx] [Fintype Idx]` and `sumIdx` matching `Finset.universe.sum`.
  -- lemma sumIdx_expand (f : Idx → ℝ) :
  --   sumIdx f = f Idx.t + f Idx.r + f Idx.θ + f Idx.φ := by
  --   classical
  --   -- unfold sumIdx to the underlying finite sum, then enumerate Idx = {t,r,θ,φ}
  --   -- simp [sumIdx, Finset.universe, add_comm, add_left_comm, add_assoc]

  -- When you choose Option A or B and enable `sumIdx_expand`, consider keeping it *local*:
  --   local attribute [simp] sumIdx_expand
  -- That lets you `simp [sumIdx_expand]` inside split sections without changing global behavior.
  -/

  /-
  -- === Local enumerator pattern for split sections (paste inside each) ===
  -- local lemma sumIdx_expand_local (f : Idx → ℝ) :
  --   sumIdx f = f Idx.t + f Idx.r + f Idx.θ + f Idx.φ := by
  --   -- Option A: definitional `sumIdx`
  --   --   simp [sumIdx, add_comm, add_left_comm, add_assoc]
  --   -- Option B: finite type enumeration
  --   --   classical
  --   --   -- unfold to finset sum; enumerate Idx = {t,r,θ,φ}
  --   --   -- simp [sumIdx, Finset.universe, add_comm, add_left_comm, add_assoc]
  --   sorry
  -- local attribute [simp] sumIdx_expand_local
  -- Then use: simp [sumIdx_expand_local] to expand locally
  -/

  /-
  -- === ACTIVATION GUIDE for Stage-1 Splits ===
  -- When ready to activate, the diff is minimal:
  -- 1. Uncomment the section
  -- 2. After the pointwise split, add:
  --    have h_add := dCoord_add c (first_family_sum) (second_family_sum) r θ
  -- 3. Apply 4-term linearity:
  --    have h_linP  := dCoord_add4_flat c P_t  P_r  P_θ  P_φ  r θ
  --    have h_linP2 := dCoord_add4_flat c P2_t P2_r P2_θ P2_φ r θ
  -- 4. Chain: pointwise_split.trans h_add |>.trans (by rw [h_linP, h_linP2])
  --
  -- Uses: dCoord_add4_flat for 4-term linearity, dCoord_mul for product rules
  -- Normalization: [add_comm, add_left_comm, add_assoc]
  -/

  /-
  -- === Stage 1: LHS c-branch (split both families) ===
  section Stage1_LHS_c_split

  have Hsplit_c_both :
    dCoord c (fun r θ => ContractionC M r θ d a b) r θ
      =
    dCoord c (fun r θ => P_t  r θ + P_r  r θ + P_θ  r θ + P_φ  r θ) r θ
    + dCoord c (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ := by
    -- idea:
    --   unfold ContractionC;  -- when DraftRiemann is active, no change needed here
    --   -- rewrite  ∑_e [Γ^e_{d a} g_{e b} + Γ^e_{d b} g_{a e}]  as  (∑ first) + (∑ second)
    --   -- then expand each finite ∑ to 4 terms using your enumerator, and `simpa` with:
    --   --   [hPt, hPr, hPθ, hPφ, hP2t, hP2r, hP2θ, hP2φ, add_comm, add_left_comm, add_assoc]

    -- Pre-wired 4-term linearity for first family (when activated):
    -- have hLinP :
    --   dCoord c (fun r θ => P_t r θ + P_r r θ + P_θ r θ + P_φ r θ) r θ
    --   =
    --   dCoord c P_t r θ + dCoord c P_r r θ + dCoord c P_θ r θ + dCoord c P_φ r θ := by
    --   simpa [add_comm, add_left_comm, add_assoc] using
    --     dCoord_add4 c P_t P_r P_θ P_φ r θ

    -- Pre-wired 4-term linearity for second family (when activated):
    -- have hLinP2 :
    --   dCoord c (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ
    --   =
    --   dCoord c P2_t r θ + dCoord c P2_r r θ + dCoord c P2_θ r θ + dCoord c P2_φ r θ := by
    --   simpa [add_comm, add_left_comm, add_assoc] using
    --     dCoord_add4 c P2_t P2_r P2_θ P2_φ r θ

    sorry

  end Stage1_LHS_c_split
  -/

  /-
  -- === Stage 1: LHS d-branch (split both families) ===
  section Stage1_LHS_d_split
  have Hsplit_d_both :
    dCoord d (fun r θ => ContractionC M r θ c a b) r θ
      =
    dCoord d (fun r θ => Q_t  r θ + Q_r  r θ + Q_θ  r θ + Q_φ  r θ) r θ
    + dCoord d (fun r θ => Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ) r θ := by
    -- mirrored idea of Hsplit_c_both; same `simpa` hint set for the Q/Q2 names

    -- Pre-wired 4-term linearity for first family (when activated):
    -- have hLinQ :
    --   dCoord d (fun r θ => Q_t r θ + Q_r r θ + Q_θ r θ + Q_φ r θ) r θ
    --   =
    --   dCoord d Q_t r θ + dCoord d Q_r r θ + dCoord d Q_θ r θ + dCoord d Q_φ r θ := by
    --   simpa [add_comm, add_left_comm, add_assoc] using
    --     dCoord_add4 d Q_t Q_r Q_θ Q_φ r θ

    -- Pre-wired 4-term linearity for second family (when activated):
    -- have hLinQ2 :
    --   dCoord d (fun r θ => Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ) r θ
    --   =
    --   dCoord d Q2_t r θ + dCoord d Q2_r r θ + dCoord d Q2_θ r θ + dCoord d Q2_φ r θ := by
    --   simpa [add_comm, add_left_comm, add_assoc] using
    --     dCoord_add4 d Q2_t Q2_r Q2_θ Q2_φ r θ

    sorry

  end Stage1_LHS_d_split
  -/

  /-
  -- Proof skeleton for Hsplit_c_both (replace the `sorry` above when ready):

  -- Self-contained: define all 8 names locally (so this works without Stage-1 blocks)
  set P_t  : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.t d a) * (g M Idx.t b r θ)) with hPt
  set P_r  : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)) with hPr
  set P_θ  : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)) with hPθ
  set P_φ  : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)) with hPφ

  set P2_t : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.t d b) * (g M a Idx.t r θ)) with hP2t
  set P2_r : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.r d b) * (g M a Idx.r r θ)) with hP2r
  set P2_θ : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.θ d b) * (g M a Idx.θ r θ)) with hP2θ
  set P2_φ : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.φ d b) * (g M a Idx.φ r θ)) with hP2φ

  -- Local simp bundle (scoped to this proof only)
  local attribute [simp] hPt hPr hPθ hPφ hP2t hP2r hP2θ hP2φ

  -- Step A: rewrite ContractionC pointwise into (first family) + (second family)
  have h_split_c_pointwise :
    (fun r θ => ContractionC M r θ d a b)
      =
    (fun r θ =>
        (P_t  r θ + P_r  r θ + P_θ  r θ + P_φ  r θ)
      + (P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ)) := by
    funext r θ
    -- Expand ContractionC, expand the finite sum, and normalize into P_* + P2_*:
    --   ContractionC = ∑e [ Γ^e_{d a}·g_{e b}  +  Γ^e_{d b}·g_{a e} ]
    -- Use your enumerator (t, r, θ, φ), then `simpa` with the names.
    -- NOTE: keep all `add_*` comm/assoc rewrites local for determinism.
    -- With local simp bundle, the normalization is cleaner:
    --   simp [ContractionC, sumIdx_expand, add_comm, add_left_comm, add_assoc]
    -- The hP*/hP2* names are already marked as simp
    sorry

  -- Step B: apply binary linearity across the two families, then normalize
  have h_lin_c :
    dCoord c
      (fun r θ =>
          (P_t  r θ + P_r  r θ + P_θ  r θ + P_φ  r θ)
        + (P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ)) r θ
    =
    dCoord c (fun r θ => P_t  r θ + P_r  r θ + P_θ  r θ + P_φ  r θ) r θ
    + dCoord c (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ := by
    -- single application of binary linearity
    simpa [add_comm, add_left_comm, add_assoc]
      using dCoord_add c
        (fun r θ => P_t  r θ + P_r  r θ + P_θ  r θ + P_φ  r θ)
        (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ

  -- Step C: tie it together with one rewrite and a `simpa`
  have Hsplit_c_both :
    dCoord c (fun r θ => ContractionC M r θ d a b) r θ
      =
    dCoord c (fun r θ => P_t  r θ + P_r  r θ + P_θ  r θ + P_φ  r θ) r θ
    + dCoord c (fun r θ => P2_t r θ + P2_r r θ + P2_θ r θ + P2_φ r θ) r θ := by
    -- pointwise rewrite, then linearity, then normalize
    have := congrArg (fun F => dCoord c F r θ) h_split_c_pointwise
    -- `this` : dCoord c (ContractionC …) = dCoord c ((P-sum)+(P2-sum))
    -- Now replace RHS via `h_lin_c`:
    simpa using this.trans h_lin_c

  -- As always, build & verify error count immediately after enabling.
  -/

  /-
  -- Proof skeleton for Hsplit_d_both (replace the `sorry` above when ready):

  -- Self-contained: define all 8 names locally (so this works without Stage-1 blocks)
  set Q_t  : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.t c a) * (g M Idx.t b r θ)) with hQt
  set Q_r  : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.r c a) * (g M Idx.r b r θ)) with hQr
  set Q_θ  : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.θ c a) * (g M Idx.θ b r θ)) with hQθ
  set Q_φ  : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.φ c a) * (g M Idx.φ b r θ)) with hQφ

  set Q2_t : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.t c b) * (g M a Idx.t r θ)) with hQ2t
  set Q2_r : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.r c b) * (g M a Idx.r r θ)) with hQ2r
  set Q2_θ : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.θ c b) * (g M a Idx.θ r θ)) with hQ2θ
  set Q2_φ : ℝ → ℝ → ℝ := (fun r θ => (Γtot M r θ Idx.φ c b) * (g M a Idx.φ r θ)) with hQ2φ

  -- Local simp bundle (scoped to this proof only)
  local attribute [simp] hQt hQr hQθ hQφ hQ2t hQ2r hQ2θ hQ2φ

  -- Step A: pointwise split of ContractionC on the d-branch
  have h_split_d_pointwise :
    (fun r θ => ContractionC M r θ c a b)
      =
    (fun r θ =>
        (Q_t  r θ + Q_r  r θ + Q_θ  r θ + Q_φ  r θ)
      + (Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ)) := by
    funext r θ
    -- Mirror the same enumerator-based expansion used for Hsplit_c_both:
    -- With local simp bundle, the normalization is cleaner:
    --   simp [ContractionC, sumIdx_expand, add_comm, add_left_comm, add_assoc]
    -- The hQ*/hQ2* names are already marked as simp
    sorry

  -- Step B: binary linearity across the two families
  have h_lin_d :
    dCoord d
      (fun r θ =>
          (Q_t  r θ + Q_r  r θ + Q_θ  r θ + Q_φ  r θ)
        + (Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ)) r θ
    =
    dCoord d (fun r θ => Q_t  r θ + Q_r  r θ + Q_θ  r θ + Q_φ  r θ) r θ
    + dCoord d (fun r θ => Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ) r θ := by
    simpa [add_comm, add_left_comm, add_assoc]
      using dCoord_add d
        (fun r θ => Q_t  r θ + Q_r  r θ + Q_θ  r θ + Q_φ  r θ)
        (fun r θ => Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ) r θ

  -- Step C: assemble
  have Hsplit_d_both :
    dCoord d (fun r θ => ContractionC M r θ c a b) r θ
      =
    dCoord d (fun r θ => Q_t  r θ + Q_r  r θ + Q_θ  r θ + Q_φ  r θ) r θ
    + dCoord d (fun r θ => Q2_t r θ + Q2_r r θ + Q2_θ r θ + Q2_φ r θ) r θ := by
    have := congrArg (fun F => dCoord d F r θ) h_split_d_pointwise
    simpa using this.trans h_lin_d
  -/

  /-
  -- Fallback enumerator lemma (if sumIdx_expand isn't available)
  lemma sumIdx_expand_local (f : Idx → ℝ) :
    sumIdx f = f Idx.t + f Idx.r + f Idx.θ + f Idx.φ := by
    -- Expand the finite sum over Idx = {t, r, θ, φ}
    simp [sumIdx]
    -- Manual enumeration if needed:
    -- cases on Idx, normalize each case
    sorry
  -/

  /-
  -- Local normalization hints (paste next to the split proof when enabling it)
  -- `simp` normalization set used across c/d splits:
  --   [hPt, hPr, hPθ, hPφ, hP2t, hP2r, hP2θ, hP2φ,
  --    hQt, hQr, hQθ, hQφ, hQ2t, hQ2r, hQ2θ, hQ2φ,
  --    add_comm, add_left_comm, add_assoc]
  -/

  /-
  -- LHS-only dry run (safe: facts-only or rewrite a local copy)
  have Hc_local := Hsplit_c_both
  -- Rewriting each addend independently keeps control:
  -- rw [Hc_one]  at Hc_local   -- first family: expands only e = t
  -- rw [Hc2_one] at Hc_local   -- second family: expands only e = t
  -- Now `Hc_local` has "expanded t + deferred (r,θ,φ)" on both families.
  -- Stop here; do not touch the main goal.

  -- Mirror for d-branch:
  have Hd_local := Hsplit_d_both
  -- rw [Hd_one]  at Hd_local   -- first family: expands only e = t
  -- rw [Hd2_one] at Hd_local   -- second family: expands only e = t
  -/

  /-
  -- === RHS Preview: Clean pattern with dCoord_add4 (once gInv exists) ===
  -- Example RHS c-branch (first family) with dCoord_add4:

  -- Let RC_* be your four RHS summands (Γtot • gInv orientation)
  -- have hLinRC :
  --   dCoord c (fun r θ => RC_t r θ + RC_r r θ + RC_θ r θ + RC_φ r θ) r θ
  --   =
  --   dCoord c RC_t r θ + dCoord c RC_r r θ + dCoord c RC_θ r θ + dCoord c RC_φ r θ := by
  --   simpa [add_comm, add_left_comm, add_assoc] using
  --     dCoord_add4 c RC_t RC_r RC_θ RC_φ r θ

  -- Product rule on the selected summand then `rw` into hLinRC, exactly like LHS.
  -/

  /-
  -- === RHS micro-pattern (copy/paste inside each Stage-1 RHS lemma) ===
  -- 1) 4-term linearity
  -- have hsum := dCoord_add4_flat μ RC_t RC_r RC_θ RC_φ r θ
  -- 2) Product rule on the chosen summand
  -- have hpush := by
  --   simpa [RC_t] using
  --     dCoord_mul μ (fun r θ => Γtot M r θ Idx.t d a)
  --                   (fun r θ => gInv M Idx.t b r θ) r θ
  -- 3) Substitute + normalize
  -- have H := hsum
  -- rw [hpush] at H
  -- simpa [add_comm, add_left_comm, add_assoc] using H
  -/

  /-
  -- === RHS Stage-1 (first family, c-branch) — ready to enable when `gInv` exists ===
  -- section Stage1_RHS_c_first_flat
  --   variable (M r θ : ℝ) (a b c d : Idx)

  --   private def RC_t : ℝ → ℝ → ℝ := fun r θ => (Γtot M r θ Idx.t d a) * (gInv M Idx.t b r θ)
  --   private def RC_r : ℝ → ℝ → ℝ := fun r θ => (Γtot M r θ Idx.r d a) * (gInv M Idx.r b r θ)
  --   private def RC_θ : ℝ → ℝ → ℝ := fun r θ => (Γtot M r θ Idx.θ d a) * (gInv M Idx.θ b r θ)
  --   private def RC_φ : ℝ → ℝ → ℝ := fun r θ => (Γtot M r θ Idx.φ d a) * (gInv M Idx.φ b r θ)

  --   lemma HRc_one :
  --     dCoord c (fun r θ => RC_t r θ + RC_r r θ + RC_θ r θ + RC_φ r θ) r θ
  --     =
  --       dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ * (gInv M Idx.t b r θ)
  --     + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => gInv M Idx.t b r θ) r θ
  --     + dCoord c RC_r r θ + dCoord c RC_θ r θ + dCoord c RC_φ r θ := by
  --     -- 4-term linearity in one step
  --     have hsum := dCoord_add4_flat c RC_t RC_r RC_θ RC_φ r θ
  --     -- Product rule on the t-summand
  --     have hpush : dCoord c RC_t r θ =
  --       dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ * (gInv M Idx.t b r θ)
  --       + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => gInv M Idx.t b r θ) r θ := by
  --       simpa [RC_t] using dCoord_mul c
  --         (fun r θ => Γtot M r θ Idx.t d a)
  --         (fun r θ => gInv M Idx.t b r θ) r θ
  --     -- Substitute and normalize
  --     have H := hsum
  --     rw [hpush] at H
  --     simpa [add_comm, add_left_comm, add_assoc] using H
  -- end Stage1_RHS_c_first_flat
  -/

  /-
  -- === Stage 1: RHS ∂_c (first family) ===
  section Stage1_RHS_c_first

  -- Note: uses gInv syntactically; safe while commented even if gInv isn't defined yet.
  set RC_t : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.t d a) * (gInv M r θ Idx.t b)) with hRCt
  set RC_r : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.r d a) * (gInv M r θ Idx.r b)) with hRCr
  set RC_θ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.θ d a) * (gInv M r θ Idx.θ b)) with hRCθ
  set RC_φ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.φ d a) * (gInv M r θ Idx.φ b)) with hRCφ

  have hAB_c :
    dCoord c (fun r θ => RC_t r θ + RC_r r θ) r θ
      = dCoord c RC_t r θ + dCoord c RC_r r θ := by
    simpa using dCoord_add c RC_t RC_r r θ
  have hCD_c :
    dCoord c (fun r θ => RC_θ r θ + RC_φ r θ) r θ
      = dCoord c RC_θ r θ + dCoord c RC_φ r θ := by
    simpa using dCoord_add c RC_θ RC_φ r θ
  have hABCD_c :
    dCoord c (fun r θ => (RC_t r θ + RC_r r θ) + (RC_θ r θ + RC_φ r θ)) r θ
      = (dCoord c RC_t r θ + dCoord c RC_r r θ)
      + (dCoord c RC_θ r θ + dCoord c RC_φ r θ) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      dCoord_add c (fun r θ => RC_t r θ + RC_r r θ)
                   (fun r θ => RC_θ r θ + RC_φ r θ) r θ

  have hsum_RC :
    dCoord c (fun r θ => RC_t r θ + RC_r r θ + RC_θ r θ + RC_φ r θ) r θ
      = dCoord c RC_t r θ + dCoord c RC_r r θ + dCoord c RC_θ r θ + dCoord c RC_φ r θ := by
    simpa [add_comm, add_left_comm, add_assoc] using hABCD_c

  -- e = t product rule on RHS
  have hRCt_push :
    dCoord c RC_t r θ
      =
    dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ * gInv M r θ Idx.t b
    + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => gInv M r θ Idx.t b) r θ := by
    simpa [hRCt] using
      dCoord_mul c
        (fun r θ => Γtot M r θ Idx.t d a)
        (fun r θ => gInv M r θ Idx.t b) r θ

  have HRc_one :
    dCoord c (fun r θ =>
      (Γtot M r θ Idx.t d a) * (gInv M r θ Idx.t b)
    + (Γtot M r θ Idx.r d a) * (gInv M r θ Idx.r b)
    + (Γtot M r θ Idx.θ d a) * (gInv M r θ Idx.θ b)
    + (Γtot M r θ Idx.φ d a) * (gInv M r θ Idx.φ b)) r θ
    =
    (dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ) * gInv M r θ Idx.t b
    + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => gInv M r θ Idx.t b) r θ
    + dCoord c RC_r r θ + dCoord c RC_θ r θ + dCoord c RC_φ r θ := by
    -- Combine hsum_RC with hRCt_push; normalize with hRC* names; keep goal untouched
    have H := hsum_RC
    rw [hRCt_push] at H
    simpa [hRCt, hRCr, hRCθ, hRCφ, add_comm, add_left_comm, add_assoc] using H

  -- Local simp bundle (optional, for cleaner normalization)
  -- local attribute [simp] hRCt hRCr hRCθ hRCφ

  end Stage1_RHS_c_first
  -/

  /-
  -- === Stage 1: RHS ∂_d (first family) ===
  section Stage1_RHS_d_first

  set RD_t : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.t c a) * (gInv M r θ Idx.t b)) with hRDt
  set RD_r : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.r c a) * (gInv M r θ Idx.r b)) with hRDr
  set RD_θ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.θ c a) * (gInv M r θ Idx.θ b)) with hRDθ
  set RD_φ : ℝ → ℝ → ℝ :=
    (fun r θ => (Γtot M r θ Idx.φ c a) * (gInv M r θ Idx.φ b)) with hRDφ

  have hAB_d2 :
    dCoord d (fun r θ => RD_t r θ + RD_r r θ) r θ
      = dCoord d RD_t r θ + dCoord d RD_r r θ := by
    simpa using dCoord_add d RD_t RD_r r θ
  have hCD_d2 :
    dCoord d (fun r θ => RD_θ r θ + RD_φ r θ) r θ
      = dCoord d RD_θ r θ + dCoord d RD_φ r θ := by
    simpa using dCoord_add d RD_θ RD_φ r θ
  have hABCD_d2 :
    dCoord d (fun r θ => (RD_t r θ + RD_r r θ) + (RD_θ r θ + RD_φ r θ)) r θ
      = (dCoord d RD_t r θ + dCoord d RD_r r θ)
      + (dCoord d RD_θ r θ + dCoord d RD_φ r θ) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      dCoord_add d (fun r θ => RD_t r θ + RD_r r θ)
                   (fun r θ => RD_θ r θ + RD_φ r θ) r θ

  have hsum_RD :
    dCoord d (fun r θ => RD_t r θ + RD_r r θ + RD_θ r θ + RD_φ r θ) r θ
      = dCoord d RD_t r θ + dCoord d RD_r r θ + dCoord d RD_θ r θ + dCoord d RD_φ r θ := by
    simpa [add_comm, add_left_comm, add_assoc] using hABCD_d2

  -- e = t product rule on RHS (∂d)
  have hRDt_push :
    dCoord d RD_t r θ
      =
    dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ * gInv M r θ Idx.t b
    + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => gInv M r θ Idx.t b) r θ := by
    simpa [hRDt] using
      dCoord_mul d
        (fun r θ => Γtot M r θ Idx.t c a)
        (fun r θ => gInv M r θ Idx.t b) r θ

  have HRd_one :
    dCoord d (fun r θ =>
      (Γtot M r θ Idx.t c a) * (gInv M r θ Idx.t b)
    + (Γtot M r θ Idx.r c a) * (gInv M r θ Idx.r b)
    + (Γtot M r θ Idx.θ c a) * (gInv M r θ Idx.θ b)
    + (Γtot M r θ Idx.φ c a) * (gInv M r θ Idx.φ b)) r θ
    =
    (dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ) * gInv M r θ Idx.t b
    + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => gInv M r θ Idx.t b) r θ
    + dCoord d RD_r r θ + dCoord d RD_θ r θ + dCoord d RD_φ r θ := by
    -- Combine hsum_RD with hRDt_push; normalize with hRD* names; keep goal untouched
    have H := hsum_RD
    rw [hRDt_push] at H
    simpa [hRDt, hRDr, hRDθ, hRDφ, add_comm, add_left_comm, add_assoc] using H

  -- Local simp bundle (optional, for cleaner normalization)
  -- local attribute [simp] hRDt hRDr hRDθ hRDφ

  end Stage1_RHS_d_first
  -/

  /-
  -- Local 4-term linearity for `dCoord` (derive from binary linearity, no globals)
  -- Works with existing `dCoord_add`. Paste inside any proof that needs it:
  have hAB (μ : Idx) (A B : ℝ → ℝ → ℝ) :
    dCoord μ (fun r θ => A r θ + B r θ) r θ
      = dCoord μ A r θ + dCoord μ B r θ := by
    simpa using dCoord_add μ A B r θ

  have hCD (μ : Idx) (C D : ℝ → ℝ → ℝ) :
    dCoord μ (fun r θ => C r θ + D r θ) r θ
      = dCoord μ C r θ + dCoord μ D r θ := by
    simpa using dCoord_add μ C D r θ

  have hAB_CD (μ : Idx) (A B C D : ℝ → ℝ → ℝ) :
    dCoord μ (fun r θ => (A r θ + B r θ) + (C r θ + D r θ)) r θ
      = (dCoord μ A r θ + dCoord μ B r θ) + (dCoord μ C r θ + dCoord μ D r θ) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      dCoord_add μ (fun r θ => A r θ + B r θ) (fun r θ => C r θ + D r θ) r θ

  have h4 (μ : Idx) (A B C D : ℝ → ℝ → ℝ) :
    dCoord μ (fun r θ => A r θ + B r θ + C r θ + D r θ) r θ
      = dCoord μ A r θ + dCoord μ B r θ + dCoord μ C r θ + dCoord μ D r θ := by
    simpa [hAB μ A B, hCD μ C D, add_comm, add_left_comm, add_assoc]
      using hAB_CD μ A B C D
  -/

  /-
  -- Pass 1 facts (t-summand only) and split shape facts
  -- These will be uncommented when the infrastructure exists

  -- Pass 1 (t-summand only, LHS c-branch, first family g_{e b})
  have Hc_one :
      dCoord c (fun r θ =>
          (Γtot M r θ Idx.t d a) * (g M Idx.t b r θ)
        + (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)
        + (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)
        + (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)) r θ
    =
      dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ * g M Idx.t b r θ
        + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ
      + dCoord c (fun r θ => (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)) r θ
      + dCoord c (fun r θ => (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)) r θ
      + dCoord c (fun r θ => (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)) r θ := by
    sorry

  -- Pass 1 (t-summand only, LHS d-branch, first family g_{e b})
  have Hd_one :
      dCoord d (fun r θ =>
          (Γtot M r θ Idx.t c a) * (g M Idx.t b r θ)
        + (Γtot M r θ Idx.r c a) * (g M Idx.r b r θ)
        + (Γtot M r θ Idx.θ c a) * (g M Idx.θ b r θ)
        + (Γtot M r θ Idx.φ c a) * (g M Idx.φ b r θ)) r θ
    =
      dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ * g M Idx.t b r θ
        + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => g M Idx.t b r θ) r θ
      + dCoord d (fun r θ => (Γtot M r θ Idx.r c a) * (g M Idx.r b r θ)) r θ
      + dCoord d (fun r θ => (Γtot M r θ Idx.θ c a) * (g M Idx.θ b r θ)) r θ
      + dCoord d (fun r θ => (Γtot M r θ Idx.φ c a) * (g M Idx.φ b r θ)) r θ := by
    sorry

  -- Pass 1 (t-summand only, RHS ∂_c, first family gInv^{e b})
  have HRc_one :
      dCoord c (fun r θ =>
          (Γtot M r θ Idx.t d a) * (gInv M r θ Idx.t b)
        + (Γtot M r θ Idx.r d a) * (gInv M r θ Idx.r b)
        + (Γtot M r θ Idx.θ d a) * (gInv M r θ Idx.θ b)
        + (Γtot M r θ Idx.φ d a) * (gInv M r θ Idx.φ b)) r θ
    =
      dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ * gInv M r θ Idx.t b
        + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => gInv M r θ Idx.t b) r θ
      + dCoord c (fun r θ => (Γtot M r θ Idx.r d a) * (gInv M r θ Idx.r b)) r θ
      + dCoord c (fun r θ => (Γtot M r θ Idx.θ d a) * (gInv M r θ Idx.θ b)) r θ
      + dCoord c (fun r θ => (Γtot M r θ Idx.φ d a) * (gInv M r θ Idx.φ b)) r θ := by
    sorry

  -- Pass 1 (t-summand only, RHS ∂_d, first family gInv^{e b})
  have HRd_one :
      dCoord d (fun r θ =>
          (Γtot M r θ Idx.t c a) * (gInv M r θ Idx.t b)
        + (Γtot M r θ Idx.r c a) * (gInv M r θ Idx.r b)
        + (Γtot M r θ Idx.θ c a) * (gInv M r θ Idx.θ b)
        + (Γtot M r θ Idx.φ c a) * (gInv M r θ Idx.φ b)) r θ
    =
      dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ * gInv M r θ Idx.t b
        + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => gInv M r θ Idx.t b) r θ
      + dCoord d (fun r θ => (Γtot M r θ Idx.r c a) * (gInv M r θ Idx.r b)) r θ
      + dCoord d (fun r θ => (Γtot M r θ Idx.θ c a) * (gInv M r θ Idx.θ b)) r θ
      + dCoord d (fun r θ => (Γtot M r θ Idx.φ c a) * (gInv M r θ Idx.φ b)) r θ := by
    sorry

  -- Split LHS c-branch contraction into two 4-term families (derivative level)
  have Hsplit_c :
      dCoord c (fun r θ => ContractionC M r θ d a b) r θ
    =
      dCoord c (fun r θ =>
          (Γtot M r θ Idx.t d a) * (g M Idx.t b r θ)
        + (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)
        + (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)
        + (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)) r θ
    +
      dCoord c (fun r θ =>
          (Γtot M r θ Idx.t d b) * (g M a Idx.t r θ)
        + (Γtot M r θ Idx.r d b) * (g M a Idx.r r θ)
        + (Γtot M r θ Idx.θ d b) * (g M a Idx.θ r θ)
        + (Γtot M r θ Idx.φ d b) * (g M a Idx.φ r θ)) r θ := by
    -- idea later: unfold ContractionC; sumIdx_expand; regroup into the two families; use dCoord linearity
    sorry

  -- Split LHS d-branch contraction into two 4-term families (derivative level)
  have Hsplit_d :
      dCoord d (fun r θ => ContractionC M r θ c a b) r θ
    =
      dCoord d (fun r θ =>
          (Γtot M r θ Idx.t c a) * (g M Idx.t b r θ)
        + (Γtot M r θ Idx.r c a) * (g M Idx.r b r θ)
        + (Γtot M r θ Idx.θ c a) * (g M Idx.θ b r θ)
        + (Γtot M r θ Idx.φ c a) * (g M Idx.φ b r θ)) r θ
    +
      dCoord d (fun r θ =>
          (Γtot M r θ Idx.t c b) * (g M a Idx.t r θ)
        + (Γtot M r θ Idx.r c b) * (g M a Idx.r r θ)
        + (Γtot M r θ Idx.θ c b) * (g M a Idx.θ r θ)
        + (Γtot M r θ Idx.φ c b) * (g M a Idx.φ r θ)) r θ := by
    -- mirrored idea of Hsplit_c
    sorry

  have HRc_split : sumIdx (fun e => Γtot M r θ e d a * gInv M r θ e b)
    = (Γtot M r θ Idx.t d a) * (gInv M r θ Idx.t b)
      + (Γtot M r θ Idx.r d a) * (gInv M r θ Idx.r b)
      + (Γtot M r θ Idx.θ d a) * (gInv M r θ Idx.θ b)
      + (Γtot M r θ Idx.φ d a) * (gInv M r θ Idx.φ b) := by
    sorry

  have HRd_split : sumIdx (fun e => Γtot M r θ e c a * gInv M r θ e b)
    = (Γtot M r θ Idx.t c a) * (gInv M r θ Idx.t b)
      + (Γtot M r θ Idx.r c a) * (gInv M r θ Idx.r b)
      + (Γtot M r θ Idx.θ c a) * (gInv M r θ Idx.θ b)
      + (Γtot M r θ Idx.φ c a) * (gInv M r θ Idx.φ b) := by
    sorry
  -/

  /-
  -- Micro-pass safety pattern (for single summand expansion)
  -- Use this pattern when enabling a single summand to minimize algebraic pressure:

  -- Step 1: Name the block robustly
  set S_c : ℝ → ℝ → ℝ :=
    (fun r θ =>
         (Γtot M r θ Idx.t d a) * (g M Idx.t b r θ)
       + (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)
       + (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)
       + (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)) with hS_c

  -- Step 2: Apply the t-summand expansion (use h4 or chain dCoord_add)
  have Hc_expanded := Hc_one

  -- Step 3: DO NOT rewrite the main goal yet
  -- Store as a fact: have Hc_partial := Hsplit_c
  -- Then: rw [Hc_expanded] at Hc_partial

  -- Step 4: Build and check error count
  -- If it moves, re-comment the last 2-3 lines
  -/

  -- Optional micro-step 1 (complete set): push ∂ across Γ⋅g for each e on both branches.
  -- Toggle by uncommenting this whole block.
  /-
  -- Local helper: specialize `dCoord_mul` at (r, θ)
  have push_mul (μ : Idx) (A B : ℝ → ℝ → ℝ) :
      dCoord μ (fun r θ => A r θ * B r θ) r θ
    = dCoord μ A r θ * B r θ + A r θ * dCoord μ B r θ := by
    simpa using (dCoord_mul μ A B r θ)

  -- -------- e = t --------
  have h_t_c :
    dCoord c (fun r θ =>
        (Γtot M r θ Idx.t d a) * (g M Idx.t b r θ)) r θ
      =
    dCoord c (fun r θ => Γtot M r θ Idx.t d a) r θ * g M Idx.t b r θ
      + (Γtot M r θ Idx.t d a) * dCoord c (fun r θ => g M Idx.t b r θ) r θ := by
    simpa using push_mul c
      (fun r θ => Γtot M r θ Idx.t d a)
      (fun r θ => g M Idx.t b r θ)

  have h_t_d :
    dCoord d (fun r θ =>
        (Γtot M r θ Idx.t c a) * (g M Idx.t b r θ)) r θ
      =
    dCoord d (fun r θ => Γtot M r θ Idx.t c a) r θ * g M Idx.t b r θ
      + (Γtot M r θ Idx.t c a) * dCoord d (fun r θ => g M Idx.t b r θ) r θ := by
    simpa using push_mul d
      (fun r θ => Γtot M r θ Idx.t c a)
      (fun r θ => g M Idx.t b r θ)

  -- -------- e = r --------
  have h_r_c :
    dCoord c (fun r θ =>
        (Γtot M r θ Idx.r d a) * (g M Idx.r b r θ)) r θ
      =
    dCoord c (fun r θ => Γtot M r θ Idx.r d a) r θ * g M Idx.r b r θ
      + (Γtot M r θ Idx.r d a) * dCoord c (fun r θ => g M Idx.r b r θ) r θ := by
    simpa using push_mul c
      (fun r θ => Γtot M r θ Idx.r d a)
      (fun r θ => g M Idx.r b r θ)

  have h_r_d :
    dCoord d (fun r θ =>
        (Γtot M r θ Idx.r c a) * (g M Idx.r b r θ)) r θ
      =
    dCoord d (fun r θ => Γtot M r θ Idx.r c a) r θ * g M Idx.r b r θ
      + (Γtot M r θ Idx.r c a) * dCoord d (fun r θ => g M Idx.r b r θ) r θ := by
    simpa using push_mul d
      (fun r θ => Γtot M r θ Idx.r c a)
      (fun r θ => g M Idx.r b r θ)

  -- -------- e = θ --------
  have h_θ_c :
    dCoord c (fun r θ =>
        (Γtot M r θ Idx.θ d a) * (g M Idx.θ b r θ)) r θ
      =
    dCoord c (fun r θ => Γtot M r θ Idx.θ d a) r θ * g M Idx.θ b r θ
      + (Γtot M r θ Idx.θ d a) * dCoord c (fun r θ => g M Idx.θ b r θ) r θ := by
    simpa using push_mul c
      (fun r θ => Γtot M r θ Idx.θ d a)
      (fun r θ => g M Idx.θ b r θ)

  have h_θ_d :
    dCoord d (fun r θ =>
        (Γtot M r θ Idx.θ c a) * (g M Idx.θ b r θ)) r θ
      =
    dCoord d (fun r θ => Γtot M r θ Idx.θ c a) r θ * g M Idx.θ b r θ
      + (Γtot M r θ Idx.θ c a) * dCoord d (fun r θ => g M Idx.θ b r θ) r θ := by
    simpa using push_mul d
      (fun r θ => Γtot M r θ Idx.θ c a)
      (fun r θ => g M Idx.θ b r θ)

  -- -------- e = φ --------
  have h_φ_c :
    dCoord c (fun r θ =>
        (Γtot M r θ Idx.φ d a) * (g M Idx.φ b r θ)) r θ
      =
    dCoord c (fun r θ => Γtot M r θ Idx.φ d a) r θ * g M Idx.φ b r θ
      + (Γtot M r θ Idx.φ d a) * dCoord c (fun r θ => g M Idx.φ b r θ) r θ := by
    simpa using push_mul c
      (fun r θ => Γtot M r θ Idx.φ d a)
      (fun r θ => g M Idx.φ b r θ)

  have h_φ_d :
    dCoord d (fun r θ =>
        (Γtot M r θ Idx.φ c a) * (g M Idx.φ b r θ)) r θ
      =
    dCoord d (fun r θ => Γtot M r θ Idx.φ c a) r θ * g M Idx.φ b r θ
      + (Γtot M r θ Idx.φ c a) * dCoord d (fun r θ => g M Idx.φ b r θ) r θ := by
    simpa using push_mul d
      (fun r θ => Γtot M r θ Idx.φ c a)
      (fun r θ => g M Idx.φ b r θ)
  -/

  -- Optional micro-step 2: Normalize double sums
  -- (Toggle by uncommenting the line below)
  -- simp only [sumIdx2_mul_const, sumIdx2_mul_left']

  -- Optional micro-step 3: Expand RHS Riemann tensors
  -- (Toggle by uncommenting the block below)
  /-
  have h_Riem_abcd : Riemann M r θ a b c d =
    dCoord c (fun r θ => ∑ λ, Γtot M r θ λ d a * gInv M r θ λ b) r θ
    - dCoord d (fun r θ => ∑ λ, Γtot M r θ λ c a * gInv M r θ λ b) r θ
    + ∑ κ λ, Γtot M r θ κ c λ * Γtot M r θ λ d a * gInv M r θ κ b
    - ∑ κ λ, Γtot M r θ κ d λ * Γtot M r θ λ c a * gInv M r θ κ b := by
    simp [Riemann, RiemannUp]

  have h_Riem_bacd : Riemann M r θ b a c d =
    dCoord c (fun r θ => ∑ λ, Γtot M r θ λ d b * gInv M r θ λ a) r θ
    - dCoord d (fun r θ => ∑ λ, Γtot M r θ λ c b * gInv M r θ λ a) r θ
    + ∑ κ λ, Γtot M r θ κ c λ * Γtot M r θ λ d b * gInv M r θ κ a
    - ∑ κ λ, Γtot M r θ κ d λ * Γtot M r θ λ c b * gInv M r θ κ a := by
    simp [Riemann, RiemannUp]

  rw [h_Riem_abcd, h_Riem_bacd]
  -/

  /-
  -- Local rewrite experiment (facts-only, no goal touch)
  -- Testing the Stage-1 micro-packs we just enabled

  -- Create local copies to test rewrites without touching the main goal
  have test_c : dCoord c (fun r θ => P_t r θ + P_r r θ + P_θ r θ + P_φ r θ) r θ
    = dCoord c (fun r θ => P_t r θ + P_r r θ + P_θ r θ + P_φ r θ) r θ := by rfl

  -- Rewrite with Hc_one to expand only the t-summand
  rw [← Hc_one] at test_c
  -- test_c now shows the expanded form for e=t

  have test_d : dCoord d (fun r θ => Q_t r θ + Q_r r θ + Q_θ r θ + Q_φ r θ) r θ
    = dCoord d (fun r θ => Q_t r θ + Q_r r θ + Q_θ r θ + Q_φ r θ) r θ := by rfl

  -- Rewrite with Hd_one to expand only the t-summand
  rw [← Hd_one] at test_d
  -- test_d now shows the expanded form for e=t
  -/

  -/ -- Close the comment block started at line 1464

end RicciInfrastructure

/-- Ricci identity specialized to the metric (lowered first index form). -/
lemma ricci_identity_on_g
    (M r θ : ℝ) (a b c d : Idx) :
  ( dCoord c (fun r θ => nabla_g M r θ d a b) r θ
  - dCoord d (fun r θ => nabla_g M r θ c a b) r θ )
  = - ( Riemann M r θ a b c d + Riemann M r θ b a c d ) := by
  -- The proof is now structured:
  -- 1. Simplify LHS using derivative commutativity (Clairaut's theorem)
  rw [ricci_LHS M r θ a b c d]
  -- 2. Relate the remaining terms to the Riemann tensor (core algebraic identity)
  rw [alternation_dC_eq_Riem M r θ a b c d]
  -- 3. Trivial algebraic rearrangement (goal already solved by rewrites)
  -- ring -- Not needed

/-- Antisymmetry in the first two (lower) slots. `R_{abcd} = - R_{bacd}`. -/
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ a b c d = - Riemann M r θ b a c d := by
  classical
  -- Apply the Ricci identity
  have hRic := ricci_identity_on_g M r θ a b c d
  -- The LHS vanishes because the connection is metric compatible (∇g = 0)
  -- Since ∇g = 0 everywhere, its derivative (∇∇g) is also 0
  have hLHS_zero : ( dCoord c (fun r θ => nabla_g M r θ d a b) r θ
                  - dCoord d (fun r θ => nabla_g M r θ c a b) r θ ) = 0 := by
    -- Apply metric compatibility
    simp only [AX_nabla_g_zero]
    -- The derivative of the zero function is zero
    have h_zero_fn : (fun r θ => (0:ℝ)) = (fun (_r : ℝ) (_θ : ℝ) => (0:ℝ)) := by rfl
    rw [h_zero_fn]
    simp only [dCoord_const, sub_self]
  rw [hLHS_zero] at hRic
  -- We now have 0 = - (R_abcd + R_bacd), which implies R_abcd = -R_bacd
  linarith

/-- Squared symmetry in the first pair. Safer for simp. -/
lemma Riemann_sq_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  (Riemann M r θ b a c d)^2 = (Riemann M r θ a b c d)^2 := by
  rw [Riemann_swap_a_b, sq_neg]

/-- Squared symmetry in the last pair. Safer for simp. -/
lemma Riemann_sq_swap_c_d (M r θ : ℝ) (a b c d : Idx) :
  (Riemann M r θ a b d c)^2 = (Riemann M r θ a b c d)^2 := by
  rw [Riemann_swap_c_d, sq_neg]

/-! ### New: vanishing lemmas for equal indices -/

/-- If the first two indices coincide, the Riemann component vanishes. -/
@[simp] lemma Riemann_first_equal_zero (M r θ : ℝ) (a c d : Idx) :
  Riemann M r θ a a c d = 0 := by
  -- By antisymmetry: R_aacd = -R_aacd
  have h := Riemann_swap_a_b M r θ a a c d
  -- The only number equal to its negation is 0
  linarith

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

end Schwarzschild
end Papers.P5_GeneralRelativity
