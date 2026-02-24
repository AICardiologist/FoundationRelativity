/-
  Paper 47: Fontaine-Mazur Conjecture — Lean 4 Formalization
  FM3_Descent.lean: Theorem FM3 — State Space Descent to ℚ (BISH)

  Main result (NOVEL contribution of Paper 47):
    Under geometric origin, the undecidable ℚ_p linear algebra on D_dR
    descends to decidable ℚ linear algebra on the rational skeleton
    via Faltings' comparison theorem.

  Structure:
    1. Skeleton has DecidableEq (axiom)
    2. Linear maps on skeleton are decidable (f = g ∨ f ≠ g)
    3. Abstract D_dR linear algebra requires LPO (contrast)
    4. Geometric origin kills LPO via Faltings comparison

  Custom axiom: baseChange_faithful (from Defs.lean).
  No sorry.
-/

import Papers.P47_FM.Defs
import Papers.P47_FM.FM1_Unramified

noncomputable section

open TensorProduct

namespace Papers.P47

-- ============================================================
-- §1. Skeleton Decidability
-- ============================================================

/-- The rational skeleton has decidable equality.
    This is the foundation of FM3: ℚ-vector spaces are decidable. -/
def geometric_descent_decidable :
    DecidableEq deRham_rational_skeleton :=
  skeleton_decidableEq

-- ============================================================
-- §2. Skeleton Linear Algebra is Decidable
-- ============================================================

/-- Linear maps on the skeleton are decidable (Prop form).
    Since the skeleton has DecidableEq and is finite-dimensional
    over ℚ, linear map equality is decidable.

    Mathematical argument: two linear maps f, g are equal iff they
    agree on a basis. The skeleton has a finite basis (FiniteDimensional),
    and each basis vector comparison is decidable (DecidableEq).
    Finite conjunction of decidable propositions is decidable.

    The by_cases here resolves via skeleton_linearMap_decidableEq,
    not via Classical.dec. -/
theorem skeleton_linear_algebra_decidable
    (f g : deRham_rational_skeleton →ₗ[ℚ] deRham_rational_skeleton) :
    f = g ∨ f ≠ g :=
  match skeleton_linearMap_decidableEq f g with
  | .isTrue h => Or.inl h
  | .isFalse h => Or.inr h

-- ============================================================
-- §3. Abstract D_dR Requires LPO (Contrast)
-- ============================================================

/-- **The zero-encoding for ℚ_p linear maps.**
    For x ∈ ℚ_p, construct a linear map on (ℚ_p)² that is zero iff x = 0.
    Uses the same encoding as Paper 45 C2. -/
def encodingZeroMap (x : Q_p) :
    (Fin 2 → Q_p) →ₗ[Q_p] (Fin 2 → Q_p) where
  toFun v := fun i =>
    match i with
    | 0 => 0
    | 1 => x * v 0
  map_add' u v := by
    ext i; fin_cases i
    · simp
    · simp; ring
  map_smul' c v := by
    ext i; fin_cases i
    · simp [smul_eq_mul]
    · simp [smul_eq_mul]; ring

/-- Basis vector e₀ = (1, 0) for encoding extraction. -/
private def e₀' : Fin 2 → Q_p := fun i => if i = 0 then 1 else 0

/-- The zero-encoding is zero iff x = 0. -/
theorem encodingZeroMap_eq_zero_iff (x : Q_p) :
    encodingZeroMap x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have key : encodingZeroMap x e₀' = 0 := by
      rw [h]; simp [LinearMap.zero_apply]
    have h1 : (encodingZeroMap x e₀') (1 : Fin 2) = (0 : Fin 2 → Q_p) (1 : Fin 2) :=
      congr_fun key 1
    simp [encodingZeroMap, e₀'] at h1
    exact h1
  · intro hx
    ext v i
    fin_cases i <;> simp [encodingZeroMap, hx]

/-- **Abstract ℚ_p linear algebra requires LPO.**
    Deciding whether a ℚ_p-linear map is zero requires testing
    elements of ℚ_p for zero, which requires LPO.

    This provides the CONTRAST with FM3's geometric decidability:
    without geometric origin, LPO is unavoidable. -/
theorem abstract_linear_algebra_requires_LPO :
    (∀ (f : (Fin 2 → Q_p) →ₗ[Q_p] (Fin 2 → Q_p)),
      f = 0 ∨ f ≠ 0) → LPO_Q_p := by
  intro oracle x
  have hdec := oracle (encodingZeroMap x)
  rcases hdec with h_zero | h_nonzero
  · left; exact (encodingZeroMap_eq_zero_iff x).mp h_zero
  · right; exact fun hx => h_nonzero ((encodingZeroMap_eq_zero_iff x).mpr hx)

-- ============================================================
-- §4. MAIN RESULT: Geometric Origin Kills LPO
-- ============================================================

/-- **Theorem FM3 (State Space Descent — MAIN RESULT).**
    Under geometric origin, endomorphisms of D_dR that come from
    the rational skeleton (via base change through Faltings comparison)
    have decidable equality (in Prop form: f = g ∨ f ≠ g).

    Proof:
    1. Extract f₀, g₀ from the skeleton
    2. f = g iff f₀ ⊗ 1 = g₀ ⊗ 1 (Faltings is isomorphism)
    3. f₀ ⊗ 1 = g₀ ⊗ 1 iff f₀ = g₀ (base change is faithful)
    4. f₀ = g₀ is decidable (skeleton has DecidableEq) -/
theorem geometric_origin_kills_LPO_state_space
    (f g : D_dR →ₗ[Q_p] D_dR)
    (f₀ g₀ : deRham_rational_skeleton →ₗ[ℚ] deRham_rational_skeleton)
    (hf : faltings_comparison.toLinearMap ∘ₗ (f₀.baseChange Q_p) ∘ₗ
            faltings_comparison.symm.toLinearMap = f)
    (hg : faltings_comparison.toLinearMap ∘ₗ (g₀.baseChange Q_p) ∘ₗ
            faltings_comparison.symm.toLinearMap = g) :
    f = g ∨ f ≠ g := by
  -- by_cases on skeleton linear maps uses skeleton_linearMap_decidableEq (not Classical.dec)
  haveI := skeleton_linearMap_decidableEq
  by_cases h : f₀ = g₀
  · -- f₀ = g₀ → f = g
    left
    rw [← hf, ← hg, h]
  · -- f₀ ≠ g₀ → f ≠ g
    right
    intro heq
    apply h
    apply baseChange_faithful
    -- From f = g and the conjugation, derive baseChange equality
    -- key: φ ∘ (f₀ ⊗ 1) ∘ φ⁻¹ = φ ∘ (g₀ ⊗ 1) ∘ φ⁻¹
    have key : faltings_comparison.toLinearMap ∘ₗ (f₀.baseChange Q_p) ∘ₗ
                 faltings_comparison.symm.toLinearMap =
               faltings_comparison.toLinearMap ∘ₗ (g₀.baseChange Q_p) ∘ₗ
                 faltings_comparison.symm.toLinearMap := by
      rw [hf, hg, heq]
    -- Cancel faltings_comparison on both sides
    -- key says: φ ∘ (f₀⊗1) ∘ φ⁻¹ = φ ∘ (g₀⊗1) ∘ φ⁻¹
    -- We need: f₀⊗1 = g₀⊗1
    -- key says: φ ∘ (f₀⊗1) ∘ φ⁻¹ = φ ∘ (g₀⊗1) ∘ φ⁻¹
    -- For any y in tensor product, apply key to φ(y):
    --   φ((f₀⊗1)(φ⁻¹(φ(y)))) = φ((g₀⊗1)(φ⁻¹(φ(y))))
    --   φ((f₀⊗1)(y)) = φ((g₀⊗1)(y))
    -- Then by injectivity of φ: (f₀⊗1)(y) = (g₀⊗1)(y)
    have h_eq : ∀ (y : Q_p ⊗[ℚ] deRham_rational_skeleton),
        (f₀.baseChange Q_p) y = (g₀.baseChange Q_p) y := by
      intro y
      -- Apply key to the arbitrary element y, going through φ⁻¹(φ(y)) = y
      have h1 : (faltings_comparison.toLinearMap ∘ₗ (f₀.baseChange Q_p) ∘ₗ
                   faltings_comparison.symm.toLinearMap) (faltings_comparison y) =
                (faltings_comparison.toLinearMap ∘ₗ (g₀.baseChange Q_p) ∘ₗ
                   faltings_comparison.symm.toLinearMap) (faltings_comparison y) := by
        rw [key]
      simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
                 LinearEquiv.symm_apply_apply] at h1
      exact faltings_comparison.injective h1
    exact LinearMap.ext h_eq

/-- **De-omniscientizing descent summary for FM3.**
    The abstract side requires LPO. The geometric side is BISH. -/
theorem FM3_descent_summary :
    -- Abstract ℚ_p linear algebra requires LPO
    ((∀ (f : (Fin 2 → Q_p) →ₗ[Q_p] (Fin 2 → Q_p)), f = 0 ∨ f ≠ 0) → LPO_Q_p) ∧
    -- Skeleton linear algebra is decidable (BISH)
    (∀ (f g : deRham_rational_skeleton →ₗ[ℚ] deRham_rational_skeleton),
      f = g ∨ f ≠ g) :=
  ⟨abstract_linear_algebra_requires_LPO, skeleton_linear_algebra_decidable⟩

end Papers.P47
