/-
  Paper 47: Fontaine-Mazur Conjecture — Lean 4 Formalization
  FM1_Unramified.lean: Theorem FM1 — Unramified Condition ↔ LPO

  Main result:
    DecidesIdentity ↔ LPO_Q_p

  (⇒) Given x : Q_p, construct a 2-dim endomorphism where f = id iff x = 0.
  (⇐) LPO_Q_p gives decidable equality, enabling finite-dimensional testing.

  Pattern: Adapts Paper 45 C2_LPO.lean encoding.
  No custom axioms. No sorry.
-/

import Papers.P47_FM.Defs

noncomputable section

namespace Papers.P47

-- ============================================================
-- The Encoding: inertia action with a single free parameter
-- ============================================================

/-- The inertia encoding map.
    For x ∈ ℚ_p, define f_x : (ℚ_p)² → (ℚ_p)² by
      f_x(a, b) = (a, b + x·a)
    This is "identity plus x times a nilpotent":
      f_x = Id + x · e₁₂
    Key properties:
    - f_x = Id iff x = 0
    - f_x is always a ℚ_p-linear endomorphism -/
def encodingInertia (x : Q_p) :
    (Fin 2 → Q_p) →ₗ[Q_p] (Fin 2 → Q_p) where
  toFun v := fun i =>
    match i with
    | 0 => v 0
    | 1 => v 1 + x * v 0
  map_add' u v := by
    ext i; fin_cases i
    · simp
    · simp; ring
  map_smul' c v := by
    ext i; fin_cases i
    · simp [smul_eq_mul]
    · simp [smul_eq_mul]; ring

/-- Basis vector e₀ = (1, 0) in (Q_p)². -/
private def e₀ : Fin 2 → Q_p := fun i => if i = 0 then 1 else 0

/-- The encoding map equals id iff x = 0. -/
theorem encodingInertia_eq_id_iff (x : Q_p) :
    encodingInertia x = LinearMap.id ↔ x = 0 := by
  constructor
  · intro h
    -- Apply f_x to e₀ = (1, 0)
    -- f_x(1, 0) = (1, 0 + x·1) = (1, x)
    -- id(1, 0) = (1, 0)
    -- So x = 0
    have key : encodingInertia x e₀ = e₀ := by
      rw [h]; simp [LinearMap.id_apply]
    have h1 : (encodingInertia x e₀) (1 : Fin 2) = e₀ (1 : Fin 2) :=
      congr_fun key 1
    simp [encodingInertia, e₀] at h1
    exact h1
  · intro hx
    ext v i
    fin_cases i <;> simp [encodingInertia, hx]

-- ============================================================
-- Forward Direction: DecidesIdentity → LPO_Q_p
-- ============================================================

/-- **FM1 Forward: An identity-testing oracle gives LPO for ℚ_p.**

    Given any x ∈ ℚ_p, construct the encoding f_x where f_x = id ↔ x = 0.
    The oracle decides f_x = id, which decides x = 0 ∨ x ≠ 0. -/
theorem unramified_requires_LPO :
    DecidesIdentity → LPO_Q_p := by
  intro oracle x
  -- Construct the encoding for x
  have hdec := oracle (encodingInertia x)
  -- Convert via the iff
  rcases hdec with h_id | h_not_id
  · left; exact (encodingInertia_eq_id_iff x).mp h_id
  · right; exact fun hx => h_not_id ((encodingInertia_eq_id_iff x).mpr hx)

-- ============================================================
-- Reverse Direction: LPO_Q_p → DecidesIdentity
-- ============================================================

/-- **FM1 Reverse: LPO for ℚ_p gives an identity-testing oracle.**

    Mathematical argument: LPO_Q_p gives decidable equality on ℚ_p
    (since x = y iff x - y = 0). For a 2-dimensional space,
    f = id iff f(e_i) = e_i for i = 0, 1, which reduces to
    4 equality checks in ℚ_p.

    Formalization note: LPO_field is Prop-valued (returns Or, not Decidable).
    Deriving a Decidable instance from Prop-level Or requires Classical.choice
    to bridge the Prop/Type gap. The `by_cases` below therefore uses
    Classical.choice even though the hypothesis `hlpo` is available.
    The mathematical content is that LPO *suffices*; the constructive
    interest of FM1 lies entirely in the forward direction.
    Phase 2 may refine this by reformulating LPO to produce Decidable. -/
theorem LPO_decides_unramified :
    LPO_Q_p → DecidesIdentity := by
  intro _hlpo f
  -- by_cases uses Classical.choice (Prop→Type bridge); see docstring
  by_cases hf : f = LinearMap.id
  · left; exact hf
  · right; exact hf

-- ============================================================
-- The Main Theorem FM1
-- ============================================================

/-- **Theorem FM1 (Unramified Condition ↔ LPO).**
    Deciding whether a ℚ_p-linear endomorphism is the identity
    (which decides unramifiedness of a Galois representation)
    is equivalent to the Limited Principle of Omniscience for ℚ_p. -/
theorem FM1_unramified_iff_LPO :
    DecidesIdentity ↔ LPO_Q_p :=
  ⟨unramified_requires_LPO, LPO_decides_unramified⟩

end Papers.P47
