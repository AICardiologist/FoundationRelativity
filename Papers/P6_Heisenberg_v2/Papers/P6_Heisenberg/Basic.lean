/-
Papers/P6_Heisenberg/Basic.lean
Paper 6 v2: Heisenberg Uncertainty — CRM formalization over Mathlib.

Defines operator expectation, variance, commutator, anticommutator,
and centered vectors for inner product spaces over ℂ.

All definitions use Mathlib's InnerProductSpace API — no custom axioms.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace Papers.P6_Heisenberg

open scoped ComplexConjugate
open Complex RCLike

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

-- ========================================================================
-- Operator type and self-adjointness
-- ========================================================================

/-- A bounded linear operator on a complex Hilbert space. -/
abbrev Op (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :=
  E →L[ℂ] E

/-- Self-adjointness: A† = A. -/
def IsSelfAdjoint (A : Op E) : Prop :=
  ContinuousLinearMap.adjoint A = A

-- ========================================================================
-- Expectation value and variance
-- ========================================================================

/-- Expectation value ⟨ψ|A|ψ⟩ = ⟪ψ, Aψ⟫_ℂ. -/
def expect (A : Op E) (ψ : E) : ℂ :=
  @inner ℂ E _ ψ (A ψ)

/-- Centered vector: ΔA(ψ) = Aψ − ⟨A⟩_ψ · ψ. -/
def centered (A : Op E) (ψ : E) : E :=
  A ψ - (expect A ψ) • ψ

/-- Variance: Var(A, ψ) = ‖ΔA(ψ)‖². -/
def var (A : Op E) (ψ : E) : ℝ :=
  ‖centered A ψ‖ ^ 2

-- ========================================================================
-- Commutator and anticommutator
-- ========================================================================

/-- Commutator [A, B] = AB − BA. -/
def comm (A B : Op E) : Op E :=
  A.comp B - B.comp A

/-- Anticommutator {A, B} = AB + BA. -/
def acomm (A B : Op E) : Op E :=
  A.comp B + B.comp A

-- ========================================================================
-- Variance is nonneg
-- ========================================================================

theorem var_nonneg (A : Op E) (ψ : E) : 0 ≤ var A ψ := by
  unfold var; positivity

-- ========================================================================
-- Key identity: expectation of self-adjoint is real (conj ⟨A⟩ = ⟨A⟩)
-- ========================================================================

theorem expect_conj_eq_of_selfAdj (A : Op E) (ψ : E) (hA : IsSelfAdjoint A) :
    starRingEnd ℂ (expect A ψ) = expect A ψ := by
  simp only [expect]
  rw [inner_conj_symm]
  have h1 : @inner ℂ E _ (A ψ) ψ = @inner ℂ E _ ψ (ContinuousLinearMap.adjoint A ψ) := by
    rw [ContinuousLinearMap.adjoint_inner_right]
  rw [h1, hA]

-- ========================================================================
-- Self-adjoint operator inner product identities
-- ========================================================================

/-- For self-adjoint A: ⟪Aψ, φ⟫ = ⟪ψ, Aφ⟫. -/
theorem inner_selfAdj_left (A : Op E) (hA : IsSelfAdjoint A) (x y : E) :
    @inner ℂ E _ (A x) y = @inner ℂ E _ x (A y) := by
  rw [← ContinuousLinearMap.adjoint_inner_right A x y, hA]

/-- ⟪ψ, ψ⟫ = 1 when ‖ψ‖ = 1. -/
theorem inner_self_of_norm_one (ψ : E) (hψ : ‖ψ‖ = 1) :
    @inner ℂ E _ ψ ψ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num

-- ========================================================================
-- Key bridge lemma: ⟪ΔA, ΔB⟫ = ⟪Aψ, Bψ⟫ - a·b for self-adjoint A, B
-- ========================================================================

/-- For self-adjoint A, B on unit ψ:
    ⟪ΔA(ψ), ΔB(ψ)⟫ = ⟪Aψ, Bψ⟫ − ⟨A⟩·⟨B⟩.
    The key step: centering shifts the inner product by a real scalar. -/
theorem inner_centered_eq (A B : Op E) (ψ : E)
    (hA : IsSelfAdjoint A) (_hB : IsSelfAdjoint B) (hψ : ‖ψ‖ = 1) :
    @inner ℂ E _ (centered A ψ) (centered B ψ) =
    @inner ℂ E _ (A ψ) (B ψ) - expect A ψ * expect B ψ := by
  unfold centered expect
  set a := @inner ℂ E _ ψ (A ψ)
  set b := @inner ℂ E _ ψ (B ψ)
  have hψ1 : @inner ℂ E _ ψ ψ = (1 : ℂ) := inner_self_of_norm_one ψ hψ
  have hca : starRingEnd ℂ a = a := expect_conj_eq_of_selfAdj A ψ hA
  -- Expand: ⟪Aψ - a·ψ, Bψ - b·ψ⟫
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  -- Replace conj(a) with a (self-adjoint)
  rw [hca]
  -- Replace ⟪ψ, ψ⟫ with 1
  rw [hψ1]
  -- Replace ⟪Aψ, ψ⟫ with conj(⟪ψ, Aψ⟫) = conj(a) = a
  have : @inner ℂ E _ (A ψ) ψ = a := by
    -- inner_conj_symm (A ψ) ψ : conj ⟪ψ, Aψ⟫ = ⟪Aψ, ψ⟫
    -- so .symm gives ⟪Aψ, ψ⟫ = conj ⟪ψ, Aψ⟫ = conj a = a
    rw [show @inner ℂ E _ (A ψ) ψ = starRingEnd ℂ (@inner ℂ E _ ψ (A ψ)) from
      (inner_conj_symm (𝕜 := ℂ) (A ψ) ψ).symm]
    exact hca
  rw [this]
  ring

-- ========================================================================
-- Commutator expectation in terms of centered inner products
-- ========================================================================

/-- Commutator expectation equals ⟪Aψ, Bψ⟫ - ⟪Bψ, Aψ⟫ for self-adjoint A, B. -/
theorem expect_comm_eq_inner_sub (A B : Op E) (ψ : E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    expect (comm A B) ψ = @inner ℂ E _ (A ψ) (B ψ) - @inner ℂ E _ (B ψ) (A ψ) := by
  unfold expect comm
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    inner_sub_right]
  rw [inner_selfAdj_left A hA ψ (B ψ)]
  rw [inner_selfAdj_left B hB ψ (A ψ)]

/-- The key bridge: commutator expectation = z − z̄ where z = ⟪ΔA, ΔB⟫. -/
theorem expect_comm_eq_sub_conj (A B : Op E) (ψ : E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hψ : ‖ψ‖ = 1) :
    expect (comm A B) ψ =
    @inner ℂ E _ (centered A ψ) (centered B ψ) -
    starRingEnd ℂ (@inner ℂ E _ (centered A ψ) (centered B ψ)) := by
  rw [expect_comm_eq_inner_sub A B ψ hA hB]
  -- Rewrite the bare inner product using inner_centered_eq
  rw [inner_centered_eq A B ψ hA hB hψ]
  -- Now the goal has: conj(⟪Aψ,Bψ⟫ − a*b) on the RHS
  -- Expand the conjugate
  simp only [map_sub, map_mul]
  have hca : starRingEnd ℂ (expect A ψ) = expect A ψ := expect_conj_eq_of_selfAdj A ψ hA
  have hcb : starRingEnd ℂ (expect B ψ) = expect B ψ := expect_conj_eq_of_selfAdj B ψ hB
  rw [hca, hcb]
  -- conj(⟪Aψ, Bψ⟫) = ⟪Bψ, Aψ⟫ by inner_conj_symm
  rw [show starRingEnd ℂ (@inner ℂ E _ (A ψ) (B ψ)) = @inner ℂ E _ (B ψ) (A ψ) from by
    rw [inner_conj_symm]]
  ring

-- ========================================================================
-- Anticommutator expectation in terms of centered inner products
-- ========================================================================

/-- Anticommutator expectation for self-adjoint operators. -/
theorem expect_acomm_eq_inner_add (A B : Op E) (ψ : E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    expect (acomm A B) ψ = @inner ℂ E _ (A ψ) (B ψ) + @inner ℂ E _ (B ψ) (A ψ) := by
  unfold expect acomm
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    inner_add_right]
  rw [inner_selfAdj_left A hA ψ (B ψ)]
  rw [inner_selfAdj_left B hB ψ (A ψ)]

/-- The bridge for Schrödinger: ⟨{A,B}⟩ − 2⟨A⟩⟨B⟩ = z + z̄ where z = ⟪ΔA, ΔB⟫. -/
theorem expect_acomm_centered (A B : Op E) (ψ : E)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hψ : ‖ψ‖ = 1) :
    expect (acomm A B) ψ - 2 * expect A ψ * expect B ψ =
    @inner ℂ E _ (centered A ψ) (centered B ψ) +
    starRingEnd ℂ (@inner ℂ E _ (centered A ψ) (centered B ψ)) := by
  rw [expect_acomm_eq_inner_add A B ψ hA hB]
  rw [inner_centered_eq A B ψ hA hB hψ]
  simp only [map_sub, map_mul]
  have hca : starRingEnd ℂ (expect A ψ) = expect A ψ := expect_conj_eq_of_selfAdj A ψ hA
  have hcb : starRingEnd ℂ (expect B ψ) = expect B ψ := expect_conj_eq_of_selfAdj B ψ hB
  rw [hca, hcb]
  rw [show starRingEnd ℂ (@inner ℂ E _ (A ψ) (B ψ)) = @inner ℂ E _ (B ψ) (A ψ) from by
    rw [inner_conj_symm]]
  ring

end

end Papers.P6_Heisenberg
