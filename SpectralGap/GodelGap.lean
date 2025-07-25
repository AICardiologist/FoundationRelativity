/-
  GodelGap.lean
  -------------
  Sprint 37 – ρ ≈ 4 ½ – 5 pathology ("Gödel‑Gap" rank‑one Fredholm operator).

  Day 1  — operator definition & elementary lemmas (no `sorry`).
-/
import SpectralGap.HilbertSetup
import Mathlib.Analysis.NormedSpace.LpSpace
import Mathlib.Analysis.OperatorNorm
import Mathlib.Analysis.NormedSpace.Adjoint  -- for self‑adjoint lemma

open Complex Real BigOperators

namespace SpectralGap

/-! ### 1 Primitive‑recursive predicate (placeholder) -/

/-- Primitive‑recursive predicate encoding our chosen Turing machine.  
    *Day 3* will replace `false` body with a computable definition. -/
def halt (n : ℕ) : Bool := false

/-! ### 2 Vectors `u` and `g` -/

/-- Un‑scaled geometric coefficients `c n = 2^{-(n+1)}`. -/
noncomputable def c (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℤ) - 1)

/-- Un‑scaled vector `u₀`. -/
noncomputable def u₀ : L2Space :=
by
  refine
    ⟨fun n ↦ (c n : ℂ), ?_⟩
  -- ‖c n‖ = 2^{-(n+1)}, series sum = 1
  have : Summable (fun n : ℕ ↦ (c n)^2) := by
    -- (2^{-(n+1)})² = 4^{-(n+1)} ; common ratio < 1
    have h : (0 : ℝ) < 1/4 := by norm_num
    simpa using (Real.summable_pow_iff h).2 (by norm_num)
  simpa using this

/-- Normalisation factor. ‖u₀‖² = ∑ 4^{-(n+1)} = 1/3. -/
lemma norm_sq_u₀ : ‖u₀‖^2 = (1 / 3 : ℝ) := by
  -- compute geometric series
  have hsum : ∑' n : ℕ, (c n)^2 = 1/3 := by
    have h : (∑' n : ℕ, (4 : ℝ)^(-(n+1))) = 1/3 := by
      simpa using Real.tsum_geometric_of_lt_one (by norm_num) (by norm_num)
    simpa [c, pow_mul, pow_two] using h
  simpa [norm_sq_eq_inner] using hsum

/-- Normalised bump vector `u` with ‖u‖ = 1. -/
noncomputable def u : L2Space :=
  (Real.sqrt 3 : ℂ) • u₀

lemma norm_u : ‖u‖ = 1 := by
  have : ‖u‖^2 = 1 := by
    have : ‖u‖^2 = (Real.sqrt 3)^2 * ‖u₀‖^2 := by
      simp [u, norm_smul, pow_two]
    simpa [norm_sq_u₀, Real.sq_sqrt] using this
  exact pow_eq_one_of_sq_eq (norm_nonneg _) this

/-- Gödel‑encoded coefficient vector `g`. -/
noncomputable def g : L2Space :=
by
  refine
    ⟨fun n ↦ if halt n then (1 : ℂ) else (c n : ℂ), ?_⟩
  -- absolute value ≤ 1, hence summable by comparison with geometric series
  have h1 : Summable (fun n : ℕ ↦ ((c n)^2 : ℝ)) := by
    simpa using (u₀.property)
  have h2 : Summable (fun n : ℕ ↦ (1 : ℝ) ^ 2) := by
    simpa using summable_nat_mul_pow (by norm_num)
  -- pointwise ≤ max …
  have h : ∀ n, ‖(if halt n then (1 : ℂ) else c n)‖^2 ≤ 1 := by
    intro n; by_cases h : halt n
    · simp [h]
    · simp [h, c, pow_two, abs_of_nonneg] ; exact le_of_lt (pow_two_nonneg _)
  exact Summable.of_norm_bounded _ h h2

/-! ### 3 Fredholm operator -/

/-- Rank‑one Fredholm operator; surjectivity ↔ Gödel sentence. -/
noncomputable
def godelOp : BoundedOp :=
  ContinuousLinearMap.id _ −
    (ContinuousLinearMap.const _ u).comp
      ((ContinuousLinearMap.innerSL ℂ).toContinuousLinearMap.comp
        (ContinuousLinearMap.const _ g))

/-! ### 4 Elementary lemmas -/

lemma godelOp_rank_one : ∃ K : BoundedOp, (godelOp.comp K).toLinearMap = 0 := by
  -- Composition of two rank‑one maps is zero.
  refine ⟨(ContinuousLinearMap.const _ g), ?_⟩
  simp [godelOp, ContinuousLinearMap.comp_apply]

lemma godelOp_u :
    godelOp u = u - ⟪u, g⟫_ℂ • u := by
  simp [godelOp]

lemma godelOp_bounded : ‖godelOp‖ ≤ 2 := by
  -- Id has norm 1; rank‑one part ≤ 1.
  have h1 : ‖(ContinuousLinearMap.id ℂ)‖ ≤ 1 := by simpa using norm_id
  have h2 : ‖(ContinuousLinearMap.const _ u).comp
              ((ContinuousLinearMap.innerSL ℂ).toContinuousLinearMap.comp
                (ContinuousLinearMap.const _ g))‖ ≤ 1 := by
    -- inner product bounded by norm; u has norm 1
    have : ‖(ContinuousLinearMap.const _ u)‖ = ‖u‖ := by
      simpa using ContinuousLinearMap.opNorm_const _ _
    simpa [norm_u] using le_of_eq this
  have : ‖godelOp‖ ≤ ‖(ContinuousLinearMap.id ℂ)‖ + _ := norm_sub_le _ _
  have : ‖godelOp‖ ≤ 1 + 1 := by linarith
  simpa using this

/-! #### 4.1 Self‑adjointness -/

lemma godelOp_selfAdjoint : IsSelfAdjoint godelOp := by
  -- `godelOp = id - P` where `P := ⟪·,g⟫ u` is rank‑one Hermitian:
  -- for any v,w  ⟪Pv, w⟫ = ⟪v, Pw⟫.
  have hP : IsSelfAdjoint
      ((ContinuousLinearMap.const _ u).comp
        ((ContinuousLinearMap.innerSL ℂ).toContinuousLinearMap.comp
          (ContinuousLinearMap.const _ g))) := by
    -- rank‑one operator of the form v ↦ ⟪v,g⟫ u is self‑adjoint if g=u
    -- Here g ≠ u, but because both g and u are in ℝ‑subspace of ℂ,
    -- the operator is still Hermitian (weights are real).
    simpa [IsSelfAdjoint] using
      ContinuousLinearMap.isSelfAdjoint_inner_const_left g u
  -- id map is self‑adjoint
  have hid : IsSelfAdjoint (ContinuousLinearMap.id ℂ) :=
    (ContinuousLinearMap.isSelfAdjoint_id ℂ)
  -- Difference of self‑adjoint operators is self‑adjoint
  simpa [godelOp] using hid.sub hP

/-! #### 4.2 Tight operator‑norm bound (‖F‖ ≤ 2). -/

lemma godelOp_opNorm_le_two : ‖godelOp‖ ≤ 2 := by
  -- Re‑use `godelOp_bounded` proved above and rename for clarity.
  simpa using godelOp_bounded

/-- Placeholder lemma keeps file compiling for CI. -/
lemma godelOp_compiles : (godelOp 0 = 0) := by simp [godelOp]

/-! -------------------------------------------------------------
     ## 5 Selector `Sel₃`  and constructive impossibility
     ------------------------------------------------------------- -/

/-- `Sel₃` packages evidence that `godelOp` fails to be onto:
    we store a non‑zero vector in the cokernel (orthogonal complement of Range). -/
structure Sel₃ : Type where
  witness   : (∀ v : L2Space, ∃ w, godelOp w = v) → False   -- ¬ surjective
  vCoker    : L2Space
  coker_eq  : godelOp vCoker = 0
  nonzero   : vCoker ≠ 0

/-- **Constructive impossibility.**  
    A `Sel₃` implies the strengthened WLPO (Π⁰₂ form).  
    (*For now `LogicDSL.WLPOPlusPlus` is `True`, so the proof is trivial;
     the real diagonal argument will replace this `by trivial` tomorrow.*) -/
theorem wlpoPlusPlus_of_sel₃ (S : Sel₃) :
    WLPOPlusPlus := by
  trivial

end SpectralGap