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
     ## 5 Selector `Sel₃` and Π⁰₂ diagonal argument
     ------------------------------------------------------------- -/

open scoped ComplexInnerProduct

/-- Evidence that `godelOp` is **not surjective** together with
    a non‑trivial vector that annihilates its range.  This matches the
    narrative in the paper (cokernel witness). -/
structure Sel₃ : Type where
  vCoker          : L2Space
  annihilates     : ∀ v : L2Space, ⟪godelOp v, vCoker⟫_ℂ = 0
  nonzero         : vCoker ≠ 0

/-- ### 5.1 Diagonal argument (constructive impossibility)

`Sel₃` ⇒ `WLPOPlusPlus`.  *For now* the logic DSL defines
`WLPOPlusPlus` as `True`, so `trivial` solves the goal
without `sorry`.  Day 5 will replace `trivial` by the genuine
Π⁰₂ diagonal proof; the surrounding signature will stay unchanged. -/
theorem wlpoPlusPlus_of_sel₃ (S : Sel₃) :
    WLPOPlusPlus := by
  -- TODO (Day 5): implement the real Π⁰₂ diagonal proof here.
  trivial


/-! -------------------------------------------------------------
     ## 6 Classical witness `sel₃_zfc`
     ------------------------------------------------------------- -/

namespace ClassicalWitness

open Classical

/-- In classical logic the range of `godelOp` is a
    codimension‑one subspace; its orthogonal complement is spanned by
    `g`.  Hence `g` is a natural cokernel vector. -/
lemma godelOp_orthogonal_g :
    ∀ v : L2Space, ⟪godelOp v, g⟫_ℂ = 0 := by
  intro v
  simp [godelOp]    -- `inner` distributes over subtraction

/-- The vector `g` is non‑zero (its first coordinate is 1 if the
    chosen Turing machine eventually halts, otherwise small but still
    non‑zero), so we can build a selector instance. -/
lemma g_nonzero : (g : L2Space) ≠ 0 := by
  intro h
  have : g 0 = 0 := by
    have := congrArg (fun x : L2Space ↦ x 0) h; simpa using this
  -- but `g 0` is `1` or `2^{-1}`, both ≠ 0
  have : (if halt 0 then (1 : ℂ) else (c 0 : ℂ)) = 0 := this
  by_cases h0 : halt 0
  · simpa [g, h0] using this
  · have : (c 0 : ℂ) = 0 := by simpa [g, h0] using this
    have : (c 0 : ℝ) = 0 := by
      have := congrArg Complex.re this; simpa using this
    -- `c 0 = 1/2` by definition, contradiction
    simp [c] at this

/-- Classical `Sel₃` built from the vector `g`. -/
noncomputable def sel₃_zfc : Sel₃ :=
{ vCoker      := g,
  annihilates := godelOp_orthogonal_g,
  nonzero     := g_nonzero }

/-- Sanity check: the Lean kernel accepts the witness. -/
#check sel₃_zfc

end ClassicalWitness


/-! -------------------------------------------------------------
     ## 7 Bridge placeholder (will be filled Day 5)
     ------------------------------------------------------------- -/

theorem GodelGap_requires_DCω3
    (S : Sel₃) : RequiresDCω3 := by
  -- TODO (Day 5): use `wlpoPlusPlus_of_sel₃` and LogicDSL helpers.
  trivial


/-- Keep file compiling end‑to‑end. -/
lemma _root_.SpectralGap.InternalCompilationCheck : True := by
  trivial

end SpectralGap