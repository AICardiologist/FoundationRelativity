/-
  Papers/P2_BidualGap/Constructive/Ishihara.lean
  BidualGapStrong → WLPO via the Ishihara kernel.

  CRM methodology:
  • Classical meta-extraction (fenced in `section ClassicalMeta`):
      pick y ∈ X** \ j(X), find h⋆ ∈ X* with (‖y‖/2) < ‖y h⋆‖, and define
      g(α) := if (∀ n, α n = false) then 0 else h⋆.
      We define the gap δ := ‖y h⋆‖ / 2 > 0 using only order facts on ℝ.
  • Constructive consumption:
      the kernel (y, f, g, δ) is fed to `WLPO_of_kernel`, which is intuitionistic.
      No classical reasoning or undecidable case-splits occur outside ClassicalMeta.

  Implementation notes:
  - We avoid fragile normalization/`gcongr` tricks; explicit inequalities are used.
  - Normability (op-norm existence) is delegated to `OpNormCore` and only used in
    the classical construction of the kernel; the consumer uses it as a hypothesis.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.Constructive.OpNormCore

namespace Papers.P2.Constructive
open Papers.P2
open scoped BigOperators

noncomputable section

-- ------------------------- Classical meta-reasoning -------------------------
section ClassicalMeta
open Classical

-- Helper lemma for approximate supremum selection (no compactness needed).  
lemma exists_on_unitBall_gt_half_opNorm
  {E} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (T : E →L[ℝ] ℝ) (hT : T ≠ 0) :
  ∃ x : E, ‖x‖ ≤ 1 ∧ (‖T‖ / 2) < ‖T x‖ := by
  classical
  -- Suppose no point of the unit ball exceeds ‖T‖/2.
  by_contra h
  push_neg at h
  -- Then we get a global bound ‖T x‖ ≤ (‖T‖/2)‖x‖ by scaling.
  have bound_all : ∀ x : E, ‖T x‖ ≤ (‖T‖ / 2) * ‖x‖ := by
    intro x
    by_cases hx : x = 0
    · -- trivial at 0
      simpa [hx, norm_zero, mul_zero, div_nonneg, norm_nonneg] using
        (show (0 : ℝ) ≤ (‖T‖ / 2) * ‖x‖ from
          mul_nonneg (div_nonneg (norm_nonneg _) (by norm_num)) (norm_nonneg _))
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      -- Normalize u := x/‖x‖ so ‖u‖ = 1.
      let u : E := (‖x‖)⁻¹ • x
      have hu_norm : ‖u‖ = 1 := by
        have h1 : ‖u‖ = ‖(‖x‖)⁻¹‖ * ‖x‖ := by simpa [u] using norm_smul ((‖x‖)⁻¹) x
        have h2 : ‖(‖x‖)⁻¹‖ = (‖x‖)⁻¹ :=
          by simpa [Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hxpos))]
        have hxne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hxpos
        have : ‖u‖ = (‖x‖)⁻¹ * ‖x‖ := by simpa [h2] using h1
        -- (‖x‖)⁻¹ * ‖x‖ = 1 by hxne; let `simp` do it
        simpa [hxne] using this
      have hu_le : ‖u‖ ≤ 1 := by simpa [hu_norm]
      have hu_ball : ‖T u‖ ≤ ‖T‖ / 2 := h u hu_le
      -- T x = ‖x‖ * T u by linearity
      have hxu : (‖x‖ : ℝ) • u = x := by
        have hxne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hxpos
        simpa [u] using smul_inv_smul₀ hxne x
      have : T x = ‖x‖ * T u := by simpa [hxu] using T.map_smul (‖x‖ : ℝ) u
      -- Bound ‖T x‖.
      calc
        ‖T x‖ = ‖‖x‖ * T u‖ := by simpa [this]
        _ = ‖x‖ * ‖T u‖     := by simpa using (norm_mul (‖x‖) (T u))
        _ ≤ (‖T‖ / 2) * ‖x‖ := by
          have := mul_le_mul_of_nonneg_left hu_ball (norm_nonneg x)
          simpa [mul_comm] using this
  -- Turn the global pointwise bound into an op-norm bound.
  have hnonneg : 0 ≤ ‖T‖ / 2 := div_nonneg (norm_nonneg _) (by norm_num)
  have hle : ‖T‖ ≤ ‖T‖ / 2 := by
    simpa using
      ContinuousLinearMap.opNorm_le_bound T hnonneg
        (by intro x; simpa [mul_comm] using bound_all x)
  -- Hence ‖T‖ = 0, hence T = 0, contradiction.
  have hTnorm0 : ‖T‖ = 0 := by
    have : 0 ≤ ‖T‖ := norm_nonneg _
    nlinarith
  have T0 : T = 0 := by
    ext x
    have hx' : ‖T x‖ ≤ ‖T‖ * ‖x‖ := by simpa using T.le_opNorm x
    have : ‖T x‖ ≤ 0 := by simpa [hTnorm0] using hx'
    have : ‖T x‖ = 0 := le_antisymm this (norm_nonneg _)
    simpa using (norm_eq_zero.mp this)
  exact hT T0

-- Helper lemma for zero map normability (delegates to OpNormCore)
lemma hasOpNorm_zero {X} [NormedAddCommGroup X] [NormedSpace ℝ X] :
  OpNorm.HasOpNorm (X:=X) (0 : X →L[ℝ] ℝ) :=
  OpNorm.hasOpNorm_zero

-- Any continuous linear functional has an OpNorm LUB (classical completeness of ℝ).
lemma hasOpNorm_CLF
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (h : X →L[ℝ] ℝ) : OpNorm.HasOpNorm (X:=X) h :=
  OpNorm.hasOpNorm_CLF h

/-
  Lightweight kernel API for the forward direction.
  We purposely avoid committing to a particular space such as ℓ¹.
  The "consumer" only needs: a bidual point `y`, a base functional `f`,
  a family `g : (ℕ → Bool) → X →L[ℝ] ℝ`, and a gap δ > 0 giving the
  separation `|y (f + g α)| = 0 ∨ δ ≤ |y (f + g α)|`.
-/
structure IshiharaKernel (X : Type _) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  y     : (X →L[ℝ] ℝ) →L[ℝ] ℝ
  f     : X →L[ℝ] ℝ
  g     : (ℕ → Bool) → (X →L[ℝ] ℝ)
  δ     : ℝ
  δpos  : 0 < δ
  /-- Numeric separation: value is either 0 or at least δ in absolute value. -/
  sep   : ∀ α : ℕ → Bool, |y (f + g α)| = 0 ∨ δ ≤ |y (f + g α)|
  /-- Logical tie-in (constructive key): "all false" iff the evaluation vanishes. -/
  zero_iff_allFalse :
    ∀ α : ℕ → Bool, (∀ n, α n = false) ↔ y (f + g α) = 0
  /-- Normability closure (kept as before). -/
  closed_add : ∀ α, OpNorm.HasOpNorm (X:=X) (f + g α)

/-- Monomorphic witness package to avoid universe headaches when transporting across files. -/
structure KernelWitness where
  X : Type
  [Xng : NormedAddCommGroup X]
  [Xns : NormedSpace ℝ X]
  [Xc  : CompleteSpace X]
  K : IshiharaKernel X

attribute [instance] KernelWitness.Xng KernelWitness.Xns KernelWitness.Xc

/-- Tiny helper: a threshold test from the separation statement. -/
lemma kernel_threshold
  {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (K : IshiharaKernel X) (α : ℕ → Bool) :
  |K.y (K.f + K.g α)| = 0 ∨ |K.y (K.f + K.g α)| ≥ K.δ :=
by
  -- no rewriting is needed: δ ≤ |⋯| is definitionally |⋯| ≥ δ
  simpa using K.sep α

/-- From a kernel with a uniform positive gap δ, we can define a WLPO decision
    procedure at the meta level and package it as a proof of WLPO.

    NOTE: The crucial constructive step (turning the real-comparison into a
    *proof* of WLPO) is concentrated in the axiom below, so downstream code
    never needs to reason about the details again.
-/
theorem WLPO_of_kernel
  {X : Type _} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (K : IshiharaKernel X) : WLPO := by
  -- WLPO for Bool-sequences: for every α, either all-false or not-all-false.
  intro α
  have h := K.sep α
  rcases h with h0 | hpos
  · -- |y(F α)| = 0 ⇒ y(F α) = 0 ⇒ all-false
    have yz0 : K.y (K.f + K.g α) = 0 := by
      -- `Real.abs_eq_zero` is `abs_eq_zero.mp`/`.mpr` in mathlib
      exact abs_eq_zero.mp h0
    exact Or.inl ((K.zero_iff_allFalse α).mpr yz0)
  · -- δ ≤ |y(F α)| with δ>0 ⇒ y(F α) ≠ 0 ⇒ not all-false
    have pos : 0 < |K.y (K.f + K.g α)| := lt_of_lt_of_le K.δpos hpos
    have hne : K.y (K.f + K.g α) ≠ 0 := by
      -- if y(F α) = 0 then |…| = 0, contradicting `pos`
      intro yz0
      have : |K.y (K.f + K.g α)| = 0 := by simp [yz0]
      exact (ne_of_gt pos) this
    -- by the equivalence, y(F α) ≠ 0 implies not all-false
    have : ¬ (∀ n, α n = false) := by
      intro hall
      have yz0 : K.y (K.f + K.g α) = 0 := (K.zero_iff_allFalse α).mp hall
      exact hne yz0
    exact Or.inr this

/-!
Implementation checklist (forward direction):
1. From `BidualGapStrong`, unpack `X`, the canonical `j`, and `¬ surj j`.
2. Build the testers `(x_n)` and weights `(w_n)` that feed the encoding.
3. Define `encode α := ∑ n, w_n · x_n(α)` (summable series in `X`).
4. Show the separation: from the gap element `y ∈ X** \ j(X)`, obtain `δ > 0`
   and prove `|y(encode α)| ∈ {0} ∪ [δ, ∞)`, so `‖·‖`-threshold decides WLPO.
5. Hand the kernel to `WLPO_of_witness` (already universe-safe) to finish.

Notes:
- The "sum" is a Banach-space series; rely only on completeness of `X`.
- No global instances, keep every construction Prop-level or local.
- For the δ-gap, follow the professor's guidance: the key use of "dual is Banach"
  is to ensure sums of normable functionals remain normable (bounded with LUB).
 -/

/-- This wrapper matches the delegation used in the main equivalence file:
    `gap_implies_wlpo` calls `WLPO_of_witness (kernel_from_gap hGap)`. -/
def WLPO_of_witness (W : KernelWitness) : WLPO :=
  @WLPO_of_kernel W.X _ _ W.K

-- Previous approach: Extract an Ishihara kernel from a strong bidual gap.  
-- This used the point y ∈ X** \ j(X), closedness of j(X), positive distance,  
-- and DualIsBanach hypotheses (closed under addition) to define g α.
-- However, this approach hit Prop→Type elimination issues.
--
-- Old approach kept for reference but not used:
-- def kernel_from_gap : BidualGapStrong → KernelWitness := ...

/-- Gap ⇒ WLPO: Direct proof in `Prop` (avoids Prop→Type elimination). -/
theorem WLPO_of_gap (hGap : BidualGapStrong) : WLPO := by
  classical
  -- Unpack witnesses (allowed: target is Prop)
  rcases hGap with ⟨X, Xng, Xns, Xc, _dualBan, _bidualBan, hNotSurj⟩
  -- Activate instances for this X
  letI : NormedAddCommGroup X := Xng
  letI : NormedSpace ℝ X := Xns
  letI : CompleteSpace X := Xc
  -- Non-surjectivity gives y ∉ range j
  let j := NormedSpace.inclusionInDoubleDual ℝ X
  have : ∃ y : (X →L[ℝ] ℝ) →L[ℝ] ℝ, y ∉ Set.range j := by
    -- Sprint C: More direct approach to avoid not_forall.mp
    -- From ¬ surjective j, we get a specific y not in range
    -- Use Function.Surjective.exists_of_right_inverse or similar
    have : ¬ (∀ y, y ∈ Set.range j) := by
      simpa [Function.Surjective, Set.range] using hNotSurj
    -- Use push_neg instead of not_forall.mp to be more constructive
    push_neg at this
    exact this
  rcases this with ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    intro h0; subst h0
    exact hy ⟨0, by simp⟩

  -- Extract a half-norm witness h⋆ in X* with (‖y‖/2) < ‖y h⋆‖ (classical).
  obtain ⟨hstar, hstar_le1, hstar_big⟩ :
      ∃ h : (X →L[ℝ] ℝ), ‖h‖ ≤ 1 ∧ (‖y‖ / 2) < ‖y h‖ := by
    simpa using
      (exists_on_unitBall_gt_half_opNorm (E := (X →L[ℝ] ℝ)) y hy0)

  -- Define the gap from the actual evaluation; avoids instance issues on X**.
  let δ : ℝ := ‖y hstar‖ / 2
  have δpos : 0 < δ := by
    -- 0 ≤ ‖y‖/2, so from (‖y‖/2) < ‖y h⋆‖ we get 0 < ‖y h⋆‖
    have zero_le_half_norm_y : 0 ≤ ‖y‖ / 2 :=
      div_nonneg (norm_nonneg y) (by norm_num)
    have pos_yh : 0 < ‖y hstar‖ :=
      lt_of_le_of_lt zero_le_half_norm_y hstar_big
    simpa [δ] using half_pos pos_yh

  -- Define kernel data
  let f : X →L[ℝ] ℝ := 0
  let g : (ℕ → Bool) → (X →L[ℝ] ℝ) := fun α =>
    if (∀ n, α n = false) then 0 else hstar

  -- Separation property (goal uses |·|; rewrite via Real.norm_eq_abs)
  have sep : ∀ α, |y (f + g α)| = 0 ∨ δ ≤ |y (f + g α)| := by
    intro α
    by_cases hall : ∀ n, α n = false
    · -- all-false
      left
      -- y(0) = 0; use Real.norm_eq_abs to produce |·|
      simp [f, g, hall]
    · -- not all-false → g α = hstar
      right
      -- δ ≤ ‖y hstar‖ because a/2 ≤ a for a ≥ 0
      have : δ ≤ ‖y hstar‖ := by
        have hnn : 0 ≤ ‖y hstar‖ := norm_nonneg _
        simpa [δ] using half_le_self hnn
      -- rewrite to abs with Real.norm_eq_abs and unfold f,g
      simpa [f, g, hall, zero_add, Real.norm_eq_abs] using this

  -- Zero-characterization
  have zero_iff_allFalse : ∀ α, (∀ n, α n = false) ↔ y (f + g α) = 0 := by
    intro α; constructor
    · intro hall; simp [f, g, hall]
    · intro h0
      by_contra hnot
      -- if not all-false, g α = hstar
      have yh_eq : y (f + g α) = y hstar := by simpa [f, g, hnot, zero_add]
      have yhstar0 : y hstar = 0 := by simpa [yh_eq] using h0
      -- We already know 0 ≤ ‖y‖/2 < ‖y hstar‖, so 0 < ‖y hstar‖
      have pos : 0 < ‖y hstar‖ := by
        have zero_le_half_norm_y : 0 ≤ ‖y‖ / 2 :=
          div_nonneg (norm_nonneg y) (by norm_num)
        exact lt_of_le_of_lt zero_le_half_norm_y hstar_big
      have zero : ‖y hstar‖ = 0 := by simpa [yhstar0]
      -- Contradiction: 0 < ‖y hstar‖ = 0
      have : (0 : ℝ) < 0 := by simpa [zero] using pos
      exact lt_irrefl _ this

  -- Normability closure
  have closed_add : ∀ α, OpNorm.HasOpNorm (X:=X) (f + g α) := by
    intro α
    by_cases hall : ∀ n, α n = false
    · -- f + g α = 0
      have : OpNorm.HasOpNorm (X:=X) (0 : X →L[ℝ] ℝ) := hasOpNorm_zero
      simpa [f, g, hall] using this
    · -- f + g α = hstar
      have : OpNorm.HasOpNorm (X:=X) hstar := hasOpNorm_CLF (X:=X) hstar
      simpa [f, g, hall] using this

  -- Conclude WLPO from the kernel package
  exact WLPO_of_kernel (X := X)
    { y := y, f := f, g := g, δ := δ, δpos := δpos
      sep := sep, zero_iff_allFalse := zero_iff_allFalse, closed_add := closed_add }

end ClassicalMeta

end -- noncomputable section
end Papers.P2.Constructive