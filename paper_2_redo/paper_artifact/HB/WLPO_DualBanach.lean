/- 
  Papers/P2_BidualGap/HB/WLPO_DualBanach.lean
  WLPO-facing DualIsBanach constructions for ℓ¹ and (c₀)*.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Tactic
import Papers.P2_BidualGap.Basic
import Papers.P2_BidualGap.HB.L1DualLinf
import Papers.P2_BidualGap.HB.DualIsometriesComplete

noncomputable section

namespace Papers.P2.HB
open scoped BigOperators

-- Shorthand
local notation "DualIsBanach" => Papers.P2.DualIsBanach
local notation "HasOperatorNorm" => Papers.P2.HasOperatorNorm
local notation "WLPO" => Papers.P2.WLPO
local notation "LPO" => Papers.P2.LPO

-- Our model for c₀ on discrete ℕ
local notation "c₀" => ZeroAtInftyContinuousMap ℕ ℝ

/-- Rational approximation for reals (classical density). -/
lemma exists_rat_abs_sub_le (r ε : ℝ) (hε : 0 < ε) : ∃ q : ℚ, |r - q| ≤ ε := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r - ε < r + ε by linarith)
  refine ⟨q, ?_⟩
  have hlt : |r - (q : ℝ)| < ε := by
    have h1 : r - (q : ℝ) < ε := by linarith [hq1]
    have h2 : -ε < r - (q : ℝ) := by linarith [hq2]
    exact abs_lt.mpr ⟨h2, h1⟩
  exact le_of_lt hlt

/-- ℓ¹ basis vector is nonzero. -/
lemma l1basis_ne_zero (n : ℕ) : (l1basis n : l1) ≠ 0 := by
  intro hzero
  have h0' := congrArg (fun f : l1 => (f : ℕ → ℝ) n) hzero
  have h0 : (1 : ℝ) = 0 := by
    simpa [l1basis_apply_self] using h0'
  exact one_ne_zero h0

/-- Operator norm exists (classically) with minimality, assuming nontrivial domain. -/
lemma hasOperatorNorm_of_nontrivial
  {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [Nontrivial X]
  (f : X →L[ℝ] ℝ) : HasOperatorNorm f := by
  refine ⟨‖f‖, ?_⟩
  refine ⟨norm_nonneg _, ?_, ?_⟩
  · intro x; exact f.le_opNorm x
  · intro N' hN'
    -- N' is nonnegative: pick any x ≠ 0 and divide by ‖x‖.
    have hN'nonneg : 0 ≤ N' := by
      classical
      obtain ⟨x, hx⟩ := exists_ne (0 : X)
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have h0 : 0 ≤ ‖f x‖ := norm_nonneg _
      have hprod : 0 ≤ N' * ‖x‖ := le_trans h0 (hN' x)
      by_contra hneg
      have hneg' : N' < 0 := lt_of_not_ge hneg
      have : N' * ‖x‖ < 0 := mul_neg_of_neg_of_pos hneg' hxpos
      exact (not_lt_of_ge hprod) this
    exact ContinuousLinearMap.opNorm_le_bound (f := f) hN'nonneg hN'

/-- WLPO-based existence of a coefficient near the ℓ^∞ norm.
    Note: witness extraction uses classical logic on Bool. -/
lemma exists_coeff_near_sup_WLPO (h : WLPO) (b : linf) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ‖b n‖ ≥ ‖b‖ - ε := by
  classical
  -- Boolean test for a coefficient beating the threshold
  let α : ℕ → Bool := fun n => decide (‖b n‖ > ‖b‖ - ε)
  have hwlpo := h α
  cases hwlpo with
  | inl hall =>
      -- all false: every coefficient ≤ ‖b‖ - ε, contradicts LUB property
      have hle : ∀ n, ‖b n‖ ≤ ‖b‖ - ε := by
        intro n
        have hfalse : α n = false := hall n
        have hnot : ¬ ‖b n‖ > ‖b‖ - ε := by
          have : decide (‖b n‖ > ‖b‖ - ε) = false := by simpa [α] using hfalse
          exact (decide_eq_false_iff_not).1 this
        exact le_of_not_gt hnot
      -- `‖b‖` is the LUB of the range of norms
      have hupper : (‖b‖ - ε) ∈ upperBounds (Set.range fun n : ℕ => ‖b n‖) := by
        intro y hy
        rcases hy with ⟨n, rfl⟩
        exact hle n
      have hsup_le : ‖b‖ ≤ ‖b‖ - ε :=
        by
          -- unpack `IsLUB` = least element of `upperBounds`
          have hlow : ‖b‖ ∈ lowerBounds (upperBounds (Set.range fun n : ℕ => ‖b n‖)) :=
            (lp.isLUB_norm b).2
          -- unfold `lowerBounds`
          dsimp [lowerBounds] at hlow
          exact hlow hupper
      have hlt : ‖b‖ - ε < ‖b‖ := by linarith
      exact (False.elim (not_lt_of_ge hsup_le hlt))
  | inr hnot =>
      -- not all false: extract an index classically
      have hExists : ∃ n, α n = true := by
        classical
        by_contra hno
        have hall : ∀ n, α n = false := by
          intro n
          by_cases h' : α n = true
          · exact (hno ⟨n, h'⟩).elim
          · -- Bool: if not true, it must be false
            cases hval : α n with
            | false => simpa [hval]
            | true =>
                have : α n = true := by simpa [hval]
                exact (h' this).elim
        exact hnot hall
      rcases hExists with ⟨n, hn⟩
      have hgt : ‖b n‖ > ‖b‖ - ε := by
        have : decide (‖b n‖ > ‖b‖ - ε) = true := by simpa [α] using hn
        exact (decide_eq_true_iff).1 this
      exact ⟨n, le_of_lt hgt⟩

/-- LPO-based existence of a coefficient near the ℓ^∞ norm (constructive witness). -/
lemma exists_coeff_near_sup_LPO (h : LPO) (b : linf) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ‖b n‖ ≥ ‖b‖ - ε := by
  -- Boolean test for a coefficient beating the threshold
  let α : ℕ → Bool := fun n => decide (‖b n‖ > ‖b‖ - ε)
  have hLPO := h α
  cases hLPO with
  | inl hall =>
      -- all false: every coefficient ≤ ‖b‖ - ε, contradicts LUB property
      have hle : ∀ n, ‖b n‖ ≤ ‖b‖ - ε := by
        intro n
        have hfalse : α n = false := hall n
        have hnot : ¬ ‖b n‖ > ‖b‖ - ε := by
          have : decide (‖b n‖ > ‖b‖ - ε) = false := by simpa [α] using hfalse
          exact (decide_eq_false_iff_not).1 this
        exact le_of_not_gt hnot
      -- `‖b‖` is the LUB of the range of norms
      have hupper : (‖b‖ - ε) ∈ upperBounds (Set.range fun n : ℕ => ‖b n‖) := by
        intro y hy
        rcases hy with ⟨n, rfl⟩
        exact hle n
      have hsup_le : ‖b‖ ≤ ‖b‖ - ε :=
        by
          have hlow : ‖b‖ ∈ lowerBounds (upperBounds (Set.range fun n : ℕ => ‖b n‖)) :=
            (lp.isLUB_norm b).2
          dsimp [lowerBounds] at hlow
          exact hlow hupper
      have hlt : ‖b‖ - ε < ‖b‖ := by linarith
      exact (False.elim (not_lt_of_ge hsup_le hlt))
  | inr hex =>
      rcases hex with ⟨n, hn⟩
      have hgt : ‖b n‖ > ‖b‖ - ε := by
        have : decide (‖b n‖ > ‖b‖ - ε) = true := by simpa [α] using hn
        exact (decide_eq_true_iff).1 this
      exact ⟨n, le_of_lt hgt⟩

/-- WLPO ⇒ DualIsBanach for ℓ¹ (via ℓ∞ coefficients). -/
lemma dual_is_banach_l1_from_WLPO (h : WLPO) : DualIsBanach l1 := by
  haveI : Nontrivial l1 := by
    exact ⟨⟨l1basis 0, 0, l1basis_ne_zero 0⟩⟩
  refine
    { norm_located := ?_
      norm_attained := ?_
      complete := by infer_instance
      closed_zero := ?_
      closed_neg := ?_
      closed_smul := ?_
      closed_add := ?_ }
  · intro φ ε hε
    rcases exists_rat_abs_sub_le ‖coeffLinf φ‖ ε hε with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have hnorm : ‖φ‖ = ‖coeffLinf φ‖ := opNorm_eq_coeffLinf_norm φ
    simpa [hnorm] using hq
  · intro φ ε hε
    obtain ⟨n, hn⟩ := exists_coeff_near_sup_WLPO h (coeffLinf φ) ε hε
    let x : l1 := l1basis n
    have hx : ‖x‖ ≤ 1 := by
      have hx' : ‖x‖ = 1 := by
        simpa [x] using (l1basis_norm n)
      exact le_of_eq hx'
    have hfx : ‖φ x‖ ≥ ‖φ‖ - ε := by
      have hnorm : ‖φ‖ = ‖coeffLinf φ‖ := opNorm_eq_coeffLinf_norm φ
      have hcoeff : ‖φ x‖ = ‖coeffLinf φ n‖ := by
        simp [x, l1basis, coeffLinf_apply, coeffL1]
      simpa [hnorm, hcoeff] using hn
    exact ⟨x, hx, hfx⟩
  · exact hasOperatorNorm_of_nontrivial (0 : l1 →L[ℝ] ℝ)
  · intro f _; exact hasOperatorNorm_of_nontrivial (-f)
  · intro a f _; exact hasOperatorNorm_of_nontrivial (a • f)
  · intro f g _ _; exact hasOperatorNorm_of_nontrivial (f + g)

/-- LPO ⇒ DualIsBanach for ℓ¹ (via ℓ∞ coefficients, constructive witness). -/
lemma dual_is_banach_l1_from_LPO (h : LPO) : DualIsBanach l1 := by
  haveI : Nontrivial l1 := by
    exact ⟨⟨l1basis 0, 0, l1basis_ne_zero 0⟩⟩
  refine
    { norm_located := ?_
      norm_attained := ?_
      complete := by infer_instance
      closed_zero := ?_
      closed_neg := ?_
      closed_smul := ?_
      closed_add := ?_ }
  · intro φ ε hε
    rcases exists_rat_abs_sub_le ‖coeffLinf φ‖ ε hε with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have hnorm : ‖φ‖ = ‖coeffLinf φ‖ := opNorm_eq_coeffLinf_norm φ
    simpa [hnorm] using hq
  · intro φ ε hε
    obtain ⟨n, hn⟩ := exists_coeff_near_sup_LPO h (coeffLinf φ) ε hε
    let x : l1 := l1basis n
    have hx : ‖x‖ ≤ 1 := by
      have hx' : ‖x‖ = 1 := by
        simpa [x] using (l1basis_norm n)
      exact le_of_eq hx'
    have hfx : ‖φ x‖ ≥ ‖φ‖ - ε := by
      have hnorm : ‖φ‖ = ‖coeffLinf φ‖ := opNorm_eq_coeffLinf_norm φ
      have hcoeff : ‖φ x‖ = ‖coeffLinf φ n‖ := by
        simp [x, l1basis, coeffLinf_apply, coeffL1]
      simpa [hnorm, hcoeff] using hn
    exact ⟨x, hx, hfx⟩
  · exact hasOperatorNorm_of_nontrivial (0 : l1 →L[ℝ] ℝ)
  · intro f _; exact hasOperatorNorm_of_nontrivial (-f)
  · intro a f _; exact hasOperatorNorm_of_nontrivial (a • f)
  · intro f g _ _; exact hasOperatorNorm_of_nontrivial (f + g)

/-- Precomposition with a linear isometry equivalence preserves op-norm. -/
lemma opNorm_comp_linearIsometryEquiv
  {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  (F : X →L[ℝ] ℝ) (e : Y ≃ₗᵢ[ℝ] X) :
  ‖F.comp (e : Y →L[ℝ] X)‖ = ‖F‖ := by
  -- ≤ direction
  have hle : ‖F.comp (e : Y →L[ℝ] X)‖ ≤ ‖F‖ := by
    have hcomp := ContinuousLinearMap.opNorm_comp_le F (e : Y →L[ℝ] X)
    have hnorme : ‖(e : Y →L[ℝ] X)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound (f := (e : Y →L[ℝ] X)) (M := 1) (by norm_num) ?_
      intro y
      simpa [one_mul] using (le_of_eq (LinearIsometry.norm_map e y))
    have hbound : ‖F‖ * ‖(e : Y →L[ℝ] X)‖ ≤ ‖F‖ * 1 :=
      mul_le_mul_of_nonneg_left hnorme (norm_nonneg _)
    exact (le_trans hcomp (by simpa using hbound))
  -- ≥ direction by composing with e.symm
  have hge : ‖F‖ ≤ ‖F.comp (e : Y →L[ℝ] X)‖ := by
    -- F = (F ∘ e) ∘ e.symm
    have hcomp := ContinuousLinearMap.opNorm_comp_le (F.comp (e : Y →L[ℝ] X))
      (e.symm : X →L[ℝ] Y)
    have hnorme : ‖(e.symm : X →L[ℝ] Y)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound (f := (e.symm : X →L[ℝ] Y)) (M := 1) (by norm_num) ?_
      intro x
      simpa [one_mul] using (le_of_eq (LinearIsometry.norm_map e.symm x))
    have hbound : ‖F.comp (e : Y →L[ℝ] X)‖ * ‖(e.symm : X →L[ℝ] Y)‖ ≤ ‖F.comp (e : Y →L[ℝ] X)‖ * 1 :=
      mul_le_mul_of_nonneg_left hnorme (norm_nonneg _)
    have hle' : ‖(F.comp (e : Y →L[ℝ] X)).comp (e.symm : X →L[ℝ] Y)‖
        ≤ ‖F.comp (e : Y →L[ℝ] X)‖ :=
      (le_trans hcomp (by simpa using hbound))
    have hcomp_id : (F.comp (e : Y →L[ℝ] X)).comp (e.symm : X →L[ℝ] Y) = F := by
      ext x; simp
    -- rewrite the left-hand side of hle' using hcomp_id
    -- rewrite the left-hand side of hle' using hcomp_id
    have hle'' := hle'
    -- explicit rewrite avoids simp failing to see the LHS
    rw [hcomp_id] at hle''
    exact hle''
  exact le_antisymm hle hge

/-- WLPO ⇒ DualIsBanach for (c₀)* via the ℓ¹ identification. -/
lemma dual_is_banach_c0_dual_from_WLPO (h : WLPO) :
    DualIsBanach (c₀ →L[ℝ] ℝ) := by
  classical
  -- Identify (c₀)* with ℓ¹
  let e := (dual_c0_iso_l1 (ι := ℕ))
  -- Provide nontriviality for ℓ¹ and (c₀)*
  haveI : Nontrivial l1 := by
    classical
    exact ⟨⟨l1basis 0, 0, l1basis_ne_zero 0⟩⟩
  haveI : Nontrivial (c₀ →L[ℝ] ℝ) := by
    classical
    refine ⟨⟨e.symm (l1basis 0), 0, ?_⟩⟩
    intro hzero
    have h0 : (l1basis 0 : l1) = 0 := by
      have h0' := congrArg e hzero
      simpa using h0'
    exact (l1basis_ne_zero 0) h0
  -- Build DualIsBanach on (c₀)* from the ℓ¹ statement
  refine
    { norm_located := ?_
      norm_attained := ?_
      complete := by infer_instance
      closed_zero := ?_
      closed_neg := ?_
      closed_smul := ?_
      closed_add := ?_ }
  · intro F ε hε
    let φ : l1 →L[ℝ] ℝ := F.comp (e.symm : l1 →L[ℝ] (c₀ →L[ℝ] ℝ))
    have hloc := (dual_is_banach_l1_from_WLPO h).norm_located φ ε hε
    rcases hloc with ⟨q, hq⟩
    have hnorm : ‖φ‖ = ‖F‖ := by
      simpa [φ] using (opNorm_comp_linearIsometryEquiv F e.symm)
    refine ⟨q, ?_⟩
    simpa [hnorm] using hq
  · intro F ε hε
    let φ : l1 →L[ℝ] ℝ := F.comp (e.symm : l1 →L[ℝ] (c₀ →L[ℝ] ℝ))
    obtain ⟨x, hx, hFx⟩ := (dual_is_banach_l1_from_WLPO h).norm_attained φ ε hε
    -- pull back along the isometry
    let y : (c₀ →L[ℝ] ℝ) := e.symm x
    have hy : ‖y‖ ≤ 1 := by
      simpa [y] using (show ‖x‖ ≤ (1 : ℝ) from hx)
    have hFy : ‖F y‖ ≥ ‖F‖ - ε := by
      have hnorm : ‖φ‖ = ‖F‖ := by
        simpa [φ] using (opNorm_comp_linearIsometryEquiv F e.symm)
      have hval : F y = φ x := by
        rfl
      -- rewrite
      simpa [hnorm, hval] using hFx
    exact ⟨y, hy, hFy⟩
  ·
    exact (hasOperatorNorm_of_nontrivial (X := (c₀ →L[ℝ] ℝ))
      (f := (0 : (c₀ →L[ℝ] ℝ) →L[ℝ] ℝ)))
  · intro f _
    exact (hasOperatorNorm_of_nontrivial (X := (c₀ →L[ℝ] ℝ)) (f := -f))
  · intro a f _
    exact (hasOperatorNorm_of_nontrivial (X := (c₀ →L[ℝ] ℝ)) (f := a • f))
  · intro f g _ _
    exact (hasOperatorNorm_of_nontrivial (X := (c₀ →L[ℝ] ℝ)) (f := f + g))

/-- LPO ⇒ DualIsBanach for (c₀)* via the ℓ¹ identification. -/
lemma dual_is_banach_c0_dual_from_LPO (h : LPO) :
    DualIsBanach (c₀ →L[ℝ] ℝ) := by
  -- Identify (c₀)* with ℓ¹
  let e := (dual_c0_iso_l1 (ι := ℕ))
  -- Provide nontriviality for ℓ¹ and (c₀)*
  haveI : Nontrivial l1 := by
    exact ⟨⟨l1basis 0, 0, l1basis_ne_zero 0⟩⟩
  haveI : Nontrivial (c₀ →L[ℝ] ℝ) := by
    refine ⟨⟨e.symm (l1basis 0), 0, ?_⟩⟩
    intro hzero
    have h0 : (l1basis 0 : l1) = 0 := by
      have h0' := congrArg e hzero
      simpa using h0'
    exact (l1basis_ne_zero 0) h0
  -- Build DualIsBanach on (c₀)* from the ℓ¹ statement
  refine
    { norm_located := ?_
      norm_attained := ?_
      complete := by infer_instance
      closed_zero := ?_
      closed_neg := ?_
      closed_smul := ?_
      closed_add := ?_ }
  · intro F ε hε
    let φ : l1 →L[ℝ] ℝ := F.comp (e.symm : l1 →L[ℝ] (c₀ →L[ℝ] ℝ))
    have hloc := (dual_is_banach_l1_from_LPO h).norm_located φ ε hε
    rcases hloc with ⟨q, hq⟩
    have hnorm : ‖φ‖ = ‖F‖ := by
      simpa [φ] using (opNorm_comp_linearIsometryEquiv F e.symm)
    refine ⟨q, ?_⟩
    simpa [hnorm] using hq
  · intro F ε hε
    let φ : l1 →L[ℝ] ℝ := F.comp (e.symm : l1 →L[ℝ] (c₀ →L[ℝ] ℝ))
    obtain ⟨x, hx, hFx⟩ := (dual_is_banach_l1_from_LPO h).norm_attained φ ε hε
    -- pull back along the isometry
    let y : (c₀ →L[ℝ] ℝ) := e.symm x
    have hy : ‖y‖ ≤ 1 := by
      simpa [y] using (show ‖x‖ ≤ (1 : ℝ) from hx)
    have hFy : ‖F y‖ ≥ ‖F‖ - ε := by
      have hnorm : ‖φ‖ = ‖F‖ := by
        simpa [φ] using (opNorm_comp_linearIsometryEquiv F e.symm)
      have hval : F y = φ x := by
        rfl
      -- rewrite
      simpa [hnorm, hval] using hFx
    exact ⟨y, hy, hFy⟩
  ·
    exact (hasOperatorNorm_of_nontrivial (X := (c₀ →L[ℝ] ℝ))
      (f := (0 : (c₀ →L[ℝ] ℝ) →L[ℝ] ℝ)))
  · intro f _
    exact (hasOperatorNorm_of_nontrivial (X := (c₀ →L[ℝ] ℝ)) (f := -f))
  · intro a f _
    exact (hasOperatorNorm_of_nontrivial (X := (c₀ →L[ℝ] ℝ)) (f := a • f))
  · intro f g _ _
    exact (hasOperatorNorm_of_nontrivial (X := (c₀ →L[ℝ] ℝ)) (f := f + g))

end Papers.P2.HB
