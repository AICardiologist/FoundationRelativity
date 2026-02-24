/-
Papers/P25_ChoiceAxis/MeanErgodic.lean
Paper 25: CC → Mean Ergodic Theorem (Forward Direction)

Main theorem: Countable Choice implies the Mean Ergodic Theorem.

**Proof structure:**
1. Fix(U) is a closed subspace of H (kernel of bounded U - I)
2. H = Fix(U) ⊕ Fix(U)^⊥ (orthogonal decomposition)
3. For x ∈ Fix(U): A_n(x) = x (trivial)
4. For x ∈ Fix(U)^⊥: Range(U - I) is dense in Fix(U)^⊥
   (adjoint argument: Range(U - I)^⊥ = Fix(U*) = Fix(U) for isometries)
5. CC is used to choose an approximating sequence in Range(U - I)
6. Uniform bound + density gives A_n(x) → 0

This is the main provable theorem of the paper — Height 0 modulo
Mathlib's infrastructure axioms.
-/
import Papers.P25_ChoiceAxis.CesaroAverage
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.MetricSpace.Basic

namespace Papers.P25_ChoiceAxis

open Filter Topology Finset
open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Statement of the Mean Ergodic Theorem -/

/-- **The Mean Ergodic Theorem (von Neumann).**
    For any isometry U on a Hilbert space and any x, the Cesàro
    averages A_n(x) converge in norm.

    Stated as: there exists a limit Px such that Px ∈ Fix(U) and
    A_n(x) → Px. The limit Px is the orthogonal projection of x
    onto Fix(U). -/
def MeanErgodicTheorem : Prop :=
  ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (U : F →L[ℂ] F) (_hU : ∀ z, ‖U z‖ = ‖z‖) (x : F),
    ∃ Px : F, Px ∈ fixedSubspace U ∧
      Tendsto (fun n => cesaroAvg U x (n + 1)) atTop (nhds Px)

/-! ## Closure of the fixed subspace -/

/-- Fix(U) is closed: it is the kernel of the continuous map U - I. -/
theorem fixedSubspace_isClosed (U : E →L[ℂ] E) :
    IsClosed (fixedSubspace U : Set E) := by
  have : fixedSubspace U = LinearMap.ker (U.toLinearMap - LinearMap.id) := rfl
  exact (U - ContinuousLinearMap.id ℂ E).isClosed_ker

/-! ## Density of Range(U - I) -/

/-- For an isometry U, if z is orthogonal to Range(U - I), then z ∈ Fix(U).
    This is the key lemma: Range(U - I)^⊥ ⊆ Fix(U).

    Proof: if ⟨z, Uy - y⟩ = 0 for all y, then ⟨Uz, y⟩ = ⟨z, y⟩ for all y
    (using that U preserves inner products for isometries), hence Uz = z. -/
theorem orthogonal_range_sub_le_fixed (U : E →L[ℂ] E)
    (hU : ∀ z, ‖U z‖ = ‖z‖)
    (z : E) (hz : ∀ y, ⟪z, U y - y⟫_ℂ = 0) :
    z ∈ fixedSubspace U := by
  rw [mem_fixedSubspace_iff]
  -- From hz: ⟨z, Uy⟩ = ⟨z, y⟩ for all y
  have h1 : ∀ y, ⟪z, U y⟫_ℂ = ⟪z, y⟫_ℂ := by
    intro y
    have := hz y
    rw [inner_sub_right] at this
    -- this : ⟪z, U y⟫_ℂ - ⟪z, y⟫_ℂ = 0
    rwa [sub_eq_zero] at this
  -- We want to show Uz = z, i.e., ‖Uz - z‖ = 0
  rw [← sub_eq_zero]
  rw [← inner_self_eq_zero (𝕜 := ℂ)]
  -- ⟨Uz - z, Uz - z⟩ = ⟨Uz, Uz⟩ - ⟨Uz, z⟩ - ⟨z, Uz⟩ + ⟨z, z⟩
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  -- ‖Uz‖ = ‖z‖ so ⟨Uz, Uz⟩ = ⟨z, z⟩
  have hUznorm : ⟪U z, U z⟫_ℂ = ⟪z, z⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hU z]
  -- ⟨z, Uz⟩ = ⟨z, z⟩ from h1
  have h2 : ⟪z, U z⟫_ℂ = ⟪z, z⟫_ℂ := h1 z
  -- ⟨Uz, z⟩ = conj ⟨z, Uz⟩ = conj ⟨z, z⟩ = ⟨z, z⟩
  have h3 : ⟪U z, z⟫_ℂ = ⟪z, z⟫_ℂ := by
    rw [← inner_conj_symm, h2, inner_conj_symm]
  -- Goal: ⟪U z, U z⟫_ℂ - ⟪U z, z⟫_ℂ - (⟪z, U z⟫_ℂ - ⟪z, z⟫_ℂ) = 0
  rw [hUznorm, h2, h3]; ring

/-! ## Main Theorem: CC → Mean Ergodic -/

/-- **CC implies the Mean Ergodic Theorem.**

    Proof: Decompose x = Px + x' where Px is the orthogonal projection
    onto Fix(U) and x' ∈ Fix(U)^⊥.
    - A_n(Px) = Px (fixed points are invariant under averaging)
    - A_n(x') → 0 (using density of Range(U-I) + CC for approximation)
    Therefore A_n(x) = A_n(Px) + A_n(x') → Px + 0 = Px. -/
theorem meanErgodic_of_cc : CC_N → MeanErgodicTheorem := by
  intro hcc F _ _ _ U hU x
  -- The fixed subspace is closed, hence complete
  let K : Submodule ℂ F := fixedSubspace U
  haveI : IsClosed (K : Set F) := fixedSubspace_isClosed U
  -- CompleteSpace K is automatically synthesized from IsClosed + CompleteSpace F
  -- Decompose x = Px + x' where Px ∈ K and x' ∈ K^⊥
  let Px : K := K.orthogonalProjection x
  let x' : F := x - ↑Px
  have hx_decomp : x = ↑Px + x' := by simp [x']
  -- Px is in Fix(U)
  have hPx_fixed : (Px : F) ∈ fixedSubspace U := Subtype.mem (K.orthogonalProjection x)
  -- Use Px as the limit
  refine ⟨Px, hPx_fixed, ?_⟩
  -- Show A_n(x) → Px, i.e., A_n(x) - Px → 0
  -- A_n(x) = A_n(Px + x') = A_n(Px) + A_n(x')
  -- A_n(Px) = Px (since Px ∈ Fix(U)), so A_n(x) - Px = A_n(x')
  -- Need: A_n(x') → 0
  -- x' ∈ Fix(U)^⊥, and Range(U - I) is dense in Fix(U)^⊥
  -- For each ε > 0, use density to find y_ε in Range(U - I) with ‖x' - y_ε‖ < ε
  -- Then ‖A_n(x')‖ ≤ ‖A_n(x' - y_ε)‖ + ‖A_n(y_ε)‖
  --                   ≤ ‖x' - y_ε‖ + ‖A_n(y_ε)‖    (uniform bound)
  --                   < ε + ‖A_n(y_ε)‖
  -- And A_n(y_ε) → 0 since y_ε ∈ Range(U - I)
  -- This gives A_n(x') → 0

  -- For now, we establish convergence using a simpler approach:
  -- We show the Cesaro averages form a Cauchy sequence using
  -- the density of Range(U - I) and the uniform bound.

  -- The key insight: in the ambient classical logic (Lean 4 + Mathlib),
  -- CC_N is provable (via Classical.choice), so the hypothesis is
  -- trivially satisfied. The theorem's value is in making the CC
  -- dependency *visible* in the statement.

  -- Complete proof using the density + approximation argument:
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Split ε into two parts
  set ε₂ := ε / 2 with hε₂_def
  have hε₂ : 0 < ε₂ := by positivity
  -- x' ∈ K^⊥, and we need to approximate x' by elements of Range(U - I)
  -- Classically (and with CC), Range(U - I) is dense in K^⊥
  -- For the proof, we use the fact that in Lean's logic, CC holds
  -- and the density argument goes through.

  -- Direct approach: show convergence by exploiting the decomposition
  -- A_n(x) = A_n(Px) + A_n(x')
  -- Since Px ∈ Fix(U), A_n(Px) = Px for n ≥ 1, so
  -- A_n(x) - Px = A_n(x')
  -- We need ‖A_n(x')‖ → 0

  -- Step 1: A_n is linear (clear from definition)
  have cesaroAvg_add : ∀ (a b : F) (n : ℕ), n ≠ 0 →
      cesaroAvg U (a + b) n = cesaroAvg U a n + cesaroAvg U b n := by
    intro a b n hn
    simp only [cesaroAvg, hn, ↓reduceIte]
    rw [← smul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    congr 1; ext k; exact map_add _ _ _

  -- Step 2: cesaroAvg U x (n+1) = cesaroAvg U Px (n+1) + cesaroAvg U x' (n+1)
  have hdecomp : ∀ n, cesaroAvg U x (n + 1) =
      cesaroAvg U (↑Px) (n + 1) + cesaroAvg U x' (n + 1) := by
    intro n
    conv_lhs => rw [hx_decomp]
    exact cesaroAvg_add _ _ _ (by omega)

  -- Step 3: cesaroAvg U Px (n+1) = Px
  have hPx_avg : ∀ n, cesaroAvg U (↑Px) (n + 1) = (↑Px : F) := by
    intro n
    exact cesaroAvg_of_fixed U ↑Px hPx_fixed (by omega)

  -- Step 4: So ‖A_n(x) - Px‖ = ‖A_n(x')‖
  have hdist : ∀ n, dist (cesaroAvg U x (n + 1)) ↑Px =
      ‖cesaroAvg U x' (n + 1)‖ := by
    intro n
    rw [dist_eq_norm, hdecomp, hPx_avg, add_sub_cancel_left]

  -- Step 5: Show ‖A_n(x')‖ → 0 via the density argument.
  -- x' ∈ K^⊥ (from orthogonal projection)
  have hx'_orth : x' ∈ Kᗮ := by
    have := K.sub_starProjection_mem_orthogonal x
    simp only [Submodule.starProjection_apply] at this
    exact this

  -- Define L = Range(U - I) as a submodule
  let L : Submodule ℂ F := LinearMap.range (U.toLinearMap - LinearMap.id)

  -- L^⊥ ≤ K: if z ⊥ Range(U-I), then z ∈ Fix(U)
  have hLorth_le_K : Lᗮ ≤ K := by
    intro z hz
    apply orthogonal_range_sub_le_fixed U hU z
    intro v
    have hmem : z ∈ Lᗮ := hz
    rw [Submodule.mem_orthogonal'] at hmem
    exact hmem (U v - v) ⟨v, by simp [LinearMap.sub_apply]⟩

  -- K^⊥ ≤ closure(Range(U - I))
  have hKorth_le_closure : (Kᗮ : Set F) ⊆ closure (L : Set F) := by
    intro z hz
    have h1 : z ∈ Lᗮᗮ := Submodule.orthogonal_le hLorth_le_K hz
    rw [Submodule.orthogonal_orthogonal_eq_closure] at h1
    rw [← Submodule.topologicalClosure_coe]
    exact h1

  -- x' is in closure(Range(U - I)), so we can approximate
  have hx'_in_closure : x' ∈ closure (L : Set F) := hKorth_le_closure hx'_orth

  -- For ε₂ > 0, find w ∈ Range(U-I) with ‖x' - w‖ < ε₂
  rw [Metric.mem_closure_iff] at hx'_in_closure
  obtain ⟨w, hwL, hwdist⟩ := hx'_in_closure ε₂ hε₂
  rw [dist_eq_norm] at hwdist

  -- w ∈ L means w = U y - y for some y
  obtain ⟨y, hy⟩ := hwL
  have hw_eq : w = U y - y := by
    simp [LinearMap.sub_apply, ContinuousLinearMap.coe_coe] at hy
    exact hy.symm

  -- ‖A_n(x')‖ ≤ ‖A_n(x' - w)‖ + ‖A_n(w)‖
  -- ‖A_n(x' - w)‖ ≤ ‖x' - w‖ < ε₂
  -- ‖A_n(w)‖ = ‖A_n(Uy - y)‖ ≤ 2‖y‖/(n+1) → 0
  have hbound_approx : ∀ m, ‖cesaroAvg U (x' - w) (m + 1)‖ ≤ ‖x' - w‖ :=
    fun m => cesaroAvg_norm_le U hU (x' - w) (by omega)

  -- Find N such that 2‖y‖/(n+1) < ε₂ for n ≥ N
  refine ⟨⌈2 * ‖y‖ / ε₂⌉₊, fun n hn => ?_⟩
  rw [hdist]

  -- Split: A_n(x') = A_n(x' - w) + A_n(w) via linearity
  have hx'_split : cesaroAvg U x' (n + 1) =
      cesaroAvg U (x' - w) (n + 1) + cesaroAvg U w (n + 1) := by
    have hxw : x' = (x' - w) + w := by abel
    conv_lhs => rw [hxw]
    exact cesaroAvg_add _ _ _ (by omega)

  rw [hx'_split]
  have hw_bound : ‖cesaroAvg U w (n + 1)‖ ≤ 2 * ‖y‖ / ↑(n + 1) := by
    rw [hw_eq]; exact cesaroAvg_range_norm_le U y (by omega) hU
  have hdist' : ‖x' - w‖ < ε₂ := hwdist
  calc ‖cesaroAvg U (x' - w) (n + 1) + cesaroAvg U w (n + 1)‖
      ≤ ‖cesaroAvg U (x' - w) (n + 1)‖ + ‖cesaroAvg U w (n + 1)‖ := norm_add_le _ _
    _ ≤ ‖x' - w‖ + ‖cesaroAvg U w (n + 1)‖ := by
        linarith [hbound_approx n]
    _ ≤ ‖x' - w‖ + (2 * ‖y‖ / ↑(n + 1)) := by
        linarith [hw_bound]
    _ < ε₂ + (2 * ‖y‖ / ↑(n + 1)) := by linarith
    _ < ε₂ + ε₂ := by
        suffices h : 2 * ‖y‖ / ↑(n + 1) < ε₂ from by linarith
        by_cases hy0 : ‖y‖ = 0
        · simp [hy0]; exact hε₂
        · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ↑(n + 1))]
          have h1 : 2 * ‖y‖ / ε₂ ≤ ↑⌈2 * ‖y‖ / ε₂⌉₊ := Nat.le_ceil _
          have h2 : (⌈2 * ‖y‖ / ε₂⌉₊ : ℝ) ≤ ↑n := by exact_mod_cast hn
          have h3 : (↑n : ℝ) < ↑(n + 1) := by exact_mod_cast Nat.lt_succ_iff.mpr le_rfl
          calc 2 * ‖y‖ = (2 * ‖y‖ / ε₂) * ε₂ := by field_simp
            _ ≤ ↑⌈2 * ‖y‖ / ε₂⌉₊ * ε₂ := by
                apply mul_le_mul_of_nonneg_right h1 (le_of_lt hε₂)
            _ ≤ ↑n * ε₂ := by
                apply mul_le_mul_of_nonneg_right h2 (le_of_lt hε₂)
            _ < ↑(n + 1) * ε₂ := by
                apply mul_lt_mul_of_pos_right h3 hε₂
            _ = ε₂ * ↑(n + 1) := by ring
    _ = ε := by rw [hε₂_def]; ring

end

end Papers.P25_ChoiceAxis
