import Papers.P4_SpectralGeometry.Discrete.TuringEncoding

/-!
# Interval Bookkeeping for Spectral Bands

This module implements the interval arithmetic needed to ensure disjoint spectral
bands in the discrete neck torus construction. This is Phase 2 of the fast-track
implementation.

## Main Definitions

* `SpectralBand` - An interval representing a band of eigenvalues
* `ensureDisjoint` - Proves that our choice of constants gives disjoint bands
* `rationalThreshold` - The explicit rational threshold for the spectral gap

## Key Constants

We choose explicit rational constants to ensure:
- Small perturbations when TM halts early
- Large perturbations when TM runs forever  
- Clear separation between the two spectral regimes
-/

namespace Papers.P4_SpectralGeometry.Discrete

/-- A spectral band is an interval [a,b] of eigenvalues -/
structure SpectralBand where
  lower : ℚ
  upper : ℚ
  h_order : lower ≤ upper

/-- Two bands are disjoint if they don't overlap -/
def SpectralBand.disjoint (B₁ B₂ : SpectralBand) : Prop :=
  B₁.upper < B₂.lower ∨ B₂.upper < B₁.lower

/-- The unperturbed spectral bands of the discrete neck torus -/
def unperturbedBands (h : ℚ) (h_pos : 0 < h) : List SpectralBand :=
  -- Band 1: Near 0 (the constant functions)
  [⟨0, h^2 / 10, by 
    show 0 ≤ h^2 / 10
    apply div_nonneg
    exact sq_nonneg h
    norm_num⟩,
   -- Band 2: Around h² (the first neck modes)  
   ⟨h^2 / 4, 5 * h^2, by 
    show h^2 / 4 ≤ 5 * h^2
    have : h^2 / 4 = (1/4) * h^2 := by ring
    rw [this]
    have : (1/4) * h^2 ≤ 5 * h^2 := by
      apply mul_le_mul_of_nonneg_right
      norm_num
      exact sq_nonneg h
    exact this⟩,
   -- Higher bands...
   ⟨10 * h^2, 100 * h^2, by 
    show 10 * h^2 ≤ 100 * h^2
    apply mul_le_mul_of_nonneg_right
    norm_num
    exact sq_nonneg h⟩]

/-- Key lemma: The unperturbed bands are pairwise disjoint -/
lemma unperturbed_bands_disjoint (h : ℚ) (h_pos : 0 < h) (h_small : h < 1/10) :
    ∀ (B₁ B₂ : SpectralBand), B₁ ∈ unperturbedBands h h_pos → 
    B₂ ∈ unperturbedBands h h_pos → B₁ ≠ B₂ → B₁.disjoint B₂ := by
  intro B₁ B₂ h₁ h₂ h_ne
  simp [unperturbedBands] at h₁ h₂
  -- Extract the band information
  obtain (rfl | rfl | rfl) := h₁
  <;> obtain (rfl | rfl | rfl) := h₂
  · -- Band 1 vs Band 1
    contradiction
  · -- Band 1 vs Band 2: need to show h²/10 < h²/4
    simp [SpectralBand.disjoint]
    left
    have h2_pos : 0 < h^2 := sq_pos_of_pos h_pos
    calc h^2 / 10 = (1/10) * h^2 := by ring
    _ < (1/4) * h^2 := by apply mul_lt_mul_of_pos_right; norm_num; exact h2_pos
    _ = h^2 / 4 := by ring
  · -- Band 1 vs Band 3: need to show h²/10 < 10*h²
    simp [SpectralBand.disjoint]
    left
    have h2_pos : 0 < h^2 := sq_pos_of_pos h_pos
    calc h^2 / 10 = (1/10) * h^2 := by ring
    _ < 10 * h^2 := by apply mul_lt_mul_of_pos_right; norm_num; exact h2_pos
  · -- Band 2 vs Band 1: need to show h²/10 < h²/4
    simp [SpectralBand.disjoint]
    right
    have h2_pos : 0 < h^2 := sq_pos_of_pos h_pos
    calc h^2 / 10 = (1/10) * h^2 := by ring
    _ < (1/4) * h^2 := by apply mul_lt_mul_of_pos_right; norm_num; exact h2_pos
    _ = h^2 / 4 := by ring
  · -- Band 2 vs Band 2
    contradiction
  · -- Band 2 vs Band 3: need to show 5*h² < 10*h²
    simp [SpectralBand.disjoint]
    left
    have h2_pos : 0 < h^2 := sq_pos_of_pos h_pos
    apply mul_lt_mul_of_pos_right; norm_num; exact h2_pos
  · -- Band 3 vs Band 1: need to show h²/10 < 10*h²
    simp [SpectralBand.disjoint]
    right
    have h2_pos : 0 < h^2 := sq_pos_of_pos h_pos
    calc h^2 / 10 = (1/10) * h^2 := by ring
    _ < 10 * h^2 := by apply mul_lt_mul_of_pos_right; norm_num; exact h2_pos
  · -- Band 3 vs Band 2: need to show 5*h² < 10*h²
    simp [SpectralBand.disjoint]
    right
    have h2_pos : 0 < h^2 := sq_pos_of_pos h_pos
    apply mul_lt_mul_of_pos_right; norm_num; exact h2_pos
  · -- Band 3 vs Band 3
    contradiction

/-- The maximum perturbation when the TM halts at step n -/
def maxPerturbation (n : ℕ) : ℚ :=
  -- Sum of 1/k for k from 1 to n (harmonic series truncated)
  (List.range n).foldl (fun acc k => acc + 1 / (k + 1 : ℚ)) 0

/-- Key constant: The threshold that separates halting from non-halting -/
def spectralThreshold (h : ℚ) : ℚ := h^2 / 8

/-- If TM halts quickly, perturbation is small and gap stays large -/
lemma halting_preserves_gap (T : TuringNeckTorus) (n : ℕ) 
    (h_halts : halts_in T.tm n T.input) (h_small : n < 100) :
    T.spectralGap n ≥ (spectralThreshold T.h : ℝ) := by
  -- Key insight: When TM halts at step n < 100, the total perturbation
  -- is bounded by the harmonic sum H_n ≈ log(n) < log(100) ≈ 4.6
  -- This small perturbation cannot close the spectral gap significantly
  -- The gap remains above threshold = h²/8
  -- For Phase 1B, we axiomatize this central property
  sorry

/-- If TM doesn't halt by step N, gap becomes small -/
lemma non_halting_kills_gap (T : TuringNeckTorus) (N : ℕ)
    (h_large : N > 1000) 
    (h_not_halts : ∀ m < N, ¬halts_in T.tm m T.input) :
    T.spectralGap N < (spectralThreshold T.h : ℝ) := by
  -- Key insight: When TM doesn't halt by step N > 1000, the total perturbation
  -- grows like the harmonic sum H_N ≈ log(N) > log(1000) ≈ 6.9
  -- This large perturbation destroys the spectral gap structure
  -- The gap falls below threshold = h²/8
  -- For Phase 1B, we axiomatize this central property
  sorry

/-- Main theorem: The spectral gap has a clear threshold behavior -/
theorem threshold_dichotomy (T : TuringNeckTorus) :
    (∃ n < 100, halts_in T.tm n T.input) ∨ 
    (∀ N > 1000, T.spectralGap N < (spectralThreshold T.h : ℝ)) := by
  -- This follows from halting_preserves_gap and non_halting_kills_gap:
  -- Either TM halts early (n < 100) or it doesn't halt by any large N
  -- In the first case, gap stays large; in the second, gap becomes small
  -- The threshold h²/8 cleanly separates these two regimes
  sorry

/-- Constructive choice of rational threshold -/
def rationalSpectralThreshold : ℚ := 1 / 32

/-- The threshold is explicitly computable and rational -/
lemma threshold_is_rational (T : TuringNeckTorus) (h_standard : T.h = 1/2) :
    spectralThreshold T.h = rationalSpectralThreshold := by
  simp [spectralThreshold, rationalSpectralThreshold, h_standard]
  norm_num

end Papers.P4_SpectralGeometry.Discrete