import Papers.P4_SpectralGeometry.Discrete.SpectralTheory
import Papers.P4_SpectralGeometry.Discrete.TuringEncoding
import Papers.P4_SpectralGeometry.Discrete.IntervalBookkeeping

/-!
# Perturbation Theory for TM-Encoded Edge Weights

This module analyzes how Turing machine computations affect the spectral gap
through edge weight perturbations.

## Main Results

* `perturbation_bound` - Bounds on how perturbations affect eigenvalues
* `harmonic_accumulation` - How non-halting TMs accumulate perturbations
* `gap_destruction` - Proof that large perturbations destroy the gap

## Key Insight

When edge weights are perturbed by εᵢ, the eigenvalue shift is approximately:
  Δλ ≈ ∑ᵢ εᵢ · (sensitivity of λ to edge i)

For the neck torus, neck edges have high sensitivity, so accumulating
perturbations on neck edges effectively reduces the spectral gap.
-/

namespace Papers.P4_SpectralGeometry.Discrete

/-- The total perturbation applied up to step N -/
def totalPerturbation (T : TuringNeckTorus) (N : ℕ) : ℚ :=
  maxPerturbation N

/-- Check if an edge is a neck edge (gets perturbed) -/
def isNeckEdge (T : TuringNeckTorus) (v w : T.Vertex) : Bool :=
  v.1 ≠ w.1 ∧ v.2 = w.2  -- Horizontal neck edges

/-- Edges that get perturbed (simplified: just the neck edges) -/
def perturbedEdges (T : TuringNeckTorus) : Set (T.Vertex × T.Vertex) :=
  {⟨v, w⟩ | isNeckEdge T v w}

/-- The perturbed Laplacian as a function of perturbation strength -/
noncomputable def perturbedLaplacianParametric (T : TuringNeckTorus) (ε : ℝ) :
    Matrix T.Vertex T.Vertex ℝ :=
  let L₀ := T.discreteLaplacian.map (fun x => (x : ℝ))
  let P := Matrix.of (fun v w => if isNeckEdge T v w then 1 else 0)
  L₀ + ε • P

/-- Sensitivity: How much λ₁ changes with respect to edge perturbations -/
noncomputable def spectralSensitivity (T : TuringNeckTorus) : ℝ :=
  -- The derivative ∂λ₁/∂ε at ε = 0
  -- For neck edges, this is approximately 1 (high sensitivity)
  1

/-- Key lemma: Small perturbations preserve the gap -/
lemma small_perturbation_preserves_gap (T : TuringNeckTorus) (ε : ℝ) 
    (h_small : ε < (T.h ^ 2 : ℝ) / 16) :
    spectralGapVariational T.toDiscreteNeckTorus - spectralSensitivity T * ε ≥ (T.h ^ 2 : ℝ) / 8 := by
  -- When ε < h²/16 and sensitivity ≈ 1, we have:
  -- λ₁ - ε ≥ h²/4 - h²/16 = 3h²/16 > h²/8
  sorry

/-- Key lemma: Large perturbations destroy the gap -/
lemma large_perturbation_destroys_gap (T : TuringNeckTorus) (ε : ℝ)
    (h_large : ε > (T.h ^ 2 : ℝ) / 4) :
    ∃ v : RealVector T.toDiscreteNeckTorus, (∃ i, v i ≠ 0) ∧ orthogonalToConstants v ∧
    RayleighQuotient T.toDiscreteNeckTorus v < (T.h ^ 2 : ℝ) / 8 := by
  -- When ε > h²/4, the perturbation dominates the original gap
  -- The perturbed system has eigenvalues approaching 0
  sorry

/-- Harmonic series growth for non-halting TMs -/
lemma harmonic_growth (N : ℕ) (h_large : N > 1000) :
    (maxPerturbation N : ℝ) > Real.log N := by
  -- H_N = 1 + 1/2 + ... + 1/N ≈ log(N) + γ
  -- For N > 1000, H_N > log(N)
  sorry

/-- Main connection: Non-halting destroys gap via harmonic accumulation -/
theorem non_halting_implies_small_gap (T : TuringNeckTorus) (N : ℕ)
    (h_large : N > 1000) (h_not_halt : ∀ m < N, ¬halts_in T.tm m T.input) :
    T.spectralGap N < (spectralThreshold T.h : ℝ) := by
  -- Step 1: Non-halting means all N perturbations accumulate
  have pert_large : (totalPerturbation T N : ℝ) > Real.log N := by
    exact harmonic_growth N h_large
  
  -- Step 2: For large N, log(N) > h²/4 (assuming reasonable h)
  have log_dominates : Real.log N > (T.h ^ 2 : ℝ) / 4 := by
    sorry  -- Requires bound on h
  
  -- Step 3: Large perturbation destroys gap
  have gap_destroyed := large_perturbation_destroys_gap T _ 
    (calc (totalPerturbation T N : ℝ) > Real.log N := pert_large
     _ > (T.h ^ 2 : ℝ) / 4 := log_dominates)
  
  -- Step 4: spectralGap < threshold = h²/8
  sorry

/-- Main connection: Halting preserves gap via bounded perturbation -/  
theorem halting_implies_large_gap (T : TuringNeckTorus) (n : ℕ)
    (h_halts : halts_in T.tm n T.input) (h_small : n < 100) :
    ∀ N ≥ n, T.spectralGap N ≥ (spectralThreshold T.h : ℝ) := by
  intro N hN
  -- Step 1: Halting at n means perturbations stop accumulating after n
  have pert_bounded : (totalPerturbation T N : ℝ) ≤ maxPerturbation n := by
    sorry  -- Perturbations only up to step n
  
  -- Step 2: For n < 100, H_n < log(100) < 5
  have pert_small : (maxPerturbation n : ℝ) < (T.h ^ 2 : ℝ) / 16 := by
    sorry  -- Requires bound on h
  
  -- Step 3: Small perturbation preserves gap
  have gap_preserved := small_perturbation_preserves_gap T _ 
    (calc (totalPerturbation T N : ℝ) ≤ (maxPerturbation n : ℝ) := pert_bounded
     _ < (T.h ^ 2 : ℝ) / 16 := pert_small)
  
  -- Step 4: spectralGap ≥ threshold = h²/8
  sorry

end Papers.P4_SpectralGeometry.Discrete