import Papers.P4_SpectralGeometry.Discrete.PerturbationTheory
import Papers.P4_SpectralGeometry.Discrete.SpectralTheory

/-!
# Perturbation Bounds via Consultant's Variational Argument

This module implements the consultant's key insight: use the unperturbed
eigenvector as a test function for the perturbed system.

## Main Results

* `perturbation_upper_bound` - Non-halting destroys gap via test function
* `weyl_lower_bound` - Halting preserves gap via Weyl's inequality
* `gap_collapse_theorem` - The main quantitative bound

## Key Insight

For the perturbed Laplacian L_N = L_0 + ΔL_N, we have:
  λ₁(L_N) ≤ R(v₁, L_N) = λ₁(L_0) + ⟨v₁, ΔL_N v₁⟩/⟨v₁, v₁⟩
where v₁ is the unperturbed eigenvector.
-/

namespace Papers.P4_SpectralGeometry.Discrete

/-- The unperturbed eigenvector (neck test function) -/
noncomputable def unperturbedEigenvector (T : DiscreteNeckTorus) : RealVector T :=
  neckTestFunction T

/-- Quadratic form of Laplacian: ⟨v, Lv⟩ = Σ w_ij(v_i - v_j)² -/
noncomputable def laplacianQuadraticForm (T : DiscreteNeckTorus) 
    (L : Matrix T.Vertex T.Vertex ℝ) (v : RealVector T) : ℝ :=
  Finset.univ.sum fun i => 
    Finset.univ.sum fun j => 
      L i j * (v i - v j)^2

/-- Key lemma: Test function has large variation across neck -/
lemma neck_test_variation (T : DiscreteNeckTorus) (i j : T.Vertex) 
    (h_neck : i.1 ≠ j.1 ∧ i.2 = j.2) :  -- Neck edge
    (unperturbedEigenvector T i - unperturbedEigenvector T j)^2 = 4 := by
  -- The test function is +1 on one side, -1 on other
  simp only [unperturbedEigenvector, neckTestFunction]
  -- For a proper neck edge in our discrete model, vertices on opposite sides
  -- are connected when they differ by approximately n/2 in the first coordinate
  -- This is the key property of the neck structure
  
  -- Since i and j are connected by a neck edge and the graph is designed
  -- so neck edges connect opposite halves, one must be < n/2 and other ≥ n/2
  have h_opposite_sides : (i.1.val < T.n / 2) ≠ (j.1.val < T.n / 2) := by
    -- This is a fundamental property of how neck edges are defined
    -- in the discrete neck torus structure
    sorry  -- Axiomatize this property of the neck graph
  
  -- Use h_opposite_sides to know one is < n/2 and other is ≥ n/2
  -- Then in both cases, the difference is ±2, squared = 4
  sorry

/-- The perturbation affects only neck edges -/
def isPerturbedEdge (T : TuringNeckTorus) (i j : T.Vertex) : Bool :=
  i.1 ≠ j.1 ∧ i.2 = j.2  -- Horizontal neck edges

/-- Perturbation matrix after N steps -/
noncomputable def perturbationMatrix (T : TuringNeckTorus) (N : ℕ) : 
    Matrix T.Vertex T.Vertex ℝ :=
  -- ΔL_N subtracts Σ(1/k) from neck edge weights
  Matrix.of fun i j => 
    if isPerturbedEdge T i j then 
      -(totalPerturbation T N : ℝ)
    else 0

/-- Main upper bound: Non-halting collapses gap -/
theorem perturbation_upper_bound (T : TuringNeckTorus) (N : ℕ) :
    let L₀ := T.discreteLaplacian.map (Rat.cast : ℚ → ℝ)
    let L_N := L₀ + perturbationMatrix T N
    let v₁ := unperturbedEigenvector T.toDiscreteNeckTorus
    T.spectralGap N ≤ spectralGapVariational T.toDiscreteNeckTorus + 
      ⟪v₁, (perturbationMatrix T N).mulVec v₁⟫ / ⟪v₁, v₁⟫ := by
  -- By variational principle: λ₁(L_N) ≤ R(v₁, L_N)
  -- R(v₁, L_N) = ⟨v₁, L_N v₁⟩ / ⟨v₁, v₁⟩
  --            = ⟨v₁, (L₀ + ΔL_N) v₁⟩ / ⟨v₁, v₁⟩
  --            = ⟨v₁, L₀ v₁⟩ / ⟨v₁, v₁⟩ + ⟨v₁, ΔL_N v₁⟩ / ⟨v₁, v₁⟩
  --            = R(v₁, L₀) + perturbation term
  -- Since v₁ is the eigenvector for L₀: R(v₁, L₀) = λ₁(L₀)
  sorry

/-- Number of neck edges in the torus -/
def neckEdgeCount (T : DiscreteNeckTorus) : ℕ := 
  -- Each vertex on one side connects to exactly one vertex on the other side
  -- So number of neck edges = T.n (one per position along the neck)
  T.n

/-- Concrete bound on perturbation term -/
lemma perturbation_term_bound (T : TuringNeckTorus) (N : ℕ) :
    let v₁ := unperturbedEigenvector T.toDiscreteNeckTorus
    |⟪v₁, (perturbationMatrix T N).mulVec v₁⟫| ≥ 
    4 * (neckEdgeCount T.toDiscreteNeckTorus : ℝ) * (totalPerturbation T N : ℝ) := by
  -- The quadratic form ⟨v, ΔL v⟩ = Σ_{edges} weight_change × (v_i - v_j)²
  -- For neck edges: weight_change = -H_N and (v_i - v_j)² = 4
  -- Number of neck edges = neckVertices.card
  simp only [perturbationMatrix]
  -- Expand inner product as sum over matrix entries
  sorry

/-- Main theorem: Large perturbation destroys gap -/
theorem gap_collapse_theorem (T : TuringNeckTorus) (N : ℕ) 
    (h_large : (totalPerturbation T N : ℝ) > (T.h^2 : ℝ) / 4) :
    T.spectralGap N < (spectralThreshold T.h : ℝ) := by
  -- From perturbation_upper_bound:
  -- λ₁(L_N) ≤ λ₁(L₀) + ⟨v₁, ΔL_N v₁⟩/⟨v₁, v₁⟩
  -- The perturbation term is negative (edges lose weight)
  -- ⟨v₁, ΔL_N v₁⟩ = -4 * neckEdgeCount * H_N
  -- When H_N > h²/4, this dominates λ₁(L₀) ≈ h²/4
  have h_bound := perturbation_upper_bound T N
  have h_pert := perturbation_term_bound T N
  -- spectralGap N ≤ h²/4 - 4 * neckEdgeCount * H_N / norm(v₁)²
  -- When H_N > h²/4 and neckEdgeCount ≥ 1, this is < h²/8
  sorry

/-- Definition of smallest eigenvalue -/
def IsSmallestEigenvalue {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (lam : ℝ) : Prop :=
  ∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = lam • v ∧
  ∀ μ v', v' ≠ 0 → M.mulVec v' = μ • v' → lam ≤ μ

/-- Weyl's inequality for eigenvalue perturbations -/
axiom weyl_inequality {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) : ∀ (eig_A eig_AB eig_B : ℝ),
    IsSmallestEigenvalue A eig_A →
    IsSmallestEigenvalue (A + B) eig_AB →
    IsSmallestEigenvalue B eig_B →
    eig_AB ≥ eig_A + eig_B

/-- Helper: smallest eigenvalue function -/
noncomputable def smallestEigenvalue {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : ℝ :=
  sorry  -- Would need Classical.choose with existence proof

/-- Lower bound: Small perturbation preserves gap -/
theorem weyl_lower_bound (T : TuringNeckTorus) (n : ℕ)
    (h_small : (totalPerturbation T n : ℝ) < (T.h^2 : ℝ) / 16) :
    T.spectralGap n ≥ (spectralThreshold T.h : ℝ) := by
  -- Use Weyl: λ₁(L_n) ≥ λ₁(L₀) + λ_min(ΔL_n)
  -- The perturbation matrix ΔL_n has negative entries -ε_k
  -- Its smallest eigenvalue ≥ -max|ε_k| = -H_n
  -- So λ₁(L_n) ≥ λ₁(L₀) - H_n ≥ h²/4 - h²/16 > h²/8
  
  -- Key ingredients:
  -- 1. λ₁(L₀) ≈ h²/4 (from spectralGapVariational)
  -- 2. λ_min(ΔL_n) ≥ -H_n (perturbation matrix has bounded norm)
  -- 3. When H_n < h²/16, we get λ₁(L_n) ≥ h²/4 - h²/16 = 3h²/16 > h²/8
  
  -- This requires properly instantiating Weyl's inequality with the right eigenvalues
  -- For now, we axiomatize the conclusion
  sorry

/-!
## Sturm's Theorem Approach for Primitive Recursiveness

The consultant suggested using Sturm's theorem to show that checking whether
all eigenvalues are above a threshold is primitive recursive.

Key idea: For a tridiagonal matrix (like our discrete Laplacian), Sturm's
theorem gives an algorithm to count eigenvalues in any interval using only:
- Polynomial evaluation
- Sign counting
- Basic arithmetic

This is primitive recursive because:
1. The characteristic polynomial has rational coefficients
2. Evaluating polynomials is primitive recursive
3. Counting sign changes is primitive recursive

For our spectral gap condition "λ₁ ≥ h²/8":
- Use Sturm sequence to count eigenvalues in [0, h²/8)
- Gap exists iff this count is 0
- This check is primitive recursive
-/

end Papers.P4_SpectralGeometry.Discrete