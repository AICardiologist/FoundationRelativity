/-
  ConstructiveRegularization.lean — Part VII

  Constructive Regularization: the grid-factorization / VC-dimension bridge.

  A grid-factored classifier factors through a discrete quantization
  and cannot shatter sub-resolution noise.  A continuous model maps to
  the dense continuum and possesses infinite capacity to separate noise
  points.

  CRITICAL DISTINCTION (reviewer correction, Round 4):
  "Grid-factored" (factors through quantize) ≠ "BISH-computable"
  (all operations in ℚ).  XGBoost is BISH-computable (Theorem A) but
  NOT grid-factored: it can draw rational decision boundaries at
  arbitrary precision within a single grid cell.  BISH-computability
  alone does not restrict shattering capacity; grid-factorization does.

  Theorem E1 (grid_factored_cannot_shatter_noise):
    If every classifier in H factors through the quantization grid,
    then H cannot shatter any set containing two distinct points with
    equal grid coordinates.

  Theorem E2 (continuum_separates_noise):
    A continuous model mapping to ℝ can always find a threshold
    separating two noise points — the infinite capacity that
    finances overfitting.

  Paper 104 of the Constructive Reverse Mathematics Series
-/
import Mathlib.Tactic

namespace P104

/-! ## Grid-Factored Classifiers and Shattering -/

/-- A classifier is grid-factored (relative to a quantization)
    if it assigns equal labels to points with equal grid coordinates.
    This is the formal content of factoring through the discrete grid.

    IMPORTANT: This is strictly stronger than BISH-computability.
    A BISH-computable model (e.g., XGBoost with rational splits) may
    distinguish points within the same grid cell.  Grid-factorization
    requires that the classifier's output depend ONLY on quantize(x). -/
def IsGridFactored {X : Type} (quantize : X → ℤ) (c : X → Bool) : Prop :=
  ∀ x y, quantize x = quantize y → c x = c y

/-- A hypothesis class H shatters a set S if it can realize
    every possible Boolean labeling of S.
    This is the foundation of VC-dimension and overfitting theory. -/
def Shatters {X : Type} (H : Set (X → Bool)) (S : Set X) : Prop :=
  ∀ (labeling : S → Bool), ∃ c ∈ H, ∀ (s : S), c s.val = labeling s

/-! ## Theorem E1: Constructive Regularization -/

/-- Theorem E1 (Constructive Regularization):
    A hypothesis class of grid-factored classifiers cannot shatter any
    set containing two distinct points with the same grid coordinate.

    Grid-factorization acts as a strict structural regularizer,
    mathematically bounding hypothesis capacity on Q-bounded data.

    Note: This does NOT apply to all BISH-computable models.
    XGBoost is BISH-computable but not grid-factored, and CAN
    shatter rational points at arbitrary precision. -/
theorem grid_factored_cannot_shatter_noise {X : Type} [DecidableEq X]
    (quantize : X → ℤ)
    (H : Set (X → Bool))
    (h_grid : ∀ c ∈ H, IsGridFactored quantize c)
    (S : Set X) (x y : X) (hx : x ∈ S) (hy : y ∈ S)
    (h_neq : x ≠ y) (h_noise : quantize x = quantize y) :
    ¬ Shatters H S := by
  intro h_shatters
  -- Pick a labeling separating the noisy pair: true at x, false elsewhere
  obtain ⟨c, hc, h_eq⟩ := h_shatters (fun ⟨z, _⟩ => decide (z = x))
  -- Grid-factored constraint: c must agree on grid-equivalent points
  have c_eq : c x = c y := h_grid c hc x y h_noise
  -- But the labeling forces c x = true and c y = false
  have hx' := h_eq ⟨x, hx⟩
  have hy' := h_eq ⟨y, hy⟩
  simp [Ne.symm h_neq] at hx' hy'
  -- hx' : c x = true,  hy' : c y = false,  c_eq : c x = c y
  rw [hx', hy'] at c_eq
  exact absurd c_eq Bool.noConfusion

/-! ## Theorem E2: Archimedean Overfitting -/

/-- Theorem E2 (Archimedean Overfitting):
    A continuous model mapping to ℝ can always find a threshold
    separating sub-resolution noise points (density of ℝ).
    This is the infinite topological capacity that finances overfitting
    on Q-bounded data. -/
theorem continuum_separates_noise {X : Type}
    (f : X → ℝ) (x y : X) (h_diff : f x < f y) :
    ∃ τ : ℝ, f x < τ ∧ τ < f y :=
  ⟨(f x + f y) / 2, by linarith, by linarith⟩

end P104
