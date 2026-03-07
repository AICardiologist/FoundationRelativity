/-
  ReLUBypass.lean — Part III

  The ReLU Bypass Theorem: ReLU networks with rational weights
  preserve ℚ under the forward pass.

  Key insight: max(0, x) is decidable over ℚ, and ℚ is closed under
  addition and multiplication. Therefore the entire forward pass of a
  ReLU network with rational weights maps ℚ^n → ℚ, remaining strictly
  within BISH.

  Paper 104 of the Constructive Reverse Mathematics Series
-/
import Mathlib.Tactic
import Mathlib.Data.Rat.Lemmas

namespace P104

/-! ## ReLU over ℚ -/

/-- ReLU activation on ℚ: max(0, x), computable via decidable ordering -/
def reluQ (x : ℚ) : ℚ := if 0 ≤ x then x else 0

/-- ReLU of a rational is rational (trivially, since the type is ℚ → ℚ) -/
theorem relu_rational_closed (x : ℚ) : ∃ (q : ℚ), reluQ x = q :=
  ⟨reluQ x, rfl⟩

/-- ReLU is non-negative -/
theorem relu_nonneg (x : ℚ) : 0 ≤ reluQ x := by
  unfold reluQ; split_ifs with h
  · exact h
  · exact le_refl 0

/-- ReLU preserves non-negative inputs -/
theorem relu_of_nonneg {x : ℚ} (hx : 0 ≤ x) : reluQ x = x := by
  unfold reluQ; simp [hx]

/-- ReLU of negative input is zero -/
theorem relu_of_neg {x : ℚ} (hx : x < 0) : reluQ x = 0 := by
  unfold reluQ; simp [not_le.mpr hx]

/-- Comparison of ReLU output with rational threshold is decidable -/
theorem relu_threshold_dec (x τ : ℚ) : reluQ x ≥ τ ∨ ¬(reluQ x ≥ τ) :=
  if h : reluQ x ≥ τ then .inl h else .inr h

/-! ## Single Layer: Affine Map + ReLU -/

/-- An affine map ℚ^n → ℚ given by weights w and bias b -/
def affineQ {n : ℕ} (w : Fin n → ℚ) (b : ℚ) (x : Fin n → ℚ) : ℚ :=
  (Finset.univ.sum fun i => w i * x i) + b

/-- Affine map preserves ℚ (closure under +, ×, finite sums) -/
theorem affine_rational_closed {n : ℕ} (w : Fin n → ℚ) (b : ℚ) (x : Fin n → ℚ) :
    ∃ (q : ℚ), affineQ w b x = q :=
  ⟨affineQ w b x, rfl⟩

/-- Single neuron: affine + ReLU, ℚ → ℚ -/
def reluNeuron {n : ℕ} (w : Fin n → ℚ) (b : ℚ) (x : Fin n → ℚ) : ℚ :=
  reluQ (affineQ w b x)

/-- Single neuron output is rational -/
theorem neuron_rational_closed {n : ℕ} (w : Fin n → ℚ) (b : ℚ) (x : Fin n → ℚ) :
    ∃ (q : ℚ), reluNeuron w b x = q :=
  ⟨reluNeuron w b x, rfl⟩

/-! ## Layer Composition -/

/-- A single ReLU layer: m neurons, each with n inputs -/
def reluLayer {n m : ℕ} (W : Fin m → Fin n → ℚ) (bias : Fin m → ℚ)
    (x : Fin n → ℚ) : Fin m → ℚ :=
  fun j => reluNeuron (W j) (bias j) x

/-- A ReLU layer maps ℚ^n → ℚ^m -/
theorem layer_rational_closed {n m : ℕ} (W : Fin m → Fin n → ℚ) (bias : Fin m → ℚ)
    (x : Fin n → ℚ) (j : Fin m) :
    ∃ (q : ℚ), reluLayer W bias x j = q :=
  ⟨reluLayer W bias x j, rfl⟩

/-- Two-layer composition: ℚ^n → ℚ^m → ℚ^k, all rational -/
def twoLayerReLU {n m k : ℕ}
    (W₁ : Fin m → Fin n → ℚ) (b₁ : Fin m → ℚ)
    (W₂ : Fin k → Fin m → ℚ) (b₂ : Fin k → ℚ)
    (x : Fin n → ℚ) : Fin k → ℚ :=
  reluLayer W₂ b₂ (reluLayer W₁ b₁ x)

/-- Two-layer ReLU network output is rational -/
theorem two_layer_rational {n m k : ℕ}
    (W₁ : Fin m → Fin n → ℚ) (b₁ : Fin m → ℚ)
    (W₂ : Fin k → Fin m → ℚ) (b₂ : Fin k → ℚ)
    (x : Fin n → ℚ) (j : Fin k) :
    ∃ (q : ℚ), twoLayerReLU W₁ b₁ W₂ b₂ x j = q :=
  ⟨twoLayerReLU W₁ b₁ W₂ b₂ x j, rfl⟩

/-! ## Threshold Decision: BISH -/

/-- Clinical alert decision for ReLU network: compare output logit to
    rational threshold. Decidable over ℚ without any omniscience principle. -/
theorem relu_alert_dec {n m : ℕ}
    (W₁ : Fin m → Fin n → ℚ) (b₁ : Fin m → ℚ)
    (w_out : Fin m → ℚ) (b_out τ : ℚ)
    (x : Fin n → ℚ) :
    affineQ w_out b_out (reluLayer W₁ b₁ x) ≥ τ
    ∨ ¬(affineQ w_out b_out (reluLayer W₁ b₁ x) ≥ τ) :=
  if h : affineQ w_out b_out (reluLayer W₁ b₁ x) ≥ τ then .inl h else .inr h

/-! ## The ReLU Bypass Theorem (Theorem B) -/

/-- Theorem B: The ReLU Bypass.
    For any ReLU network with rational weights and rational input,
    the output is rational and comparison with a rational threshold
    is decidable without any omniscience principle. -/
theorem relu_bypass {n m : ℕ}
    (W : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (w_out : Fin m → ℚ) (b_out τ : ℚ)
    (x : Fin n → ℚ) :
    (∃ q : ℚ, affineQ w_out b_out (reluLayer W b x) = q)
    ∧ (affineQ w_out b_out (reluLayer W b x) ≥ τ
       ∨ ¬(affineQ w_out b_out (reluLayer W b x) ≥ τ)) :=
  ⟨⟨_, rfl⟩, if h : affineQ w_out b_out (reluLayer W b x) ≥ τ then .inl h else .inr h⟩

end P104
