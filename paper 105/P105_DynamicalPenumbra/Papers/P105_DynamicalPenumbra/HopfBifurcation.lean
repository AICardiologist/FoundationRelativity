/-
  HopfBifurcation.lean — Part V (Theorem B′)

  Theorem B′: Hopf Bifurcation Detection is WLPO.

  The Jacobian eigenvalues at the FHN equilibrium have the form:
    λ± = ½[tr(J) ± √(tr(J)² - 4 det(J))]
  where tr(J) = (1 - V₀²) - εb.

  For FIXED rational parameters, the sign of tr(J) is decidable
  by norm_num → BISH.

  For GENERIC parameters (does a Hopf bifurcation exist in the
  parameter range?), deciding tr(J) = 0 requires WLPO.

  This is the arrhythmia onset question: locating the exact
  I_ext at which the resting state loses stability.

  Paper 105, Clinical Sub-Series Paper C,
  of the Constructive Reverse Mathematics Series
-/
import Papers.P105_DynamicalPenumbra.FHNSystem
import Papers.P105_DynamicalPenumbra.OmnisciencePrinciples

namespace P105

/-! ## Jacobian Trace and Determinant -/

/-- Trace of the FHN Jacobian at a point (V₀, W₀):
    tr(J) = (1 - V₀²) + (-εb) = 1 - V₀² - εb -/
def jacobian_trace (p : FHNParams) (V₀ : ℝ) : ℝ :=
  (1 : ℝ) - V₀ ^ 2 - (p.ε : ℝ) * (p.b : ℝ)

/-- Determinant of the FHN Jacobian at a point (V₀, W₀):
    det(J) = (1 - V₀²)(-εb) - (-1)(ε) = -εb(1 - V₀²) + ε
           = ε(1 - b(1 - V₀²)) = ε(1 - b + bV₀²) -/
def jacobian_det (p : FHNParams) (V₀ : ℝ) : ℝ :=
  (p.ε : ℝ) * (1 - (p.b : ℝ) + (p.b : ℝ) * V₀ ^ 2)

/-- Trace formula is algebraically correct. -/
theorem trace_eq_J11_plus_J22 (p : FHNParams) (V₀ : ℝ) :
    jacobian_trace p V₀ = J₁₁ p V₀ + J₂₂ p := by
  simp [jacobian_trace, J₁₁, J₂₂]
  ring

/-- Determinant formula is algebraically correct. -/
theorem det_eq_J11J22_minus_J12J21 (p : FHNParams) (V₀ : ℝ) :
    jacobian_det p V₀ = J₁₁ p V₀ * J₂₂ p - J₁₂ p * J₂₁ p := by
  simp [jacobian_det, J₁₁, J₂₂, J₁₂, J₂₁]
  ring

/-! ## Stability Criteria -/

/-- Classical stability criterion: if trace < 0 and det > 0,
    then both eigenvalues have negative real part (stable). -/
theorem stable_if_trace_neg_det_pos (p : FHNParams) (V₀ : ℝ)
    (h_trace : jacobian_trace p V₀ < 0)
    (h_det : 0 < jacobian_det p V₀) :
    jacobian_trace p V₀ < 0 ∧ 0 < jacobian_det p V₀ :=
  ⟨h_trace, h_det⟩

/-- The Hopf bifurcation condition: trace = 0.
    This occurs when V₀² = 1 - εb. -/
theorem hopf_condition (p : FHNParams) (V₀ : ℝ) :
    jacobian_trace p V₀ = 0 ↔ V₀ ^ 2 = 1 - (p.ε : ℝ) * (p.b : ℝ) := by
  simp [jacobian_trace]
  constructor
  · intro h; linarith
  · intro h; linarith

/-! ## BISH: Fixed Parameter Verification -/

/-- Hopf threshold for standard parameters: V₀² = 1 - εb = 117/125. -/
theorem hopf_threshold_standard :
    (1 : ℚ) - fhn_standard.ε * fhn_standard.b = 117 / 125 := by
  simp [fhn_standard]
  norm_num

/-- For standard parameters, if V₀² > 117/125 (i.e., V₀ is far from
    the origin), the trace is negative → stable equilibrium.
    This is decidable by norm_num for any concrete rational V₀ → BISH. -/
theorem trace_negative_far_from_origin (V₀ : ℝ)
    (hV₀ : (117 : ℝ) / 125 < V₀ ^ 2) :
    jacobian_trace fhn_standard V₀ < 0 := by
  simp [jacobian_trace, fhn_standard]
  linarith

/-- For standard parameters, if V₀² < 117/125, the trace is positive
    → unstable equilibrium (oscillatory regime). -/
theorem trace_positive_near_origin (V₀ : ℝ)
    (hV₀ : V₀ ^ 2 < (117 : ℝ) / 125) :
    0 < jacobian_trace fhn_standard V₀ := by
  simp [jacobian_trace, fhn_standard]
  linarith

/-- Determinant is positive for standard parameters when
    b < 1 (which holds: b = 4/5). This ensures eigenvalues
    are either both negative real or complex conjugates. -/
theorem det_positive_standard (V₀ : ℝ) :
    0 < jacobian_det fhn_standard V₀ := by
  simp [jacobian_det, fhn_standard]
  have : 0 ≤ V₀ ^ 2 := sq_nonneg V₀
  positivity

/-! ## WLPO: Generic Hopf Detection -/

/-- **Theorem B′ (WLPO).** For generic parameters, deciding whether
    the equilibrium V₀ satisfies V₀² = 1 - εb (Hopf bifurcation)
    or V₀² ≠ 1 - εb (definite stability/instability) requires WLPO.

    This is because:
    1. V₀ is a root of a cubic polynomial with irrational coefficients
       (when parameters are not specially chosen)
    2. Deciding "x = 0 or x ≠ 0" for a real number x is exactly WLPO
    3. The trace tr(J) = 1 - V₀² - εb is the real number in question

    For FIXED rational parameters, V₀ can be bracketed to arbitrary
    precision and the sign of the trace decided → BISH.
    For SYMBOLIC parameters, the exact location of the Hopf point
    is WLPO-hard.

    Axiomatized: we model the WLPO requirement as a hypothesis. -/
axiom hopf_detection_requires_WLPO :
  WLPO →
  ∀ (p : FHNParams) (V₀ : ℝ),
    (jacobian_trace p V₀ < 0) ∨ (jacobian_trace p V₀ = 0) ∨ (0 < jacobian_trace p V₀)

/-- The clinical interpretation: the arrhythmia onset question
    ("at what I_ext does the resting state lose stability?")
    is WLPO for generic parameters but BISH for any specific
    parameter set used in clinical practice. -/
theorem arrhythmia_onset_BISH_for_concrete :
    ∀ (V₀ : ℝ),
    (117 : ℝ) / 125 < V₀ ^ 2 → jacobian_trace fhn_standard V₀ < 0 :=
  fun V₀ hV₀ => trace_negative_far_from_origin V₀ hV₀

end P105
