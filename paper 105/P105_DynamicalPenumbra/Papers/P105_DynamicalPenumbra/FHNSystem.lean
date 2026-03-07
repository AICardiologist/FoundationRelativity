/-
  FHNSystem.lean — Part II

  Algebraic representation of the FitzHugh-Nagumo model.

  The FHN system is a 2-variable polynomial reduction of Hodgkin-Huxley:
    dV/dt = V - V³/3 - W + I_ext
    dW/dt = ε(V + a - bW)

  All parameters are strictly positive rationals. The right-hand side
  is polynomial, hence Lipschitz on any compact set.

  Paper 105, Clinical Sub-Series Paper C,
  of the Constructive Reverse Mathematics Series
-/
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace P105

/-! ## FitzHugh-Nagumo Parameter Structure -/

/-- FitzHugh-Nagumo parameters. All strictly positive rationals. -/
structure FHNParams where
  ε : ℚ  -- time-scale separation (small, e.g., 0.08)
  a : ℚ  -- excitability parameter (e.g., 0.7)
  b : ℚ  -- recovery rate (e.g., 0.8)
  I : ℚ  -- external current (stimulus)
  hε : 0 < ε
  ha : 0 < a
  hb : 0 < b

/-! ## Standard Parameter Sets -/

/-- Standard FHN parameters (FitzHugh 1961). -/
def fhn_standard : FHNParams where
  ε := 8/100   -- 0.08
  a := 7/10    -- 0.7
  b := 8/10    -- 0.8
  I := 1/2     -- 0.5 (mild stimulus)
  hε := by norm_num
  ha := by norm_num
  hb := by norm_num

/-! ## Vector Field Components -/

/-- Voltage equation: dV/dt = V - V³/3 - W + I_ext -/
noncomputable def fhn_dV (p : FHNParams) (V W : ℝ) : ℝ :=
  V - V ^ 3 / 3 - W + (p.I : ℝ)

/-- Recovery equation: dW/dt = ε(V + a - bW) -/
def fhn_dW (p : FHNParams) (V W : ℝ) : ℝ :=
  (p.ε : ℝ) * (V + (p.a : ℝ) - (p.b : ℝ) * W)

/-! ## Jacobian Matrix Entries -/

/-- ∂(dV/dt)/∂V = 1 - V² -/
def J₁₁ (_p : FHNParams) (V : ℝ) : ℝ := 1 - V ^ 2

/-- ∂(dV/dt)/∂W = -1 -/
def J₁₂ (_p : FHNParams) : ℝ := -1

/-- ∂(dW/dt)/∂V = ε -/
def J₂₁ (p : FHNParams) : ℝ := (p.ε : ℝ)

/-- ∂(dW/dt)/∂W = -εb -/
def J₂₂ (p : FHNParams) : ℝ := -((p.ε : ℝ) * (p.b : ℝ))

/-- The Jacobian entries are correct partial derivatives of the vector field.
    Verification by ring. -/
theorem jacobian_dV_correct (p : FHNParams) (V W : ℝ) (h : ℝ) (hne : h ≠ 0) :
    (fhn_dV p (V + h) W - fhn_dV p V W) / h - J₁₁ p V =
    -(V * h + h ^ 2 / 3) := by
  simp only [fhn_dV, J₁₁]
  field_simp
  ring

theorem jacobian_dW_V_correct (p : FHNParams) (V W : ℝ) (h : ℝ) (hne : h ≠ 0) :
    (fhn_dW p (V + h) W - fhn_dW p V W) / h = J₂₁ p := by
  simp only [fhn_dW, J₂₁]
  field_simp
  ring

theorem jacobian_dW_W_correct (p : FHNParams) (V W : ℝ) (h : ℝ) (hne : h ≠ 0) :
    (fhn_dW p V (W + h) - fhn_dW p V W) / h = J₂₂ p := by
  simp only [fhn_dW, J₂₂]
  field_simp
  ring

/-! ## Nullclines -/

/-- V-nullcline: W = V - V³/3 + I (cubic) -/
noncomputable def v_nullcline (p : FHNParams) (V : ℝ) : ℝ := V - V ^ 3 / 3 + (p.I : ℝ)

/-- W-nullcline: W = (V + a) / b (linear) -/
noncomputable def w_nullcline (p : FHNParams) (V : ℝ) : ℝ :=
  (V + (p.a : ℝ)) / (p.b : ℝ)

/-- At equilibrium, V-nullcline equals W-nullcline. -/
theorem equilibrium_condition (p : FHNParams) (V₀ W₀ : ℝ)
    (hV : fhn_dV p V₀ W₀ = 0) (hW : fhn_dW p V₀ W₀ = 0)
    (hε_ne : (p.ε : ℝ) ≠ 0) :
    W₀ = v_nullcline p V₀ ∧ W₀ = w_nullcline p V₀ := by
  constructor
  · -- From dV/dt = 0: W₀ = V₀ - V₀³/3 + I
    simp only [fhn_dV] at hV
    simp only [v_nullcline]
    linarith
  · -- From dW/dt = 0: ε(V₀ + a - bW₀) = 0, ε ≠ 0 → W₀ = (V₀ + a)/b
    simp only [fhn_dW] at hW
    have : V₀ + (p.a : ℝ) - (p.b : ℝ) * W₀ = 0 := by
      have := mul_eq_zero.mp hW
      rcases this with h | h
      · exact absurd h hε_ne
      · linarith
    simp only [w_nullcline]
    have hb_ne : (p.b : ℝ) ≠ 0 := by
      exact_mod_cast p.hb.ne'
    field_simp
    linarith

end P105
