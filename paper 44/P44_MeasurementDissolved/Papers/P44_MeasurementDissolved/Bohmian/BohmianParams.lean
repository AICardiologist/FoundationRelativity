/-
  Paper 44: The Measurement Problem Dissolved
  Bohmian/BohmianParams.lean — Bohmian trajectory definitions

  In Bohmian mechanics, particles have definite positions guided by
  the wavefunction via dx/dt = v^B(x,t) where v^B = (ℏ/m) Im(∂ₓ log ψ).

  For a free Gaussian wave packet on ℝ, the guidance equation has an
  explicit solution. The key objects:
    - σ(t) = √(σ₀² + ℏ²t²/(4m²σ₀²))  — spreading width
    - x(t) = x₀ + v₀t + (x_init - x₀) · σ(t)/σ₀  — trajectory
    - v(t) = v₀ + (x_init - x₀) · ℏ²t/(4m²σ₀³σ(t))  — velocity

  ERRATUM: The velocity field coefficient is ℏ²/(4m²σ₀²), NOT ℏ/(2mσ₀²).
  This arises from the complex-valued width parameter σ_c² = σ₀² + iℏt/(2m);
  see §5.4 of the proof draft for the detailed calculation.
-/
import Papers.P44_MeasurementDissolved.Defs.BinaryEncoding
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section
namespace Papers.P44

open Real

-- ========================================================================
-- Physical parameters
-- ========================================================================

/-- Physical parameters for a Bohmian free Gaussian wave packet. -/
structure BohmianParams where
  σ₀ : ℝ     -- initial width (standard deviation)
  v₀ : ℝ     -- group velocity (momentum / mass)
  x₀ : ℝ     -- initial center of the wave packet
  m  : ℝ     -- particle mass
  ℏ  : ℝ     -- reduced Planck constant
  σ₀_pos : 0 < σ₀
  m_pos  : 0 < m
  ℏ_pos  : 0 < ℏ

-- ========================================================================
-- Spreading coefficient
-- ========================================================================

/-- The spreading coefficient: c = ℏ²/(4m²σ₀²).
    This is the rate at which the wave packet width grows.
    Corrected coefficient per §5.4 erratum (not ℏ/(2mσ₀²)). -/
noncomputable def spreadCoeff (p : BohmianParams) : ℝ :=
  p.ℏ ^ 2 / (4 * p.m ^ 2 * p.σ₀ ^ 2)

theorem spreadCoeff_pos (p : BohmianParams) : 0 < spreadCoeff p := by
  unfold spreadCoeff
  apply div_pos
  · exact sq_pos_of_pos p.ℏ_pos
  · apply mul_pos
    · apply mul_pos (by norm_num : (0:ℝ) < 4) (sq_pos_of_pos p.m_pos)
    · exact sq_pos_of_pos p.σ₀_pos

theorem spreadCoeff_nonneg (p : BohmianParams) : 0 ≤ spreadCoeff p :=
  le_of_lt (spreadCoeff_pos p)

-- ========================================================================
-- Spreading width σ(t)
-- ========================================================================

/-- The spreading width: σ(t) = √(σ₀² + c·t²)
    where c = ℏ²/(4m²σ₀²). At t = 0, σ(0) = σ₀. -/
noncomputable def sigma_t (p : BohmianParams) (t : ℝ) : ℝ :=
  Real.sqrt (p.σ₀ ^ 2 + spreadCoeff p * t ^ 2)

/-- The argument of sigma_t is positive. -/
theorem sigma_t_arg_pos (p : BohmianParams) (t : ℝ) :
    0 < p.σ₀ ^ 2 + spreadCoeff p * t ^ 2 := by
  have h1 : 0 < p.σ₀ ^ 2 := sq_pos_of_pos p.σ₀_pos
  have h2 : 0 ≤ spreadCoeff p * t ^ 2 := mul_nonneg (spreadCoeff_nonneg p) (sq_nonneg t)
  linarith

/-- σ(t) > 0 for all t. -/
theorem sigma_t_pos (p : BohmianParams) (t : ℝ) : 0 < sigma_t p t :=
  Real.sqrt_pos_of_pos (sigma_t_arg_pos p t)

/-- σ(t) ≠ 0 for all t. -/
theorem sigma_t_ne_zero (p : BohmianParams) (t : ℝ) : sigma_t p t ≠ 0 :=
  ne_of_gt (sigma_t_pos p t)

/-- σ₀ ≠ 0. -/
theorem sigma0_ne_zero (p : BohmianParams) : p.σ₀ ≠ 0 :=
  ne_of_gt p.σ₀_pos

/-- σ(t) ≥ σ₀ for all t. -/
theorem sigma_t_ge_sigma0 (p : BohmianParams) (t : ℝ) :
    p.σ₀ ≤ sigma_t p t := by
  unfold sigma_t
  rw [← Real.sqrt_sq (le_of_lt p.σ₀_pos)]
  apply Real.sqrt_le_sqrt
  have h1 : Real.sqrt (p.σ₀ ^ 2) ^ 2 = p.σ₀ ^ 2 := by
    rw [Real.sq_sqrt (sq_nonneg p.σ₀)]
  have h2 : 0 ≤ spreadCoeff p * t ^ 2 := mul_nonneg (spreadCoeff_nonneg p) (sq_nonneg t)
  nlinarith

/-- σ(0) = σ₀. -/
theorem sigma_t_zero (p : BohmianParams) : sigma_t p 0 = p.σ₀ := by
  simp [sigma_t, spreadCoeff]
  exact Real.sqrt_sq (le_of_lt p.σ₀_pos)

-- ========================================================================
-- Bohmian trajectory
-- ========================================================================

/-- The explicit Bohmian trajectory:
    x(t) = x₀ + v₀·t + (x_init - x₀) · σ(t)/σ₀

    This is the exact solution of the guidance equation
    dx/dt = v^B(x,t) for a free Gaussian wave packet. -/
noncomputable def bohmian_trajectory (p : BohmianParams) (x_init : ℝ) (t : ℝ) : ℝ :=
  p.x₀ + p.v₀ * t + (x_init - p.x₀) * sigma_t p t / p.σ₀

/-- At t = 0, the trajectory returns the initial position. -/
theorem bohmian_trajectory_zero (p : BohmianParams) (x_init : ℝ) :
    bohmian_trajectory p x_init 0 = x_init := by
  unfold bohmian_trajectory
  rw [sigma_t_zero]
  have h : p.σ₀ ≠ 0 := sigma0_ne_zero p
  field_simp
  ring

-- ========================================================================
-- Trajectory velocity (from explicit differentiation)
-- ========================================================================

/-- The instantaneous velocity along the trajectory:
    dx/dt = v₀ + (x_init - x₀) · c·t / (σ₀ · σ(t))

    Derived by differentiating the trajectory formula.
    This equals the Bohmian velocity field v^B evaluated at (x(t), t). -/
noncomputable def trajectory_velocity (p : BohmianParams) (x_init : ℝ) (t : ℝ) : ℝ :=
  p.v₀ + (x_init - p.x₀) * spreadCoeff p * t / (p.σ₀ * sigma_t p t)

-- ========================================================================
-- Bohmian velocity field
-- ========================================================================

/-- The Bohmian velocity field:
    v^B(x, t) = v₀ + c·t/σ(t)² · (x - x₀ - v₀·t)

    where c = ℏ²/(4m²σ₀²). This is derived from v^B = (ℏ/m)Im(∂ₓ log ψ)
    for a Gaussian wave packet with complex width parameter. -/
noncomputable def bohmian_velocity (p : BohmianParams) (x t : ℝ) : ℝ :=
  p.v₀ + spreadCoeff p * t / (sigma_t p t) ^ 2 * (x - p.x₀ - p.v₀ * t)

-- ========================================================================
-- Discretized velocity sequence (for BMC application)
-- ========================================================================

/-- The velocity at integer times: v_n = trajectory_velocity(p, x_init, n).
    This is the sequence whose convergence is equivalent to BMC/LPO. -/
noncomputable def velocity_seq (p : BohmianParams) (x_init : ℝ) (n : ℕ) : ℝ :=
  trajectory_velocity p x_init (n : ℝ)

-- ========================================================================
-- Encoding binary sequences into initial positions
-- ========================================================================

/-- Encode a binary sequence f into an initial position:
    x_init(f) = x₀ + σ₀ · r_f
    where r_f = binaryEncoding(f) ∈ [0, 1]. -/
noncomputable def bohmianEncoding (p : BohmianParams) (f : ℕ → Bool) : ℝ :=
  p.x₀ + p.σ₀ * binaryEncoding f

/-- The encoding equals x₀ iff all entries are false. -/
theorem bohmianEncoding_eq_x0_iff (p : BohmianParams) (f : ℕ → Bool) :
    bohmianEncoding p f = p.x₀ ↔ ∀ n, f n = false := by
  simp only [bohmianEncoding]
  constructor
  · intro h
    have : p.σ₀ * binaryEncoding f = 0 := by linarith
    have hne : p.σ₀ ≠ 0 := sigma0_ne_zero p
    have := (mul_eq_zero.mp this).resolve_left hne
    exact (binaryEncoding_eq_zero_iff f).mp this
  · intro h
    rw [(binaryEncoding_eq_zero_iff f).mpr h]
    ring

end Papers.P44
end
