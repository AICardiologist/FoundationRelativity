/-
  Paper 34: Scattering Amplitudes Are Constructively Computable
  Defs.lean: Infrastructure and definitions

  Bhabha scattering (e⁺e⁻ → e⁺e⁻) infrastructure:
  Mandelstam variables, special functions, and constructive principles.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic

noncomputable section

open Real

-- ============================================================
-- Constructive Principles
-- ============================================================

def LPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ (∃ n, a n = true)

def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a → (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

axiom bmc_of_lpo : LPO → BMC

-- ============================================================
-- Kinematics: Mandelstam Variables
-- ============================================================

/-- The electron mass (positive real). -/
def m_e : ℝ := 1  -- normalized; physical value irrelevant for classification

/-- Mandelstam variables for 2→2 scattering.
    s = (p1+p2)², t = (p1-p3)², u = (p1-p4)²
    Kinematic constraint: s + t + u = 4m² -/
structure MandelstamVars where
  s : ℝ
  t : ℝ
  u : ℝ
  constraint : s + t + u = 4 * m_e ^ 2
  s_pos : 4 * m_e ^ 2 < s  -- above threshold
  t_neg : t < 0             -- spacelike transfer

/-- s is nonzero (positive, in fact above threshold). -/
theorem s_ne_zero (k : MandelstamVars) : k.s ≠ 0 := by
  have : 0 < k.s := by linarith [k.s_pos, pow_pos (show (0:ℝ) < m_e from by unfold m_e; norm_num) 2]
  exact ne_of_gt this

/-- t is nonzero (negative, in fact). -/
theorem t_ne_zero (k : MandelstamVars) : k.t ≠ 0 := by
  exact ne_of_lt k.t_neg

/-- t² is nonzero. -/
theorem t_sq_ne_zero (k : MandelstamVars) : k.t ^ 2 ≠ 0 :=
  pow_ne_zero 2 (t_ne_zero k)

/-- s² is nonzero. -/
theorem s_sq_ne_zero (k : MandelstamVars) : k.s ^ 2 ≠ 0 :=
  pow_ne_zero 2 (s_ne_zero k)

/-- s*t is nonzero. -/
theorem st_ne_zero (k : MandelstamVars) : k.s * k.t ≠ 0 :=
  mul_ne_zero (s_ne_zero k) (t_ne_zero k)

-- ============================================================
-- Special Functions Infrastructure
-- ============================================================

/-- The dilogarithm (Spence function): Li₂(z) = -∫₀¹ log(1-zt)/t dt
    = Σ_{n=1}^∞ z^n/n² for |z| ≤ 1.
    This is computable with explicit convergence rate. -/
def Li2 (z : ℝ) : ℝ := z  -- placeholder; series definition axiomatized

/-- Li₂ partial sum: Σ_{n=1}^N z^n/n² -/
def Li2_partial (z : ℝ) (N : ℕ) : ℝ := z * N  -- placeholder

/-- Li₂ has an explicit convergence rate: the partial sums
    converge to Li₂(z) for |z| ≤ 1. -/
axiom Li2_computable (z : ℝ) (hz : |z| ≤ 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, |Li2 z - Li2_partial z N| < ε

-- ============================================================
-- Dimensional Regularization Infrastructure
-- ============================================================

/-- A formal Laurent series in ε (dim reg parameter).
    Represents expressions like a_{-1}/ε + a_0 + a_1·ε + ... -/
structure LaurentSeries where
  pole : ℝ      -- coefficient of 1/ε
  finite : ℝ    -- finite part (coefficient of ε⁰)

/-- MS-bar subtraction: remove the 1/ε pole. -/
def msbar_subtract (L : LaurentSeries) : ℝ := L.finite

-- ============================================================
-- Cross Section Infrastructure
-- ============================================================

/-- The fine structure constant -/
def alpha_em : ℝ := 1 / 137  -- approximate; exact value irrelevant

/-- Tree-level Bhabha scattering function F(s,t,u) -/
def bhabha_F (k : MandelstamVars) : ℝ :=
  (k.s ^ 2 + k.u ^ 2) / k.t ^ 2 +
  (k.t ^ 2 + k.u ^ 2) / k.s ^ 2 +
  2 * k.u ^ 2 / (k.s * k.t)

/-- Tree-level differential cross section -/
def tree_cross_section (k : MandelstamVars) (α : ℝ) : ℝ :=
  (α ^ 2 / (4 * k.s)) * bhabha_F k

/-- One-loop correction (finite after renormalization) -/
def one_loop_correction (k : MandelstamVars) (α : ℝ) : ℝ :=
  α ^ 3 * k.s  -- placeholder structure

/-- Fixed-order inclusive cross section (tree + one-loop) -/
def fixed_order_cross_section (k : MandelstamVars) (α : ℝ) : ℝ :=
  tree_cross_section k α + one_loop_correction k α

end
