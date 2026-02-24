/-
Papers/P17_BHEntropy/Basic.lean
Core definitions for Paper 17: Axiom Calibration of Black Hole Entropy.

Defines the LPO omniscience principle, BMC, half-integer type for spin labels,
Casimir values, area eigenvalues, spin configurations, and admissibility.

Key insight: Half-integers are represented as natural numbers storing 2j.
This avoids rationals entirely for the combinatorial core. All arithmetic
on spin labels reduces to natural number arithmetic on the `twice` field.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Rat.Cast.Defs

universe u

namespace Papers.P17

open Real

-- ========================================================================
-- Logical principles
-- ========================================================================

/-- Limited Principle of Omniscience.
    Equivalent to: every bounded monotone sequence of reals converges
    (Bridges–Vîță 2006). -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Bounded Monotone Convergence: every bounded non-decreasing sequence
    of reals has a limit. Equivalent to LPO over BISH [Bridges–Vîță 2006]. -/
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

-- ========================================================================
-- Half-integer type (spin labels)
-- ========================================================================

/-- Positive half-integer type for spin network labels.
    Stores 2j as a natural number, so j = twice/2.
    The constraint `twice ≥ 1` ensures j ≥ 1/2. -/
structure HalfInt where
  twice : ℕ
  pos : twice ≥ 1
  deriving DecidableEq

instance : LE HalfInt where
  le a b := a.twice ≤ b.twice

instance : LT HalfInt where
  lt a b := a.twice < b.twice

instance (a b : HalfInt) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.twice ≤ b.twice))

instance (a b : HalfInt) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.twice < b.twice))

/-- The minimal half-integer: j = 1/2 (twice = 1). -/
def HalfInt.min : HalfInt := ⟨1, le_refl 1⟩

-- ========================================================================
-- Casimir value
-- ========================================================================

/-- Casimir square: j(j+1) = k(k+2)/4 where k = twice.
    Returns a rational to keep exact arithmetic for finiteness proofs.
    For j with twice = k: casimir_sq = (k/2)(k/2 + 1) = k(k+2)/4. -/
def casimir_sq (j : HalfInt) : ℚ :=
  (j.twice : ℚ) * (j.twice + 2) / 4

/-- Casimir square root as a real number: √(j(j+1)). -/
noncomputable def casimir (j : HalfInt) : ℝ :=
  Real.sqrt (casimir_sq j : ℝ)

-- ========================================================================
-- Area eigenvalue
-- ========================================================================

/-- Area eigenvalue: a(j) = 8πγ√(j(j+1)).
    This is the area contribution of a single puncture with spin j. -/
noncomputable def area_eigenvalue (gamma : ℝ) (j : HalfInt) : ℝ :=
  8 * Real.pi * gamma * casimir j

/-- Area gap: the minimum area eigenvalue, at j = 1/2.
    a_min = 8πγ√(3/4) = 4πγ√3. -/
noncomputable def area_gap (gamma : ℝ) : ℝ :=
  area_eigenvalue gamma HalfInt.min

-- ========================================================================
-- Spin configuration
-- ========================================================================

/-- A spin configuration: a finite list of positive half-integers.
    Each entry represents a puncture of the horizon by a spin network edge. -/
def SpinConfig := List HalfInt

instance : DecidableEq SpinConfig := inferInstanceAs (DecidableEq (List HalfInt))

/-- Total area of a spin configuration. -/
noncomputable def total_area (gamma : ℝ) (config : SpinConfig) : ℝ :=
  (config.map (area_eigenvalue gamma)).sum

/-- A configuration is admissible if its total area is within δ of the target A. -/
noncomputable def admissible (A gamma delta : ℝ) (config : SpinConfig) : Prop :=
  |total_area gamma config - A| ≤ delta

-- ========================================================================
-- Upper bound on configuration size (for finiteness)
-- ========================================================================

/-- Upper bound on the number of punctures in an admissible configuration.
    Each puncture contributes at least area_gap to the total, so
    the number of punctures ≤ ⌈(A + δ) / area_gap⌉. -/
noncomputable def N_max (A gamma delta : ℝ) : ℕ :=
  Nat.ceil ((A + delta) / area_gap gamma)

/-- Upper bound on twice-field of any spin in an admissible configuration.
    Each spin j has area_eigenvalue ≤ A + δ, which bounds j.twice.
    We use a simple but loose bound: j.twice ≤ ⌈(A + δ) / (4πγ)⌉ + 1.
    (Since area_eigenvalue gamma j ≥ 8πγ · j.twice/2 for large j.) -/
noncomputable def j_max_twice (A gamma delta : ℝ) : ℕ :=
  Nat.ceil ((A + delta) / (4 * Real.pi * gamma)) + 1

end Papers.P17
