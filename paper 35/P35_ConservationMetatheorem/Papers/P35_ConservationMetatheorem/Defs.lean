/-
  Paper 35: The Conservation Metatheorem
  Defs.lean: Infrastructure and definitions

  Core types for classifying physical predictions:
  ComputableFun, FiniteComposition, CRMCategory, CalibratedResult.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

noncomputable section

open Real

-- ============================================================
-- Constructive Principles
-- ============================================================

def LPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ (∃ n, a n = true)

def WLPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ ¬(∀ n, a n = false)

def LLPO : Prop :=
  ∀ (a : ℕ → Bool),
    (∀ n, a (2 * n) = false) ∨ (∀ n, a (2 * n + 1) = false)

def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a → (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

/-- Cauchy completeness without computable modulus. -/
def CauchyComplete : Prop :=
  ∀ (a : ℕ → ℝ),
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → |a n - a m| < ε) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

/-- Bounded supremum existence. -/
def BoundedSupExists : Prop :=
  ∀ (S : ℕ → ℝ) (M : ℝ),
    (∀ n, S n ≤ M) →
    ∃ s : ℝ, (∀ n, S n ≤ s) ∧
      ∀ ε : ℝ, 0 < ε → ∃ n, s - ε < S n

-- Standard implications
axiom bmc_of_lpo : LPO → BMC
axiom wlpo_of_lpo : LPO → WLPO
axiom llpo_of_wlpo : WLPO → LLPO

-- ============================================================
-- CRM Classification Types
-- ============================================================

/-- The CRM classification categories. -/
inductive CRMCategory where
  | BISH : CRMCategory    -- finitary computation
  | LLPO : CRMCategory    -- disjunction / sign decision
  | WLPO : CRMCategory    -- threshold / equality decision
  | LPO  : CRMCategory    -- completed limit without modulus
  deriving DecidableEq, BEq, Repr

/-- The constructive hierarchy is linearly ordered. -/
def CRMCategory.le : CRMCategory → CRMCategory → Prop
  | .BISH, _ => True
  | .LLPO, .BISH => False
  | .LLPO, _ => True
  | .WLPO, .BISH => False
  | .WLPO, .LLPO => False
  | .WLPO, _ => True
  | .LPO, .LPO => True
  | .LPO, _ => False

/-- A calibrated result from a paper in the programme. -/
structure CalibratedResult where
  paper : ℕ
  description : String
  category : CRMCategory
  deriving DecidableEq, BEq, Repr

-- ============================================================
-- LPO Mechanisms
-- ============================================================

/-- The three equivalent mechanisms that produce LPO. -/
inductive LPOMechanism where
  | BMC             : LPOMechanism  -- bounded monotone convergence
  | CauchyNoModulus : LPOMechanism  -- Cauchy completeness without rate
  | SupExists       : LPOMechanism  -- supremum of bounded set
  deriving DecidableEq, BEq, Repr

-- ============================================================
-- Computable Functions (simplified framework)
-- ============================================================

/-- A computable function: one that produces approximations at
    any desired precision. Simplified for this classification paper. -/
structure ComputableFun where
  f : ℝ → ℝ
  approx_exists : ∀ (x : ℝ), ∀ (ε : ℝ), 0 < ε → ∃ (q : ℝ), |f x - q| < ε

/-- A finite composition of computable functions. -/
inductive FiniteComposition where
  | base : ComputableFun → FiniteComposition
  | comp : FiniteComposition → FiniteComposition → FiniteComposition

/-- Evaluate a finite composition. -/
def FiniteComposition.eval : FiniteComposition → ℝ → ℝ
  | .base cf => cf.f
  | .comp fc1 fc2 => fun x => fc1.eval (fc2.eval x)

-- ============================================================
-- Convergence with and without modulus
-- ============================================================

/-- A convergent sequence with a computable modulus. -/
structure ConvergentWithModulus where
  seq : ℕ → ℝ
  limit : ℝ
  modulus : ℕ → ℕ  -- given k, returns N such that n ≥ N ⟹ |a_n - L| < 2⁻ᵏ
  spec : ∀ k : ℕ, ∀ n : ℕ, modulus k ≤ n →
    |seq n - limit| < (2 : ℝ)⁻¹ ^ k

/-- A bounded monotone sequence (the type that costs LPO). -/
structure BoundedMonotoneSeq where
  seq : ℕ → ℝ
  bound : ℝ
  mono : Monotone seq
  bdd : ∀ n, seq n ≤ bound

end
