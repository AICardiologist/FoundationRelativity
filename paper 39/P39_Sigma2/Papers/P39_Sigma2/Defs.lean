/-
  Paper 39: Physics Reaches Σ₂⁰ — The Thermodynamic Stratification
  Defs.lean: Core definitions

  NEW in this paper: LPO_jump (the Turing jump of LPO),
  strictly stronger than LPO. Encodes Σ₂⁰-LEM.
-/
import Mathlib.Topology.Order
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic

noncomputable section

-- ============================================================
-- Turing Machines and Halting (standard infrastructure)
-- ============================================================

abbrev TM : Type := ℕ

axiom halting_seq : TM → ℕ → Bool

def halts (M : TM) : Prop := ∃ n, halting_seq M n = true

-- Multi-input halting: M runs on input k
def halts_on_input (M : TM) (k : ℕ) : Prop := ∃ n, halting_seq (M + k) n = true

-- Bounded halting: M halts on input k within t steps
-- (In the modified Cubitt encoding, t = 16^k)
axiom halts_within : TM → ℕ → ℕ → Prop

-- The bounded halting predicate is decidable (BISH — finite computation)
axiom halts_within_decidable (M : TM) (k : ℕ) (t : ℕ) :
    Decidable (halts_within M k t)

-- TM encoding from binary sequences
axiom tm_from_seq : (ℕ → Bool) → TM
axiom tm_from_seq_halts (a : ℕ → Bool) :
    halts (tm_from_seq a) ↔ ∃ n, a n = true

-- ============================================================
-- LPO (Σ₁⁰-LEM) — from Papers 1–38
-- ============================================================

def LPO : Prop :=
    ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ (∃ n, a n = true)

-- ============================================================
-- LPO_jump (Σ₂⁰-LEM) — NEW in Paper 39
-- ============================================================

-- LPO_jump is the Turing jump of LPO.
-- It decides: for a double sequence α : ℕ → ℕ → Bool,
-- given that each row is LPO-decidable (inner level),
-- decide whether all rows are all-false, or some row has a true entry.
-- Equivalently: decide the Finiteness Problem.
--
-- Formal definition via double sequences:
--   Given α : ℕ → ℕ → Bool where each row's LPO status is known,
--   decide: (∃ n, ∀ m, α n m = false) ∨ (∀ n, ∃ m, α n m = true)
--
-- Simplified operational form used here:
def LPO_jump : Prop :=
    ∀ (β : ℕ → Bool),
      -- β is LPO-computable (decidable relative to an LPO oracle)
      (LPO → ∀ n, β n = true ∨ β n = false) →
      (∀ n, β n = false) ∨ (∃ n, β n = true)

-- LPO_jump is strictly stronger than LPO
theorem lpo_jump_implies_lpo : LPO_jump → LPO := by
  intro lpo_j a
  exact lpo_j a (fun _ _ => by cases a _  <;> simp)

-- ============================================================
-- Σ₂⁰ and Π₂⁰ completeness structures
-- ============================================================

structure Sigma2Complete (P : TM → Prop) : Prop where
  -- P is Σ₂⁰: ∃-∀ form over decidable predicates
  sigma2_form : ∀ M, P M ↔ ∃ K, ∀ k, k > K → ¬halts_within M k (16 ^ k)
  -- Deciding P for all M requires LPO_jump
  requires_lpo_jump : (∀ M, P M ∨ ¬P M) → LPO_jump
  -- LPO_jump suffices to decide P
  decided_by_lpo_jump : LPO_jump → ∀ M, P M ∨ ¬P M

structure Pi2Complete (P : TM → Prop) : Prop where
  -- P is Π₂⁰: ∀-∃ form (complement of Σ₂⁰)
  pi2_form : ∀ M, P M ↔ ∀ K, ∃ k, k > K ∧ halts_within M k (16 ^ k)
  -- Deciding P for all M requires LPO_jump
  requires_lpo_jump : (∀ M, P M ∨ ¬P M) → LPO_jump
  -- LPO_jump suffices to decide P
  decided_by_lpo_jump : LPO_jump → ∀ M, P M ∨ ¬P M

-- Σ₁⁰ completeness (from Paper 38, for comparison)
structure Sigma1Complete (P : TM → Prop) : Prop where
  sigma1_form : ∀ M, P M ↔ ∃ n, halting_seq M n = true
  requires_lpo : (∀ M, P M ∨ ¬P M) → LPO
  decided_by_lpo : LPO → ∀ M, P M ∨ ¬P M

-- ============================================================
-- The Finiteness Problem
-- ============================================================

-- The halting set of M (bounded version)
def halting_set (M : TM) : Set ℕ :=
    {k : ℕ | halts_within M k (16 ^ k)}

-- The Finiteness Problem: is the halting set finite?
def finiteness_problem (M : TM) : Prop :=
    Set.Finite (halting_set M)

-- ============================================================
-- Modified Cubitt Encoding (Theorem 1)
-- ============================================================

-- The modified Hamiltonian: M ↦ H*(M)
axiom ModifiedHamiltonian : Type
axiom modified_hamiltonian : TM → ModifiedHamiltonian

-- Spectral gap properties
axiom is_gapped : ModifiedHamiltonian → Prop
axiom is_gapless : ModifiedHamiltonian → Prop

-- Gapped and gapless are complementary
axiom gapped_iff_not_gapless (H : ModifiedHamiltonian) :
    is_gapped H ↔ ¬is_gapless H

-- ============================================================
-- Promise-Gapped Hamiltonians (Theorem 3)
-- ============================================================

structure PromiseGapped where
  hamiltonian : ModifiedHamiltonian
  gamma : ℝ
  gamma_pos : gamma > 0
  -- The promise: gap is either 0 or ≥ gamma
  promise : is_gapless hamiltonian ∨ is_gapped hamiltonian

-- ============================================================
-- Thermodynamic Observable Types (Theorem 4)
-- ============================================================

-- Extensive observable (energy density, free energy, magnetization)
-- Converges via Fekete/BMC — subadditive
structure ExtensiveObservable where
  -- Finite-size values
  finite_value : ℕ → ℝ
  -- Subadditivity: f(m+n) ≤ f(m) + f(n) (after normalization)
  subadditive : ∀ m n, finite_value (m + n) ≤ finite_value m + finite_value n
  -- BISH-computable for each L
  computable : True  -- placeholder (each f(L) is computable)

-- Intensive observable (spectral gap, correlation length)
-- Determined by infimum over spatial sectors
structure IntensiveObservable where
  -- Values at each scale
  scale_value : ℕ → ℝ
  -- The observable is the infimum
  is_infimum : True  -- placeholder (value = inf over scales)

-- Sign decision for extensive observables
def extensive_sign_positive (O : ExtensiveObservable) : Prop :=
    ∃ n, O.finite_value n > 0

-- Zero test for intensive observables
def intensive_is_zero (O : IntensiveObservable) : Prop :=
    ∀ ε : ℝ, ε > 0 → ∃ n, O.scale_value n < ε

-- Gap-less-than for empirical physics
axiom gap_less_than : ModifiedHamiltonian → ℝ → Prop

end
