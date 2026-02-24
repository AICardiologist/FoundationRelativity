/-
  Paper 36: Cubitt's Spectral Gap Undecidability Stratification
  Defs.lean: Infrastructure and definitions

  Turing machines, CPgW Hamiltonians, spectral gap definitions,
  and constructive principles.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open Real

-- ============================================================
-- Constructive Principles
-- ============================================================

def LPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ (∃ n, a n = true)

def WLPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ ¬(∀ n, a n = false)

def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a → (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

axiom bmc_of_lpo : LPO → BMC
axiom wlpo_of_lpo : LPO → WLPO

-- ============================================================
-- Turing Machine Encoding
-- ============================================================

/-- Abstract Turing machine type.
    We do not formalize the internal structure; the CPgW bridge
    lemmas encode the relevant computational content. -/
def TM : Type := ℕ  -- Gödel number encoding

/-- The halting sequence for a TM: h_n = true iff M halts within n steps. -/
def halting_seq (_ : TM) : ℕ → Bool := fun _ => false  -- placeholder

/-- M halts iff ∃ n, halting_seq M n = true. -/
def halts (M : TM) : Prop := ∃ n, halting_seq M n = true

-- ============================================================
-- CPgW Hamiltonian Family
-- ============================================================

/-- The CPgW construction maps a TM to a family of Hamiltonians
    parameterized by lattice size L. -/
def CPgW_gap (_ : TM) (_ : ℕ) : ℝ := 0  -- placeholder

/-- The gap constant γ > 0 from CPgW: in the non-halting case,
    the gap is at least γ for all sufficiently large L. -/
def cpgw_gamma : ℝ := 1  -- normalized

/-- The thermodynamic limit of the spectral gap. -/
def spectral_gap (_ : TM) : ℝ := 0  -- placeholder (exists by LPO)

-- ============================================================
-- Gap Classification
-- ============================================================

/-- A Hamiltonian is "gapped" if Δ > 0, "gapless" if Δ = 0. -/
inductive GapStatus where
  | Gapped  : GapStatus
  | Gapless : GapStatus
  deriving DecidableEq, BEq, Repr

/-- The uniform classification function G : TM → GapStatus.
    This is the function that Cubitt proved is non-computable. -/
def gap_classify (M : TM) : GapStatus :=
  if spectral_gap M > 0 then .Gapped else .Gapless

end
