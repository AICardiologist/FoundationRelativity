/-
  Paper 37: Uncomputability of Phase Diagrams and RG Flows is LPO
  Defs.lean: Core definitions shared across all modules

  Definitions for Turing machines, halting, LPO/WLPO,
  and the physical system types for BCW, BCLPG, and CLPE encodings.
-/
import Mathlib.Topology.Order
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic

noncomputable section

open Real

-- ============================================================
-- Logical Principles
-- ============================================================

/-- LPO (Limited Principle of Omniscience):
    For any binary sequence, either some term is true or all terms are false. -/
def LPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ (∃ n, a n = true)

/-- WLPO (Weak LPO): For any binary sequence,
    either all terms are false or it is not the case that all are false. -/
def WLPO : Prop :=
  ∀ (a : ℕ → Bool), (∀ n, a n = false) ∨ ¬(∀ n, a n = false)

/-- WLPO is subsumed by LPO. -/
theorem wlpo_of_lpo : LPO → WLPO := by
  intro hlpo a
  rcases hlpo a with h_all | ⟨n, hn⟩
  · left; exact h_all
  · right; intro h_all
    have := h_all n
    rw [this] at hn
    exact Bool.false_ne_true hn

-- ============================================================
-- Turing Machine Infrastructure
-- ============================================================

/-- Turing machines are encoded as natural numbers (Gödel numbers). -/
def TM : Type := ℕ

/-- The halting indicator sequence for a Turing machine.
    halting_seq M n = true iff M halts in exactly n steps. -/
def halting_seq (_ : TM) : ℕ → Bool := fun _ => false  -- placeholder

/-- A Turing machine halts if its halting sequence has a true entry. -/
def halts (M : TM) : Prop := ∃ n, halting_seq M n = true

/-- Construct a TM from a binary sequence (for reduction arguments). -/
axiom tm_from_seq : (ℕ → Bool) → TM

/-- The constructed TM halts iff the sequence has a true entry. -/
axiom tm_from_seq_halts (a : ℕ → Bool) :
    halts (tm_from_seq a) ↔ ∃ n, a n = true

-- ============================================================
-- Physical System Types (Opaque / Axiomatized)
-- ============================================================

/-- Phase classification for BCW (Bausch-Cubitt-Watson) phase diagrams. -/
inductive Phase where
  | PhaseA  -- corresponds to non-halting (ordered phase)
  | PhaseB  -- corresponds to halting (disordered phase)
  deriving DecidableEq, BEq, Repr

/-- Gap status for spectral gap problems. -/
inductive GapStatus where
  | Gapped   -- spectral gap > 0 (non-halting)
  | Gapless  -- spectral gap = 0 (halting)
  deriving DecidableEq, BEq, Repr

/-- RG fixed point classification for CLPE (Cubitt-Lucia-Perez-Garcia-Perez-Eceiza). -/
inductive RGFixedPoint where
  | GappedFP    -- gapped fixed point (non-halting)
  | GaplessFP   -- gapless fixed point (halting)
  deriving DecidableEq, BEq, Repr

-- ============================================================
-- Encoding Functions (Opaque types for bridge lemmas)
-- ============================================================

/-- BCW Hamiltonian (parametrized by real φ ∈ [0,1]). -/
def BCW_Hamiltonian : Type := ℝ

/-- BCLPG 1D Hamiltonian (parametrized by TM). -/
def BCLPG_Hamiltonian : Type := ℕ

/-- CLPE RG flow initial condition (parametrized by TM). -/
def CLPE_RGState : Type := ℕ

/-- Watson-Cubitt: ground state energy density. -/
def GroundStateEnergyDensity : Type := ℝ

-- ============================================================
-- Utility: binary real from sequence
-- ============================================================

/-- The real number Σ a(n) · 2⁻ⁿ ∈ [0,1] from a binary sequence. -/
def binary_real (_ : ℕ → Bool) : ℝ := 0  -- placeholder

/-- The binary real of any sequence lies in [0,1]. -/
axiom binary_real_in_unit (a : ℕ → Bool) :
    binary_real a ∈ Set.Icc (0 : ℝ) 1

end
