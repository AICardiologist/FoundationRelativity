/-
  Paper 44: The Measurement Problem Dissolved
  Defs/Principles.lean — Constructive principles and hierarchy

  Self-contained redeclarations following the programme convention.
  Each paper is a standalone Lake package.

  Principles:
    - LPO  (Limited Principle of Omniscience)
    - WLPO (Weak Limited Principle of Omniscience)
    - BMC  (Bounded Monotone Convergence)
    - DC   (Dependent Choice, DC_ω)

  Hierarchy: LPO → WLPO (strict); DC independent of both.
  Equivalence: LPO ↔ BMC [Bridges–Vîță 2006].
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic

namespace Papers.P44

-- ========================================================================
-- Limited Principle of Omniscience
-- ========================================================================

/-- Limited Principle of Omniscience.
    For every binary sequence, either all terms are false or some term is true. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

-- ========================================================================
-- Weak Limited Principle of Omniscience
-- ========================================================================

/-- Weak Limited Principle of Omniscience.
    For every binary sequence, either all terms are false
    or it is not the case that all terms are false. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

-- ========================================================================
-- Bounded Monotone Convergence
-- ========================================================================

/-- Bounded Monotone Convergence: every bounded non-decreasing sequence
    of reals has a limit. Equivalent to LPO over BISH [Bridges–Vîță 2006].
    Identical to Papers.P14.BMC and Papers.P8.BMC. -/
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

-- ========================================================================
-- Dependent Choice
-- ========================================================================

/-- Dependent Choice (DC_ω): for any type α, any total binary relation R,
    and any starting point a₀, there exists an infinite R-chain from a₀.
    Strictly weaker than full AC but stronger than countable choice.
    Following Papers.P16.DC_omega. -/
def DC : Prop :=
  ∀ (α : Type) (R : α → α → Prop) (a₀ : α),
    (∀ a, ∃ b, R a b) →
    ∃ f : ℕ → α, f 0 = a₀ ∧ ∀ n, R (f n) (f (n + 1))

-- ========================================================================
-- Hierarchy
-- ========================================================================

/-- LPO implies WLPO. -/
theorem lpo_implies_wlpo : LPO → WLPO := by
  intro hLPO α
  rcases hLPO α with h_all | ⟨n, hn⟩
  · exact Or.inl h_all
  · right
    intro h_all
    exact absurd (h_all n) (by simp [hn])

-- ========================================================================
-- LPO ↔ BMC (axiomatized, citing verified sources)
-- ========================================================================

/-- LPO implies BMC. Sorry'd; follows from [Bridges–Vîță 2006, Theorem 2.1.5].
    The classical proof uses binary search on the value axis with LPO decisions.
    Changed from `axiom` to `theorem ... sorry` per ITP convention:
    `sorry` is for obligations to be filled; `axiom` for genuinely external assumptions. -/
theorem bmc_of_lpo : LPO → BMC := by sorry

/-- BMC implies LPO. Sorry'd; fully verified in Paper 8 (P8_LPO_IsingBound,
    theorem `lpo_of_bmc` in PartB_Backward.lean) via encoding binary sequences
    into 1D Ising free energy sequences. See Zenodo bundle for Paper 8.
    Changed from `axiom` to `theorem ... sorry` per ITP convention. -/
theorem lpo_of_bmc : BMC → LPO := by sorry

/-- **LPO ↔ BMC.** The fundamental equivalence between the Limited Principle
    of Omniscience and Bounded Monotone Convergence [Bridges–Vîță 2006].
    Both directions axiomatized here; see Paper 8 for the verified backward proof. -/
theorem lpo_iff_bmc : LPO ↔ BMC :=
  ⟨bmc_of_lpo, lpo_of_bmc⟩

end Papers.P44
