/-
Papers/P8_LPO_IsingBound/PartB_Defs.lean
Core definitions for Part B: LPO ↔ BMC via free energy convergence.

Part B proves the converse to Part A: asserting the thermodynamic limit
exists as a completed real number is equivalent to LPO (Bounded Monotone
Convergence). The proof encodes binary sequences into free energy sequences.

Definitions:
  - BMC (Bounded Monotone Convergence)
  - runMax (running maximum of a binary sequence)
  - couplingSeq (non-decreasing coupling from a binary sequence)
  - freeEnergyAtCoupling (g(J) = -log(2·cosh(β·J)))
  - encodedSeq (free energy along the coupling sequence)
-/
import Papers.P8_LPO_IsingBound.EigenvalueProps

noncomputable section
namespace Papers.P8

open Real

-- ========================================================================
-- Bounded Monotone Convergence
-- ========================================================================

/-- Bounded Monotone Convergence: every bounded non-decreasing sequence
    of reals has a limit. Equivalent to LPO over BISH [Bridges–Vîță 2006]. -/
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

-- ========================================================================
-- Running maximum of a binary sequence
-- ========================================================================

/-- Running maximum of a binary sequence α.
    runMax α n = max(α(0), α(1), ..., α(n)).
    In Bool: false < true, so this is true iff ∃ k ≤ n, α(k) = true. -/
def runMax (α : ℕ → Bool) : ℕ → Bool
  | 0 => α 0
  | n + 1 => α (n + 1) || runMax α n

-- ========================================================================
-- Coupling sequence
-- ========================================================================

/-- Coupling sequence from a binary sequence α.
    Maps α to a non-decreasing sequence in {J₀, J₁} via the running maximum.
    If all α(k) = false up to n, coupling is J₀; otherwise J₁. -/
noncomputable def couplingSeq (α : ℕ → Bool) (J₀ J₁ : ℝ) (n : ℕ) : ℝ :=
  if runMax α n then J₁ else J₀

-- ========================================================================
-- Free energy at coupling
-- ========================================================================

/-- Free energy at coupling J: g(J) = -log(2·cosh(β·J)).
    This is the infinite-volume free energy density of the 1D Ising chain
    with uniform coupling J. Equivalently, freeEnergyInfVol(β·J). -/
noncomputable def freeEnergyAtCoupling (β J : ℝ) : ℝ :=
  -log (2 * cosh (β * J))

-- ========================================================================
-- Encoded sequence
-- ========================================================================

/-- The encoded sequence: F(n) = g(J(n)) where J is the coupling sequence.
    This is the free energy along the coupling path determined by α. -/
noncomputable def encodedSeq (α : ℕ → Bool) (β J₀ J₁ : ℝ) (n : ℕ) : ℝ :=
  freeEnergyAtCoupling β (couplingSeq α J₀ J₁ n)

end Papers.P8
end
