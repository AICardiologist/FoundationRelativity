/-
  Paper 29: Fekete's Subadditive Lemma ↔ LPO
  Defs.lean — Core definitions

  Part of the Constructive Calibration Programme (see Paper 10).

  Defines:
    - LPO (Limited Principle of Omniscience)
    - BMC (Bounded Monotone Convergence)
    - FeketeConvergence (Fekete's Subadditive Lemma as a Prop)
    - hasTrue (decidable bounded search indicator)
    - mockFreeEnergy (the encoding F_n = -n · x_n)

  The key encoding insight (due to analysis by Gemini 3.0 DeepThink):
  For a binary sequence α, define x_n = 1 if ∃ k < n, α(k) = true, else 0.
  Then F_n = -n · x_n is subadditive, bounded below, and its Fekete limit
  decides α. This gives Fekete → LPO.

  Constructive design:
    - x_n is computed by decidable bounded search (no Classical.choice)
    - F_n is pure arithmetic
    - The Fekete → LPO direction uses NO classical logic beyond ℝ infrastructure
    - The LPO → Fekete direction intentionally uses BMC (the whole point)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
namespace Papers.P29

open Real

-- ========================================================================
-- Logical principles
-- ========================================================================

/-- Limited Principle of Omniscience.
    For every binary sequence, either all terms are false or some term is true. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- Bounded Monotone Convergence: every bounded non-decreasing sequence
    of reals has a limit. Equivalent to LPO over BISH [Bridges–Vîță 2006]. -/
def BMC : Prop :=
  ∀ (a : ℕ → ℝ) (M : ℝ),
    Monotone a →
    (∀ n, a n ≤ M) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → |a N - L| < ε

/-- Fekete's Subadditive Lemma as a logical principle.
    Every subadditive sequence with u(n)/n bounded below converges.
    Classically, lim u(n)/n = inf_{n≥1} u(n)/n. -/
def FeketeConvergence : Prop :=
  ∀ (u : ℕ → ℝ),
    (∀ m n, u (m + n) ≤ u m + u n) →
    (∃ C : ℝ, ∀ n : ℕ, 0 < n → C ≤ u n / ↑n) →
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N → |u N / ↑N - L| < ε

-- ========================================================================
-- Indicator sequence (decidable, no classical content)
-- ========================================================================

/-- Decidable bounded search: is there a k < n with α(k) = true?
    This is computable because α is Bool-valued and the search is finite.
    Using strict < avoids the n=0 edge case: hasTrue α 0 = false always. -/
def hasTrue (α : ℕ → Bool) (n : ℕ) : Bool :=
  (List.range n).any (fun k => α k)

/-- The indicator as a real number: x_n ∈ {0, 1}.
    x_n = 1 if ∃ k < n, α(k) = true, else x_n = 0. -/
def indicator (α : ℕ → Bool) (n : ℕ) : ℝ :=
  if hasTrue α n then 1 else 0

-- ========================================================================
-- Mock free energy (the encoding)
-- ========================================================================

/-- Mock free energy: F_n = -n · x_n.
    Encodes a binary sequence into a subadditive sequence.
    If α ≡ false: F_n = 0 for all n, so F_n/n → 0.
    If ∃ k, α(k) = true: eventually F_n = -n, so F_n/n → -1.
    The gap of 1 between the two limit values enables LPO extraction. -/
def mockFreeEnergy (α : ℕ → Bool) (n : ℕ) : ℝ :=
  -(↑n : ℝ) * indicator α n

end Papers.P29
end
