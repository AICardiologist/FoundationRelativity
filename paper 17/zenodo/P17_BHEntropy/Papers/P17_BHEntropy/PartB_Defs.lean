/-
Papers/P17_BHEntropy/PartB_Defs.lean
Core definitions for Part B: Entropy convergence ↔ LPO.

Part B proves that asserting the entropy density S(A)/A converges to a
completed real number as A → ∞ is equivalent to LPO (via Bounded Monotone
Convergence). The proof encodes binary sequences into entropy density
sequences via the running maximum.

Definitions:
  - runMax (running maximum of a binary sequence)
  - areaSeq (non-decreasing area sequence from a binary sequence)
  - S_alpha (entropy density along the area sequence)
  - EntropyConvergence (the convergence statement parameterized by γ, δ)
-/
import Papers.P17_BHEntropy.Entropy

noncomputable section
namespace Papers.P17

open Real

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
-- Area sequence
-- ========================================================================

/-- Area sequence from a binary sequence α.
    Maps α to a non-decreasing sequence in {A_lo, A_hi} via the running maximum.
    If all α(k) = false up to n, area is A_lo; otherwise A_hi. -/
def areaSeq (α : ℕ → Bool) (A_lo A_hi : ℝ) (n : ℕ) : ℝ :=
  if runMax α n then A_hi else A_lo

-- ========================================================================
-- Encoded entropy density sequence
-- ========================================================================

/-- The encoded entropy density sequence.
    S_alpha(n) = entropy_density(A(n), γ, δ) where A(n) is the area
    determined by the running maximum of α.

    Note: we use explicit proof terms for the positivity hypotheses,
    obtained from the gap lemma witnesses. -/
def S_alpha (α : ℕ → Bool) (A_lo A_hi gamma delta : ℝ)
    (hA_lo : A_lo > 0) (hA_hi : A_hi > 0)
    (hg : gamma > 0) (hd : delta > 0) (n : ℕ) : ℝ :=
  match runMax α n with
  | true => entropy_density A_hi gamma delta hA_hi hg hd
  | false => entropy_density A_lo gamma delta hA_lo hg hd

-- ========================================================================
-- Entropy convergence statement
-- ========================================================================

/-- Entropy Convergence: for every binary sequence α, the encoded
    entropy density sequence S_alpha converges.
    This is parameterized by the gap witnesses (A_lo, A_hi) and
    physical parameters (γ, δ). -/
def EntropyConvergence
    (A_lo A_hi gamma delta : ℝ)
    (hA_lo : A_lo > 0) (hA_hi : A_hi > 0)
    (hg : gamma > 0) (hd : delta > 0) : Prop :=
  ∀ (α : ℕ → Bool),
    ∃ L : ℝ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |S_alpha α A_lo A_hi gamma delta hA_lo hA_hi hg hd N - L| < ε

end Papers.P17
end
