/-
Papers/P19_WKBTunneling/WKB/Limit.lean
Semiclassical limit structure: the WKB amplitude convergence as ℏ → 0.

The sequence ℏₙ = 1/(n+1) → 0 as n → ∞. The assertion that the WKB
amplitude T(ℏₙ) converges to a limit L is a completed infinite process
that costs BMC/LPO.
-/
import Papers.P19_WKBTunneling.WKB.Amplitude

noncomputable section
namespace Papers.P19

-- ========================================================================
-- Semiclassical convergence (sequence formulation)
-- ========================================================================

/-- The semiclassical sequence: ℏₙ = 1/(n+1).
    This is a positive, monotone decreasing sequence converging to 0. -/
def hbarSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- Each ℏₙ is positive. -/
lemma hbarSeq_pos (n : ℕ) : 0 < hbarSeq n := by
  unfold hbarSeq
  positivity

/-- Semiclassical convergence for a specific barrier:
    the sequence T(ℏₙ) has a limit as n → ∞. -/
def SemiclassicalConvergence (B : Barrier) (tp : TurningPoints B) (m : ℝ) : Prop :=
  ∃ L : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |wkbAmplitude B tp m (hbarSeq N) - L| < ε

-- ========================================================================
-- Full WKB assertion (for Part C)
-- ========================================================================

/-- The full WKB assertion for a general barrier combines two ingredients:
    1. **Turning points exist** (TPP): for any continuous barrier, find where
       V(x) = E. This costs LLPO (Part B, Theorem 4).
    2. **Bounded monotone convergence** (BMC): the semiclassical limit ℏ → 0
       involves asserting convergence of bounded monotone sequences of
       approximations. This costs LPO (Bridges-Vîță 2006).

    The conjunction TPP ∧ BMC captures the full logical content of the
    semiclassical tunneling computation for general barriers. Since
    BMC ↔ LPO and LPO → LLPO → TPP, the conjunction is equivalent to LPO. -/
def FullWKBGeneralBarrier : Prop :=
  TPP ∧ BMC

end Papers.P19
end
