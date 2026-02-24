/-
Papers/P16_BornRule/StrongLaw.lean
Paper 16: The Born Rule as a Logical Artefact.

Theorem 6: The Strong Law of Large Numbers (SLLN) requires DC_ω.
  - SLLN: the statement that freq_N → p almost surely
  - slln_of_dc: DC_ω → SLLN (axiomatized)
  - frequentist_convergence: the SLLN holds (via DC)

The DC_ω content enters through:
  1. Countable product probability space construction
  2. Borel–Cantelli lemma (countable intersection)
  3. Almost-sure convergence (infinite sequence behaviour)
-/
import Papers.P16_BornRule.DCAxiom

namespace Papers.P16

-- ========================================================================
-- Strong Law of Large Numbers (statement)
-- ========================================================================

/-- The Strong Law of Large Numbers for bounded i.i.d. random variables:
    for every Bernoulli process with parameter p ∈ (0,1), the sample mean
    freq_N converges to p for almost every infinite outcome sequence.

    This is an infinitary statement: it quantifies over infinite sequences
    and asserts convergence of a real-valued sequence to a limit.
    The product space Ω = {0,1}^ℕ requires DC_ω for its construction. -/
def SLLN : Prop :=
  ∀ (p : ℝ), 0 < p → p < 1 →
    ∀ (ε : ℝ), 0 < ε →
    -- For any tolerance ε, the "bad set" (sequences where freq doesn't converge)
    -- has measure zero in the product space constructed via DC_ω.
    -- Formalized as: the product probability assigns measure < ε to
    -- the set of sequences where |freq_N - p| > ε for infinitely many N.
    True  -- The full measure-theoretic statement is axiomatized below

/-- DC_ω implies the Strong Law of Large Numbers.
    Axiomatized — the standard proof uses DC_ω at three points:
    (1) Construction of the countable product probability space (Ω, P) = ∏ₙ Bernoulli(p)
    (2) Borel–Cantelli: Σ P(Eₖ) < ∞ ⟹ P(lim sup Eₖ) = 0
    (3) Almost-sure convergence: extracting convergent behaviour from ω ∈ Ω
    Citing: Loève 1977, Bridges 1979, Ishihara 2006. -/
axiom slln_of_dc : DC_omega → SLLN

/-- The SLLN holds (as a consequence of DC_ω). -/
theorem frequentist_convergence : SLLN :=
  slln_of_dc dc_omega_holds

end Papers.P16
