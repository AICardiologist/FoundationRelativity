/-
  Paper 29: Fekete's Subadditive Lemma ↔ LPO
  Forward.lean — Forward direction: LPO → FeketeConvergence (axiomatized)

  The classical proof of Fekete's lemma proceeds by:
  1. Taking the running minimum v_n = inf_{1≤k≤n} u(k)/k
  2. Observing v_n is non-increasing and bounded below (by the given C)
  3. Applying BMC (≡ LPO) to -v_n to get a limit L
  4. Proving u(n)/n → L by the Euclidean division argument

  Step 3 is the single invocation of BMC/LPO. Steps 1, 2, 4 are BISH.
  The full proof is available in Mathlib as `Subadditive.tendsto_lim`
  (which uses classical logic throughout, including the infimum construction).

  We axiomatize this direction, following the same pattern as Paper 9's
  axiomatization of `bmc_of_lpo` [Bridges–Vîță 2006, Theorem 2.1.5].

  The novel content of Paper 29 is the backward direction (Decision.lean).
-/
import Papers.P29_FeketeLPO.Defs

namespace Papers.P29

-- ========================================================================
-- Forward direction (axiomatized)
-- ========================================================================

/-- LPO implies Bounded Monotone Convergence.
    [Bridges–Vîță 2006, Theorem 2.1.5]. Axiomatized. -/
axiom bmc_of_lpo : LPO → BMC

/-- BMC implies Fekete's Subadditive Lemma.
    The classical proof uses BMC to extract the limit of the running minimum,
    then the Euclidean division argument for the upper bound. Axiomatized.

    Mathlib proof: `Subadditive.tendsto_lim` in `Mathlib.Analysis.Subadditive`. -/
axiom fekete_of_bmc : BMC → FeketeConvergence

/-- LPO implies FeketeConvergence. Composition of the two axiomatized steps. -/
theorem fekete_of_lpo : LPO → FeketeConvergence :=
  fun h => fekete_of_bmc (bmc_of_lpo h)

end Papers.P29
