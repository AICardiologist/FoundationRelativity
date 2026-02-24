/-
  Paper 29: Fekete's Subadditive Lemma ↔ LPO
  Main.lean — Assembly of the equivalence theorem

  Main result:
    FeketeConvergence ↔ LPO

  Forward (axiomatized): LPO → BMC → FeketeConvergence
    [Bridges–Vîță 2006 for LPO → BMC; classical Fekete proof for BMC → Fekete]
  Backward (fully proved): FeketeConvergence → LPO
    By encoding binary sequences into mock free energy F_n = -n · x_n.

  Physical significance (Paper 10, Problem 1 — resolved):
  ─────────────────────────────────────────────────────────
  The thermodynamic limit for GENERIC interacting systems relies on
  Fekete's subadditive lemma applied to log Z_Λ. Since Fekete ↔ LPO,
  the generic thermodynamic limit costs exactly LPO.

  Exactly solvable models (1D Ising) bypass Fekete via closed-form
  solutions that provide explicit Cauchy moduli (Papers 8, 9 — BISH).
  Exact solvability is the physical mechanism that exempts specific
  systems from the universal LPO cost.

  The LPO cost becomes ineliminable precisely at phase transitions
  and critical points, where correlation lengths diverge and all
  explicit finite-size bounds (closed forms, cluster expansions) fail.

  Axiom profile:
    lpo_of_fekete:    [propext, Classical.choice, Quot.sound] (no custom axioms)
    fekete_iff_lpo:   [propext, Classical.choice, Quot.sound, bmc_of_lpo, fekete_of_bmc]
                      (two cited axioms for the forward direction)

  Zero `sorry`s. Zero custom axioms in the backward direction.
-/
import Papers.P29_FeketeLPO.Decision
import Papers.P29_FeketeLPO.Forward

namespace Papers.P29

-- ========================================================================
-- The Equivalence Theorem
-- ========================================================================

/-- **FeketeConvergence ↔ LPO (Main Theorem).**

    Over BISH, Fekete's Subadditive Lemma is equivalent to the
    Limited Principle of Omniscience.

    Forward (fekete_of_lpo): LPO → BMC [Bridges–Vîță 2006] → Fekete.
      Axiomatized. The classical proof of Fekete uses BMC to extract
      the limit of the running minimum of u(n)/n.

    Backward (lpo_of_fekete): By encoding binary sequences α into
      mock free energies F_n = -n · x_n (where x_n = 1 iff ∃ k<n, α(k)=true),
      applying Fekete to obtain a limit, and using the gap between the
      two possible limit values (0 and -1) to decide α.

    Combined with Papers 8 and 9, this resolves Paper 10 Problem 1:
    the thermodynamic limit via Fekete (the generic route) costs exactly LPO,
    while the exactly solvable 1D Ising model bypasses Fekete at zero cost.

    The constructive hierarchy calibrates:
      Exact solution (closed-form modulus)     → BISH
      Cluster expansion (exponential modulus)   → BISH
      Generic subadditivity (Fekete's lemma)    → LPO  -/
theorem fekete_iff_lpo : FeketeConvergence ↔ LPO :=
  ⟨lpo_of_fekete, fekete_of_lpo⟩

-- ========================================================================
-- Axiom audit
-- ========================================================================

-- The backward direction should have NO custom axioms:
#print axioms lpo_of_fekete
-- Expected: [propext, Classical.choice, Quot.sound]

-- The full equivalence depends on the axiomatized forward direction:
#print axioms fekete_iff_lpo
-- Expected: [propext, Classical.choice, Quot.sound, bmc_of_lpo, fekete_of_bmc]

end Papers.P29
