/-
  Paper 49: Hodge Conjecture — Lean 4 Formalization
  H2_RationalityLPO.lean: Theorem H2 — Rationality Requires LPO

  Main result (Theorem H2):
    (∀ x, is_rational x ∨ ¬ is_rational x) → LPO_C

  Testing whether a complex cohomology class is rational requires
  LPO: one must decide whether transcendental coordinates are
  exactly equal to rational numbers.

  The full characterization is LPO + MP (Markov's Principle):
  - LPO: for zero-testing complex coordinates
  - MP: for unbounded search of the rational witness p/q
  We formalize the LPO component; MP is documented but not
  formally encoded as a biconditional.

  This parallels the encoding pattern of Paper 46 T1 and
  Paper 49 H1, with rationality replacing Galois-invariance.

  Axiom profile: encode_scalar_to_rationality
  No sorry.
-/

import Papers.P49_Hodge.Defs

noncomputable section

namespace Papers.P49

-- ============================================================
-- §1. Rationality Testing Requires LPO
-- ============================================================

/-- **Theorem H2: Deciding rationality requires LPO.**

    If rationality (membership in the image of H_Q → H_C)
    is decidable for all x ∈ H_C, then every scalar z ∈ ℂ
    is decidably zero or nonzero.

    Proof: For any z : ℂ, the encoding axiom provides x ∈ H_C
    with is_rational x ↔ z = 0. The decidability oracle on x
    then decides z = 0.

    NOTE: The full characterization of rationality decidability
    is LPO + MP:
    - LPO component (formalized here): testing whether a given
      complex number equals a specific rational p/q requires
      exact zero-testing (z - p/q = 0?).
    - MP component (documented, not formalized): even with LPO,
      FINDING which p/q equals z requires unbounded search over
      all rationals — this is Markov's Principle.

    Together, rationality testing = LPO (test) + MP (search). -/
theorem rationality_requires_LPO :
    (∀ (x : H_C), is_rational x ∨ ¬ is_rational x) → LPO_C := by
  intro h_dec z
  -- Encode z into a class whose rationality encodes z = 0
  obtain ⟨x, hx⟩ := encode_scalar_to_rationality z
  -- The oracle decides is_rational x
  rcases h_dec x with h_in | h_not_in
  · -- x is rational → z = 0
    left; exact hx.mp h_in
  · -- x is not rational → z ≠ 0
    right; exact fun hz => h_not_in (hx.mpr hz)

end Papers.P49
