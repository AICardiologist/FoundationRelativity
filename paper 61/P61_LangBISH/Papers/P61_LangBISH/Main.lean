/-
  Paper 61: Lang's Conjecture as the MP → BISH Gate
  The Decidability Hierarchy for Mixed Motives
  Main.lean — Root module and axiom audit

  Series: Constructive Reverse Mathematics and Physics
  Author: Paul C.-K. Lee, February 2026

  Main results:
    Theorem A (lang_implies_bish):          Lang + Minkowski + Northcott → BISH
    Theorem B (bish_does_not_imply_lang):   BISH ⟹̸ Lang
    Theorem C (generators_within_bound):    X₀(389) generators within bound
    Theorem D (no_northcott_iff_lpo):       Without Northcott, decidability ↔ LPO
    Theorem E (uniform_lang_analytic_bish): Uniform Lang → L-function certificates

  DPT Hierarchy:
    BISH ⊊ MP ⊊ LPO
    Lang's conjecture gates MP → BISH.
    Northcott property gates LPO → MP.

  Zero `sorry`s. Two axioms:
    - minkowski_second_theorem (geometry of numbers)
    - UniformLang (open conjecture, used only for Theorem E)
  Plus standard infrastructure axiom:
    - northcott_abelian_variety (classical finiteness)
-/
import Papers.P61_LangBISH.Forward.LangToBISH
import Papers.P61_LangBISH.Forward.Explicit389
import Papers.P61_LangBISH.Converse.BISHNotLang
import Papers.P61_LangBISH.Northcott.EscalationLPO
import Papers.P61_LangBISH.Uniform.UniformLang
import Papers.P61_LangBISH.Hierarchy

namespace Papers.P61_LangBISH

-- ========================================================================
-- Axiom audit
-- ========================================================================

#print axioms lang_implies_bish
#print axioms bish_does_not_imply_lang
#print axioms generators_within_bound
#print axioms no_northcott_iff_lpo
#print axioms uniform_lang_analytic_bish
#print axioms lang_gates_mp_to_bish
#print axioms hierarchy_exhaustive

-- Expected output:
--   lang_implies_bish:          [propext, Quot.sound, northcott_abelian_variety]
--   bish_does_not_imply_lang:   [propext, Quot.sound]  (no custom axioms)
--   generators_within_bound:    [propext, Quot.sound]  (pure computation)
--   no_northcott_iff_lpo:       does not depend on any axioms (or [propext])
--   uniform_lang_analytic_bish: [propext, Quot.sound, UniformLang]
--
-- Notes:
-- • Classical.choice may appear via Mathlib's ℚ/ℝ infrastructure — this is
--   a library artifact, not mathematical content (see Paper 10 §Methodology).
-- • minkowski_second_theorem is not used directly in the main theorems;
--   it justifies the formula in lang_minkowski_bound's docstring.
-- • UniformLang is an open conjecture, used only for Theorem E.
-- • northcott_abelian_variety is a classical theorem; axiomatized because
--   the proof requires algebraic geometry infrastructure beyond Mathlib.
-- • Zero `sorry`s. All proofs are complete.

end Papers.P61_LangBISH
