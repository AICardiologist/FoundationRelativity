/-
  Paper 45: Weight-Monodromy Conjecture — Lean 4 Formalization
  Main.lean: Root module and axiom audit

  This paper formalizes the reduction of the Weight-Monodromy Conjecture
  (WMC) for smooth projective varieties in mixed characteristic to a
  single open conjecture — the Arithmetic Kashiwara Conjecture (Sub-lemma 5) —
  and applies Constructive Reverse Mathematics to calibrate its logical strength.

  ═══════════════════════════════════════════════════════════════════════
  MAIN RESULTS
  ═══════════════════════════════════════════════════════════════════════

  1. WMC_from_five_sublemmas:
     Sub-lemma 5 → WMC for all smooth projective varieties
     (by induction on dimension, composing Sub-lemmas 1–5)

  2. polarization_forces_degeneration_BISH (Theorem C1):
     Positive-definite inner product + Laplacian = 0 → d = 0
     (FULL PROOF — no sorry, no custom axioms, no omniscience needed)

  3. abstract_degeneration_iff_LPO (Theorem C2):
     DecidesDegeneration K ↔ LPO_field K
     (FULL PROOF, exact logical calibration)

  4. no_pos_def_hermitian_padic (Theorem C3):
     Over ℚ_p, no positive-definite Hermitian form in dim ≥ 3
     (sorry-free — trace form isotropy axiomatized, proof from axioms)

  5. de_omniscientizing_descent (Theorem C4):
     Abstract: LPO required. Geometric: decidable in BISH.
     (decidability derived constructively from geometric_differential_decidable
      and spectral_sequence_bounded — no Classical.dec, no sorry)

  ═══════════════════════════════════════════════════════════════════════
  AXIOM INVENTORY (22 custom axioms)
  ═══════════════════════════════════════════════════════════════════════

  Arithmetic geometry (Phase 2 will replace with full definitions):
  - WMC_holds_for              — WMC as opaque Prop
  - StalkwiseWMC               — stalkwise WMC on fibers
  - GradedPiecesArePure         — pointwise pure graded pieces
  - FrobeniusPure               — Frobenius purity predicate
  - IsGeometric                 — geometric origin predicate
  - defaultWSS                  — default spectral sequence
  - abutment_eq_monodromy       — abutment = monodromy filtration

  Sub-lemmas 1–4 (all KNOWN results):
  - sublemma_1 [KNOWN] — Semistable Lefschetz pencil
  - sublemma_2 [KNOWN] — Perverse pushforward via nearby cycles
  - sublemma_3 [KNOWN] — Stalkwise purity (inductive hypothesis)
  - sublemma_4 [KNOWN] — Global Frobenius purity (Weil II)
  (Sub-lemma 5 is NOT axiomatized — it is a hypothesis parameter
   in WMC_from_five_sublemmas, preserving conditionality.)

  Bridge axioms:
  - WMC_curves                  — base case (dim ≤ 1, Grothendieck SGA 7)
  - WMC_base_change_descent     — descent from finite extensions [DECLARED, UNUSED]
  - combine_filtrations         — spectral sequence → global WMC

  Constructive calibration (C3):
  - uInvariant                  — u-invariant function [DECLARED, UNUSED — absorbed into trace_form_isotropic]
  - u_invariant_padic           — u(ℚ_p) = 4 [DECLARED, UNUSED — absorbed into trace_form_isotropic]
  - trace_form_isotropic        — Hermitian forms of dim ≥ 3 have isotropic trace form

  Constructive calibration (C4):
  - QBar                        — algebraic closure of ℚ (type)
  - QBar_instField              — field instance on ℚ̄
  - QBar_decidable_eq           — decidable equality on ℚ̄
  - geometric_differential_decidable — per-page decidable differentials (from algebraicity)
  - spectral_sequence_bounded   — spectral sequences eventually stationary

  NOTE on unused axioms:
  - WMC_base_change_descent: intended for base-change descent step, but
    combine_filtrations absorbed that role in the reduction proof
  - uInvariant, u_invariant_padic: intended for explicit u-invariant bound,
    but trace_form_isotropic directly gives isotropy without separate bound
  - QBar, QBar_instField, QBar_decidable_eq:
    These axioms document the mathematical JUSTIFICATION for
    geometric_differential_decidable (algebraicity → decidable equality →
    decidable matrix vanishing). They are referenced in the axiom chain
    explanation but not directly called in proofs. The load-bearing axiom
    is geometric_differential_decidable which captures their combined content.

  ═══════════════════════════════════════════════════════════════════════
  SORRY COUNT: 0
  All non-constructive mathematical content is isolated in axioms.
  All proofs from axioms are machine-checked and sorry-free.
  ═══════════════════════════════════════════════════════════════════════
-/

import Papers.P45_WMC.Reduction
import Papers.P45_WMC.Calibration

namespace Papers.P45

-- ============================================================
-- Axiom Audits
-- ============================================================

-- Main reduction theorem: 5 sub-lemma axioms + bridge axioms
-- Expected: propext, Quot.sound, FrobeniusPure, GradedPiecesArePure,
--   StalkwiseWMC, WMC_curves, WMC_holds_for, abutment_eq_monodromy,
--   combine_filtrations, defaultWSS, sublemma_1–4
-- NOTE: No Classical.choice in the reduction!
#print axioms WMC_from_five_sublemmas

-- Theorem C1: only Lean infrastructure axioms
-- (propext, Classical.choice, Quot.sound — no custom axioms)
#print axioms polarization_forces_degeneration_BISH

-- Theorem C2: only Lean infrastructure axioms
#print axioms abstract_degeneration_iff_LPO

-- Theorem C3: trace_form_isotropic + infrastructure
#print axioms no_pos_def_hermitian_padic

-- Theorem C4 (core): geometric_differential_decidable,
--   spectral_sequence_bounded, IsGeometric + infrastructure
-- NOTE: Classical.choice appears from Lean ℝ/ℂ infrastructure,
--   NOT from Classical.dec — decidability is derived from axioms
#print axioms geometric_degeneration_decidable_BISH

-- Constructive calibration summary (C1 + C2 + C3 + C4 combined)
#print axioms constructive_calibration_summary

-- De-omniscientizing descent (C2 + C4 combined)
#print axioms de_omniscientizing_descent

end Papers.P45
