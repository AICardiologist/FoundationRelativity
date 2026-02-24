/-
  Paper 49: Hodge Conjecture — Lean 4 Formalization
  Main.lean: Root module and axiom audit

  This paper formalizes the constructive reverse mathematics calibration
  of the Hodge Conjecture, proving that:

  ═══════════════════════════════════════════════════════════════════════
  MAIN RESULTS
  ═══════════════════════════════════════════════════════════════════════

  1. hodge_type_iff_LPO (Theorem H1):
     Deciding Hodge type (r,r) ↔ LPO for ℂ
     (FULL PROOF from encoding axiom)

  2. rationality_requires_LPO (Theorem H2):
     Deciding rationality → LPO for ℂ
     (FULL PROOF from encoding axiom; MP component documented)

  3. archimedean_polarization_available (Theorem H3a):
     Hodge-Riemann form is positive-definite on (r,r)-classes
     (sorry-free — from axiom)

  4. polarization_blind_to_rational_lattice (Theorem H3b):
     Hodge-Riemann pairing is blind to the rational lattice
     (sorry-free — from axiom, transcendence of periods)

  5. cycle_verification_BISH (Theorem H4):
     Numerical equivalence is decidable in BISH
     (FULL PROOF — integer arithmetic, no custom axioms beyond Defs)

  6. hodge_class_detection_requires_LPO (Theorem H5a):
     Detecting Hodge classes requires LPO
     (FULL PROOF from encoding axiom)

  7. hodge_conjecture_reduces_to_BISH (Theorem H5b):
     With the Hodge Conjecture, verification reduces to BISH + MP
     (FULL PROOF from conjecture hypothesis + DecidableEq on H_Q)

  8. nexus_observation (Theorem H5c):
     Neither polarization nor algebraic descent alone suffices
     (FULL PROOF assembling H3a, H3b, H5a)

  ═══════════════════════════════════════════════════════════════════════
  AXIOM INVENTORY
  ═══════════════════════════════════════════════════════════════════════

  Complex cohomology:
  - H_C                            — complex cohomology space (type)
  - H_C_addCommGroup               — additive group on H_C
  - H_C_module                     — ℂ-module on H_C
  - H_C_finiteDim                  — finite-dimensionality of H_C
  - H_C_module_Q                   — ℚ-module on H_C (restriction of scalars)

  Rational cohomology:
  - H_Q                            — rational cohomology space (type)
  - H_Q_addCommGroup               — additive group on H_Q
  - H_Q_module                     — ℚ-module on H_Q
  - H_Q_finiteDim                  — finite-dimensionality of H_Q
  - H_Q_decidableEq                — decidable equality on H_Q

  Rational inclusion:
  - rational_inclusion             — H_Q →ₗ[ℚ] H_C

  Hodge decomposition:
  - hodge_projection_rr            — projection onto H^{r,r}
  - hodge_projection_complement    — projection onto complement
  - hodge_decomposition            — x = π_rr(x) + π_comp(x)
  - hodge_projections_complementary — π_rr ∘ π_comp = 0

  Hodge-Riemann form:
  - hodge_riemann                  — bilinear form H_C × H_C → ℝ
  - hodge_riemann_pos_def_on_primitive — positive-definite on (r,r)

  Cycle class infrastructure:
  - ChowGroup                      — Chow group (type)
  - ChowGroup_addCommGroup         — additive group on ChowGroup
  - ChowGroup_module               — ℚ-module on ChowGroup
  - cycle_class                    — cycle class map ChowGroup →ₗ[ℚ] H_Q
  - intersection                   — integer-valued intersection pairing

  Encoding axioms:
  - encode_scalar_to_hodge_type    — encoding for H1 (scalar → Hodge type test)
  - LPO_decides_hodge_type         — bridge for H1 (LPO → decidability)
  - encode_scalar_to_rationality   — encoding for H2 (scalar → rationality test)
  - encode_scalar_to_cycle_in_HC   — encoding for H4e (scalar → cycle equation)
  - encode_scalar_to_hodge_class   — encoding for H5a (scalar → Hodge class test)

  Polarization blindness:
  - polarization_blind_to_Q        — periods are transcendental

  ═══════════════════════════════════════════════════════════════════════
  SORRY COUNT: 0
  All non-constructive mathematical content is isolated in axioms.
  All proofs from axioms are machine-checked and sorry-free.
  ═══════════════════════════════════════════════════════════════════════
-/

import Papers.P49_Hodge.H1_HodgeTypeLPO
import Papers.P49_Hodge.H2_RationalityLPO
import Papers.P49_Hodge.H3_Polarization
import Papers.P49_Hodge.H4_CycleVerify
import Papers.P49_Hodge.H5_Nexus

noncomputable section

namespace Papers.P49

-- ============================================================
-- Summary Theorem
-- ============================================================

/-- **Summary: The Constructive Calibration of the Hodge Conjecture.**

    The theorems H1–H5 together paint a precise picture of
    the logical structure of the Hodge Conjecture:

    H1. Hodge type decidability ↔ LPO:
        Deciding x ∈ H^{r,r} (complement projection = 0) is
        equivalent to the Limited Principle of Omniscience for ℂ.

    H2. Rationality testing → LPO:
        Deciding x ∈ im(H_Q → H_C) requires at least LPO
        (full characterization is LPO + MP).

    H3a. Archimedean polarization available:
        The Hodge-Riemann form is positive-definite on (r,r)-classes.
        u(ℝ) = 1 ensures this, unlike u(ℚ_p) = 4 which blocks it.

    H3b. Polarization blind to ℚ:
        The Hodge-Riemann pairing of rational classes is generally
        transcendental — the metric cannot see rational structure.

    H4. Cycle verification is BISH:
        Numerical equivalence of algebraic cycles reduces to
        finitely many integer equality tests — no LPO needed.

    H5. The nexus:
        Detecting Hodge classes requires LPO, but the Hodge
        Conjecture reduces detection to BISH + MP (cycle search +
        integer verification). Polarization handles Hodge type,
        algebraic descent handles rationality, but only the
        conjecture connects them. -/
theorem hodge_calibration_summary :
    -- H1: Hodge type decidability ↔ LPO
    ((∀ x : H_C, is_hodge_type_rr x ∨ ¬ is_hodge_type_rr x) ↔ LPO_C)
    ∧
    -- H2: Rationality testing → LPO
    ((∀ x : H_C, is_rational x ∨ ¬ is_rational x) → LPO_C)
    ∧
    -- H3a: Archimedean polarization available
    (∀ x : H_C, hodge_projection_rr x = x → x ≠ 0 →
      hodge_riemann x x > 0)
    ∧
    -- H3b: Polarization blind to ℚ
    ¬ (∀ (q₁ q₂ : H_Q), ∃ r : ℚ,
      hodge_riemann (rational_inclusion q₁) (rational_inclusion q₂) = ↑r)
    ∧
    -- H4: Cycle verification BISH-decidable
    (∀ {m : ℕ} (basis : Fin m → ChowGroup) (Z₁ Z₂ : ChowGroup),
      num_equiv_fin basis Z₁ Z₂ ∨ ¬ num_equiv_fin basis Z₁ Z₂)
    ∧
    -- H5: Hodge class detection requires LPO
    ((∀ x : H_C, is_hodge_class x ∨ ¬ is_hodge_class x) → LPO_C) := by
  exact ⟨
    hodge_type_iff_LPO,
    rationality_requires_LPO,
    hodge_riemann_pos_def_on_primitive,
    polarization_blind_to_Q,
    fun basis Z₁ Z₂ => cycle_verification_BISH basis Z₁ Z₂,
    hodge_class_detection_requires_LPO
  ⟩

-- ============================================================
-- Axiom Audits
-- ============================================================

-- H1: encode_scalar_to_hodge_type, LPO_decides_hodge_type + infrastructure
#print axioms hodge_type_iff_LPO

-- H2: encode_scalar_to_rationality + infrastructure
#print axioms rationality_requires_LPO

-- H3a: hodge_riemann_pos_def_on_primitive + infrastructure
#print axioms archimedean_polarization_available

-- H3b: polarization_blind_to_Q + infrastructure
#print axioms polarization_blind_to_rational_lattice

-- H4: no custom axioms beyond Defs infrastructure
#print axioms cycle_verification_BISH

-- H4e: encode_scalar_to_cycle_in_HC + infrastructure
#print axioms cycle_verification_in_HC_requires_LPO

-- H5a: encode_scalar_to_hodge_class + infrastructure
#print axioms hodge_class_detection_requires_LPO

-- H5b: H_Q_decidableEq + infrastructure
#print axioms hodge_conjecture_reduces_to_BISH

-- H5c: all axioms combined
#print axioms nexus_observation

-- Summary: all axioms
#print axioms hodge_calibration_summary

end Papers.P49
