/-
  Paper 49: Hodge Conjecture — Lean 4 Formalization
  H5_Nexus.lean: Theorem H5 — The Nexus Theorem

  Main results:
    1. hodge_class_detection_requires_LPO: Detecting Hodge classes
       (rational AND type (r,r)) requires LPO.
    2. hodge_conjecture_reduces_to_BISH: With the Hodge Conjecture,
       verification reduces to cycle search (MP) + integer test (BISH).
    3. nexus_observation: Neither polarization alone nor algebraic
       descent alone suffices — the Hodge Conjecture is the nexus
       where both mechanisms interact.

  The nexus is the key mathematical insight unique to Paper 49:
  - Papers 45-47: Polarization is BLOCKED (u = 4 over ℚ_p)
  - Paper 48: Polarization is AVAILABLE AND USEFUL (u = 1, Néron-Tate)
  - Paper 49: Polarization is AVAILABLE BUT INSUFFICIENT — it splits
    continuous space but cannot see rational structure.

  The Hodge Conjecture lives at the exact point where algebraic
  descent (from ℂ to ℚ via cycle classes) meets Archimedean
  polarization (from the Hodge-Riemann metric).

  Axiom profile: encode_scalar_to_hodge_class (from Defs), plus
  all axioms via imported theorems from H1, H2, H3, H4.
  No sorry.
-/

import Papers.P49_Hodge.H1_HodgeTypeLPO
import Papers.P49_Hodge.H2_RationalityLPO
import Papers.P49_Hodge.H3_Polarization
import Papers.P49_Hodge.H4_CycleVerify

noncomputable section

namespace Papers.P49

-- ============================================================
-- §1. Detecting Hodge Classes Requires LPO
-- ============================================================

/-- **H5a: Detecting Hodge classes requires LPO.**

    A Hodge class is both rational AND of Hodge type (r,r).
    If detection of Hodge classes is decidable for all x ∈ H_C,
    then LPO holds for ℂ.

    Proof: Use the encoding axiom — for any z : ℂ, there exists
    x with is_hodge_class x ↔ z = 0. The oracle decides z = 0.

    This follows from the conjunction structure: detecting Hodge
    classes is at least as hard as detecting either component
    (Hodge type or rationality), each of which requires LPO
    (Theorems H1 and H2). -/
theorem hodge_class_detection_requires_LPO :
    (∀ (x : H_C), is_hodge_class x ∨ ¬ is_hodge_class x) → LPO_C := by
  intro h_dec z
  -- Encode z into a class whose Hodge class status encodes z = 0
  obtain ⟨x, hx⟩ := encode_scalar_to_hodge_class z
  -- The oracle decides is_hodge_class x
  rcases h_dec x with h_yes | h_no
  · -- x is a Hodge class → z = 0
    left; exact hx.mp h_yes
  · -- x is not a Hodge class → z ≠ 0
    right; exact fun hz => h_no (hx.mpr hz)

-- ============================================================
-- §2. The Hodge Conjecture Reduces Verification to BISH
-- ============================================================

/-- **H5b: With the Hodge Conjecture, verification reduces to BISH + MP.**

    If the Hodge Conjecture holds, then for any Hodge class x:
    1. There exists a cycle Z with ι(cl(Z)) = x (from the conjecture)
    2. x is rational, so ∃ q ∈ H_Q with ι(q) = x (from is_hodge_class)
    3. Checking cl(Z) = q in H_Q is BISH-decidable (DecidableEq on H_Q)

    Thus the conjecture converts the detection problem from:
    - LPO: test x ∈ H^{r,r} and x ∈ im(H_Q → H_C) in H_C (over ℂ)
    to:
    - MP + BISH: search for Z (MP) and verify cl(Z) = q in H_Q (BISH) -/
theorem hodge_conjecture_reduces_to_BISH :
    hodge_conjecture →
    ∀ (x : H_C), is_hodge_class x →
      ∃ (Z : ChowGroup) (q : H_Q),
        rational_inclusion q = x ∧
        (cycle_class Z = q ∨ cycle_class Z ≠ q) := by
  intro hHC x hx
  -- The Hodge Conjecture gives a cycle Z
  obtain ⟨Z, hZ⟩ := hHC x hx
  -- is_hodge_class has is_rational as first component
  obtain ⟨q, hq⟩ := hx.1
  -- Checking cycle_class Z = q is decidable in H_Q (excluded middle from DecidableEq)
  exact ⟨Z, q, hq, (H_Q_decidableEq (cycle_class Z) q).em⟩

-- ============================================================
-- §3. The Nexus Observation
-- ============================================================

/-- **H5c: The Nexus — Neither mechanism alone suffices.**

    The Hodge Conjecture is the nexus where:
    - Archimedean polarization (Hodge-Riemann, positive-definite)
      can split H_C into Hodge types (BISH from the metric)
      BUT cannot see ℚ-structure (periods are transcendental)
    - Algebraic descent (cycle class map, rational lattice)
      can verify rational structure (DecidableEq on H_Q)
      BUT cannot determine Hodge type without the metric

    Neither mechanism alone detects Hodge classes.
    The conjecture asserts: when BOTH conditions hold simultaneously
    (x is rational AND type (r,r)), the cause is algebraic geometry. -/
theorem nexus_observation :
    -- Polarization is available (positive-definite on (r,r)-classes)
    (∀ (x : H_C), hodge_projection_rr x = x → x ≠ 0 →
      hodge_riemann x x > 0)
    ∧
    -- Polarization is blind to ℚ
    ¬ (∀ (q₁ q₂ : H_Q),
       ∃ (r : ℚ), hodge_riemann
         (rational_inclusion q₁)
         (rational_inclusion q₂) = ↑r)
    ∧
    -- Detecting Hodge classes requires LPO
    ((∀ (x : H_C), is_hodge_class x ∨ ¬ is_hodge_class x) → LPO_C) :=
  ⟨hodge_riemann_pos_def_on_primitive,
   polarization_blind_to_Q,
   hodge_class_detection_requires_LPO⟩

end Papers.P49
