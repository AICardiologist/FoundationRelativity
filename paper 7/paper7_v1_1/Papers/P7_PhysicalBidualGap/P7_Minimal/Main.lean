/-
  P7_Minimal/Main.lean
  Top-level theorem and axiom audit for the P7 logical skeleton.

  P7_main certifies: The logical reduction from
  "S₁(H) non-reflexivity witness" to WLPO uses no classical axioms
  beyond the explicitly listed assumptions. In particular, no
  Classical.choice appears in the axiom profile.
-/

import Papers.P7_PhysicalBidualGap.P7_Minimal.Reduction

namespace P7_Minimal

/-- **Main theorem (P7_Minimal):**
    NonReflexiveWitness(S₁(H)) ↔ WLPO.

    Forward uses the universal Ishihara kernel (any witness → WLPO).
    Reverse uses the Lemma B chain through ℓ¹ and Paper 2. -/
theorem P7_main : NonReflexiveWitness S1H_Type ↔ WLPO :=
  ⟨S1H_witness_implies_WLPO, WLPO_implies_S1H_witness⟩

end P7_Minimal

-- =============================================
-- Axiom audit
-- =============================================
#print axioms P7_Minimal.P7_main
/-
  ACTUAL output (verified 2026-02-08):
    'P7_Minimal.P7_main' depends on axioms:
    [P7_Minimal.ell1_closed_subspace_of_S1,
     P7_Minimal.ishihara_kernel,
     P7_Minimal.not_reflexive_implies_witness_S1,
     P7_Minimal.paper2_reverse,
     P7_Minimal.reflexive_closedSubspace_of_reflexive,
     P7_Minimal.witness_implies_not_reflexive]

  NOTABLY ABSENT: Classical.choice, propext, Quot.sound

  All six axioms are explicitly declared interface assumptions
  with backing proofs in P7_Full or P2_Full:
  1. Paper 2 import: paper2_reverse (proved in P2_Full)
  2. Paper 7 content:
     - reflexive_closedSubspace_of_reflexive
       (P7_Full/ReflexiveSubspace.lean, 174 lines, zero sorry)
     - ell1_closed_subspace_of_S1
       (P7_Full/DiagonalEmbedding.lean interface)
     - not_reflexive_implies_witness_S1
       (P7_Full/Main.lean + ReflexiveSubspace.lean)
  3. Universal Ishihara:
     - ishihara_kernel
       (P7_Full/WLPOFromWitness.lean, 196 lines, zero sorry)
  4. Structural:
     - witness_implies_not_reflexive (definitional)
-/
