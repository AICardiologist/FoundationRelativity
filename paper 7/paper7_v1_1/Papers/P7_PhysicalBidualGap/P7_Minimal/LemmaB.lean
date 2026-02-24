/-
  P7_Minimal/LemmaB.lean
  Lemma B skeleton: reflexivity descends to closed subspaces.

  PROOF JUSTIFICATION:
  In P7_Full, this is `reflexive_closedSubspace_of_reflexive` in
  ReflexiveSubspace.lean (174 lines, zero sorry), proved using two
  applications of the Hahn-Banach theorem:
    Step 3: geometric_hahn_banach_closed_point (separation)
    Step 4: Real.exists_extension_norm_eq (norm-preserving extension)
  Here we axiomatize it to keep P7_Minimal Mathlib-free.
-/

import Papers.P7_PhysicalBidualGap.P7_Minimal.Defs

namespace P7_Minimal

/-- **Lemma B (abstract skeleton):** If X is reflexive and Y is a
    closed subspace of X, then Y is reflexive.

    Backed by: P7_Full/ReflexiveSubspace.lean (174 lines, zero sorry).
    Uses: geometric Hahn-Banach separation + norm-preserving extension.
    Constructively available for separable Banach spaces
    (Bridges-Vîță 2006, §4.3). -/
axiom reflexive_closedSubspace_of_reflexive
    (X Y : Type _) [ClosedSubspaceOf Y X] :
    IsReflexiveSpace X → IsReflexiveSpace Y

/-- **Contrapositive of Lemma B** (what we actually use in the
    reverse direction): If Y is a non-reflexive closed subspace of X,
    then X is not reflexive.

    This is a pure logical derivation — no axioms beyond Lemma B. -/
theorem not_reflexive_of_closedSubspace_not_reflexive
    (X Y : Type _) [ClosedSubspaceOf Y X]
    (hY : ¬ IsReflexiveSpace Y) : ¬ IsReflexiveSpace X :=
  fun hX => hY (reflexive_closedSubspace_of_reflexive X Y hX)

end P7_Minimal
