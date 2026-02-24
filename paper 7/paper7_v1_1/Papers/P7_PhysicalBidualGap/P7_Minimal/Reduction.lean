/-
  P7_Minimal/Reduction.lean
  The core logical reduction: NonReflexiveWitness(S₁(H)) ↔ WLPO.

  CRITICAL ASYMMETRY (see P7_Minimal_Agent_Instructions.md):

  Forward (NonReflexiveWitness(X) → WLPO):
    The Ishihara kernel construction works for ANY Banach space X.
    It is a universal result axiomatized here, backed by the 196-line
    proof in P7_Full/WLPOFromWitness.lean. It does NOT use Lemma B
    or ℓ¹ — it constructs WLPO directly from the witness.

  Reverse (WLPO → NonReflexiveWitness(S₁(H))):
    Chains through ℓ¹ via Lemma B:
      WLPO → witness(ℓ¹)            [Paper 2 reverse]
           → ¬Reflexive(ℓ¹)         [witness_implies_not_reflexive]
           → ¬Reflexive(S₁(H))      [Lemma B contrapositive]
           → witness(S₁(H))         [not_reflexive_implies_witness_S1]
-/

import Papers.P7_PhysicalBidualGap.P7_Minimal.Defs
import Papers.P7_PhysicalBidualGap.P7_Minimal.LemmaB

namespace P7_Minimal

-- =============================================
-- Interface assumptions (axioms with proof backing)
-- =============================================

/-- ℓ¹ embeds as a closed subspace of S₁(H).
    Witness: the diagonal embedding ι(λ) = Σ λₙ |eₙ⟩⟨eₙ|.
    Backed by: P7_Full/DiagonalEmbedding.lean (HasTraceClassContainer). -/
axiom ell1_closed_subspace_of_S1 : ClosedSubspaceOf ell1_Type S1H_Type

/-- Paper 2 reverse: WLPO → NonReflexiveWitness(ℓ¹).
    Backed by: P2_Full/WLPO_to_Gap_HB.lean (constructs G ∈ c₀** \ J(c₀),
    transfers to ℓ¹ via dual isometries). -/
axiom paper2_reverse : WLPO → NonReflexiveWitness ell1_Type

/-- Ishihara kernel (universal): For ANY space X, a non-reflexivity
    witness implies WLPO. This is the forward direction of the bidual
    gap equivalence, and it works for arbitrary X.

    Backed by: P7_Full/WLPOFromWitness.lean (196 lines, zero sorry).
    The proof constructs an Ishihara kernel from any Ψ ∈ X** \ J(X)
    and applies a purely constructive consumer to extract WLPO.
    The constructive consumer (WLPO_of_kernel) is purely intuitionistic;
    only the kernel construction uses classical reasoning. -/
axiom ishihara_kernel (X : Type _) : NonReflexiveWitness X → WLPO

/-- NonReflexiveWitness implies ¬IsReflexiveSpace.
    If there exists Ψ ∈ X** \ J(X), then J_X is not surjective.
    This is a structural/definitional fact. -/
axiom witness_implies_not_reflexive (X : Type _) :
  NonReflexiveWitness X → ¬ IsReflexiveSpace X

/-- For S₁(H): ¬IsReflexiveSpace implies NonReflexiveWitness.
    This is the non-trivial direction; in P7_Full it ultimately
    follows from: ℓ¹ not reflexive (Paper 2) → S₁(H) not reflexive
    (Lemma B contrapositive) → S₁(H) has a witness (by Hahn-Banach,
    failure of surjectivity gives a functional outside the range).
    Backed by: P7_Full/Main.lean + ReflexiveSubspace.lean. -/
axiom not_reflexive_implies_witness_S1 :
  ¬ IsReflexiveSpace S1H_Type → NonReflexiveWitness S1H_Type

-- Make the ClosedSubspaceOf instance available for typeclass resolution
attribute [instance] ell1_closed_subspace_of_S1

-- =============================================
-- THE REDUCTION
-- =============================================

/-- **Forward: NonReflexiveWitness(S₁(H)) → WLPO.**

    This is an IMMEDIATE application of the universal Ishihara kernel.
    The proof does not use Lemma B, ℓ¹, or any chain — it goes directly
    from the S₁(H) witness to WLPO.

    In P7_Full, this corresponds to `wlpo_of_traceClass_witness` (Main.lean)
    which calls `wlpo_of_nonreflexive_witness_proof` (WLPOFromWitness.lean). -/
theorem S1H_witness_implies_WLPO :
    NonReflexiveWitness S1H_Type → WLPO :=
  ishihara_kernel S1H_Type

/-- **Reverse: WLPO → NonReflexiveWitness(S₁(H)).**

    Chain:
      WLPO → witness(ℓ¹)         [Paper 2]
           → ¬Reflexive(ℓ¹)      [witness_implies_not_reflexive]
           → ¬Reflexive(S₁(H))   [Lemma B contrapositive]
           → witness(S₁(H))      [not_reflexive_implies_witness_S1]

    In P7_Full, this corresponds to `not_reflexive_of_contains_ell1` (Main.lean)
    which chains through Lemma B, Compat, and the ℓ¹ embedding. -/
theorem WLPO_implies_S1H_witness :
    WLPO → NonReflexiveWitness S1H_Type := by
  intro h_wlpo
  -- Step 1: WLPO → ℓ¹ has witness
  have h_ell1_witness := paper2_reverse h_wlpo
  -- Step 2: ℓ¹ witness → ℓ¹ not reflexive
  have h_ell1_not_ref := witness_implies_not_reflexive ell1_Type h_ell1_witness
  -- Step 3: ℓ¹ not reflexive → S₁(H) not reflexive (Lemma B contrapositive)
  have h_S1_not_ref : ¬ IsReflexiveSpace S1H_Type :=
    not_reflexive_of_closedSubspace_not_reflexive S1H_Type ell1_Type h_ell1_not_ref
  -- Step 4: S₁(H) not reflexive → S₁(H) has witness
  exact not_reflexive_implies_witness_S1 h_S1_not_ref

end P7_Minimal
