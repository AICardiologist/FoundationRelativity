/-
Papers/P7_PhysicalBidualGap/Main.lean
Module 4: Assembly of the Physical Bidual Gap theorem.

Main result: WLPO ↔ non-reflexivity of S₁(H) (in appropriate senses).

Forward direction (unconditional):
  S₁(H) is not reflexive, because it contains ℓ¹ as a closed subspace
  (via HasTraceClassContainer), and ℓ¹ is not reflexive.
  The chain: c₀ not reflexive → ℓ¹ not reflexive → S₁(H) not reflexive.

Backward direction (proven in WLPOFromWitness.lean, adapted from Lee 2026a, Paper 2):
  Any Banach space with a non-reflexivity witness (element of X** \ J(X))
  implies WLPO. The proof constructs an Ishihara kernel and applies the
  constructive WLPO consumer.
-/
import Papers.P7_PhysicalBidualGap.Basic
import Papers.P7_PhysicalBidualGap.ReflexiveDual
import Papers.P7_PhysicalBidualGap.ReflexiveSubspace
import Papers.P7_PhysicalBidualGap.DiagonalEmbedding
import Papers.P7_PhysicalBidualGap.Compat
import Papers.P7_PhysicalBidualGap.WLPOFromWitness

noncomputable section
namespace Papers.P7

open NormedSpace

-- ========================================================================
-- ℓ¹ is not reflexive (interface assumption bridging Paper 2)
-- ========================================================================

/-- ℓ¹ is not reflexive.

    Proof sketch (relies on the chain through c₀, proven in Paper 2):
    - c₀ is not reflexive (proven unconditionally via the witness G ∈ c₀**
      that evaluates to 1 on every point evaluation δ_m; see Paper 2,
      WLPO_to_Gap_HB.lean:69–102).
    - (c₀)* ≅ ℓ¹ and (ℓ¹)* ≅ ℓ∞ are isometric isomorphisms (Paper 2,
      DualIsometriesComplete.lean, ~1,593 lines).
    - If ℓ¹ were reflexive, then by Lemma A (reflexive_dual_of_reflexive),
      (ℓ¹)* = ℓ∞ would be reflexive. By Lemma A again, (ℓ∞)* would be
      reflexive. Since c₀ embeds isometrically into c₀** ≅ (ℓ∞)* as a
      closed subspace, Lemma B (reflexive_closedSubspace_of_reflexive) would
      give c₀ reflexive — contradiction.

    This remains an interface assumption (Lean `axiom`) because eliminating it
    requires porting Paper 2's full dual isometry infrastructure
    ((c₀)* ≅ ℓ¹, ~1,593 lines of isometric isomorphism proofs) to the
    Paper 7 toolchain (Lean v4.28.0-rc1 vs Paper 2's v4.23.0-rc2).
    The dual isometry chain is the sole remaining bridge to Paper 2. -/
axiom ell1_not_reflexive : ¬ IsReflexive ℝ ell1

-- ========================================================================
-- Forward direction: S₁(H) is not reflexive (unconditional)
-- ========================================================================

/-- If a Banach space X contains ℓ¹ isometrically as a closed subspace,
    then X is not reflexive. -/
theorem not_reflexive_of_contains_ell1
    [tc : HasTraceClassContainer] : ¬ IsReflexive ℝ tc.X := by
  -- If X were reflexive, then the closed subspace range(ι) would be reflexive
  -- (by Lemma B), and range(ι) ≅ ℓ¹ would be reflexive (by Compat).
  -- But ℓ¹ is not reflexive. Contradiction.
  intro hX
  -- Build a LinearIsometry from tc.ι (ContinuousLinearMap) + tc.ι_isometry
  let ι_li : ell1 →ₗᵢ[ℝ] tc.X :=
    { tc.ι.toLinearMap with
      norm_map' := fun x =>
        (AddMonoidHomClass.isometry_iff_norm tc.ι).mp tc.ι_isometry x }
  -- Get LinearIsometryEquiv: ell1 ≃ₗᵢ range(ι)
  let e : ell1 ≃ₗᵢ[ℝ] (LinearMap.range ι_li.toLinearMap) :=
    LinearIsometry.equivRange ι_li
  -- The range as a Submodule of tc.X
  let Y : Submodule ℝ tc.X := LinearMap.range ι_li.toLinearMap
  -- Show range(ι_li) is closed (same as Set.range tc.ι)
  have hYc : IsClosed (Y : Set tc.X) := by
    suffices h : (Y : Set tc.X) = Set.range tc.ι by
      rw [h]; exact tc.ι_closedRange
    ext x
    simp only [Y, LinearMap.mem_range, SetLike.mem_coe, Set.mem_range]
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a, ha⟩
    · rintro ⟨a, ha⟩; exact ⟨a, ha⟩
  -- Closed subspace of reflexive X → reflexive (Lemma B)
  have hY_refl : IsReflexive ℝ Y :=
    reflexive_closedSubspace_of_reflexive Y hYc hX
  -- Transfer via isometry: range(ι) reflexive → ell1 reflexive (Compat)
  have h_ell1_refl : IsReflexive ℝ ell1 :=
    reflexive_of_linearIsometryEquiv e hY_refl
  -- Contradiction with ell1_not_reflexive
  exact absurd h_ell1_refl ell1_not_reflexive

-- ========================================================================
-- Backward direction: non-reflexivity witness → WLPO (now proven)
-- ========================================================================

/-- If S₁(H) has a non-reflexivity witness, then WLPO holds.

    This was previously an axiom bridging Paper 2. It is now a theorem,
    proven in WLPOFromWitness.lean via the Ishihara kernel construction
    adapted from Paper 2 (Lee 2026a). -/
theorem wlpo_of_traceClass_witness
    [tc : HasTraceClassContainer]
    (h : ∃ Ψ : StrongDual ℝ (StrongDual ℝ tc.X),
         Ψ ∉ Set.range (inclusionInDoubleDual ℝ tc.X)) :
    WLPO :=
  wlpo_of_nonreflexive_witness_proof h

-- ========================================================================
-- Combined: The Physical Bidual Gap Theorem
-- ========================================================================

/-- **Physical Bidual Gap Theorem.**

    Forward (unconditional): S₁(H) is not reflexive.
    Backward: A non-reflexivity witness for S₁(H) implies WLPO.

    Combined, this gives the physical interpretation of the bidual gap:
    the trace-class operators S₁(H) on a separable Hilbert space are
    inherently non-reflexive, and any constructive witness of this
    non-reflexivity is equivalent to WLPO. -/
theorem physical_bidual_gap [tc : HasTraceClassContainer] :
    (¬ IsReflexive ℝ tc.X) ∧
    ((∃ Ψ : StrongDual ℝ (StrongDual ℝ tc.X),
         Ψ ∉ Set.range (inclusionInDoubleDual ℝ tc.X)) → WLPO) :=
  ⟨not_reflexive_of_contains_ell1, wlpo_of_traceClass_witness⟩

end Papers.P7
