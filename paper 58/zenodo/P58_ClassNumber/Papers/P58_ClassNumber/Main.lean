/-
  Paper 58: Class Number Correction for Exotic Weil Classes on CM Abelian Fourfolds
  Series: Constructive Reverse Mathematics and Arithmetic Geometry
  Author: Paul C.-K. Lee, February 2026

  Root module — imports all submodules.

  Summary:
    Papers 56–57 proved h = f (conductor) for CM abelian fourfolds with h_K = 1.
    Paper 58 extends to h_K > 1 with the corrected formula:

        h · Nm(𝔞) = f

    where 𝔞 is the Steinitz class of the Weil lattice, forced by the norm
    condition h = f/Nm(𝔞) ∈ Nm(K×).

    First test field: K = ℚ(√-5), h_K = 2, |Δ_K| = 20.

    Results:
    - f = 7:   non-free (Nm(𝔞)=2), h = 7/2,   G = [[28,14],[14,42]],     det = 980   ✓
    - f = 9:   free     (Nm(𝔞)=1), h = 9,      G = [[18,0],[0,90]],       det = 1620  ✓
    - f = 13:  inert    (no CM fourfold)
    - f = 19:  inert    (no CM fourfold)
    - f = 37:  inert    (no CM fourfold)
    - f = 61:  free     (Nm(𝔞)=1), h = 61,     G = [[122,0],[0,610]],     det = 74420 ✓
    - f = 79:  inert    (no CM fourfold)
    - f = 97:  inert    (no CM fourfold)
    - f = 163: non-free (Nm(𝔞)=2), h = 163/2,  G = [[652,326],[326,978]], det = 531380 ✓

    The topological volume det(G) = f²·|Δ_K| is an absolute invariant.
    The class group determines how this volume distributes between h and Nm(𝔞).

    Zero `sorry`s. Zero custom axioms.
-/
import Papers.P58_ClassNumber.Completeness

-- ========================================================================
-- Axiom audit
-- ========================================================================

-- Expected axioms: [propext, Classical.choice, Quot.sound]
-- These are Mathlib infrastructure only (ℝ construction, quotient types).
-- No custom axioms or principles (LPO, WLPO, MP) are used.

-- Core identity
#print axioms paper58_summary_K5

-- Gram matrix determinants
#print axioms gram_K5_f7_match
#print axioms gram_K5_f9_match
#print axioms gram_K5_f61_match
#print axioms gram_K5_f163_match

-- Norm obstruction (mod-5 descent)
#print axioms seven_not_rational_norm_K5
#print axioms onesixtythree_not_rational_norm_K5

-- Positive norm witnesses
#print axioms nine_is_norm_K5
#print axioms sixtyone_is_norm_K5
#print axioms seven_half_is_norm_K5
#print axioms onesixtythree_half_is_norm_K5

-- Inert classification
#print axioms thirteen_inert_K5
#print axioms nineteen_inert_K5
#print axioms thirtyseven_inert_K5
#print axioms seventynine_inert_K5
#print axioms ninetyseven_inert_K5

-- Steinitz forced
#print axioms steinitz_forced_nontrivial_K5_f7
#print axioms steinitz_forced_nontrivial_K5_f163

-- Template determinant identities (purely algebraic)
#print axioms gramFree_det
#print axioms gramNonFree_det
#print axioms gram_volume_invariant
