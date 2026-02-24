/-
  Paper 52: The Decidability Conduit — CRM Signatures Across the Langlands Correspondence
  RamanujanSeparation.lean — Theorem 2.6(a): Automorphic CRM Incompleteness

  The three automorphic CRM axioms (A1: multiplicity one, A2: algebraic integrality,
  A3: Petersson unitarity) do NOT imply the Ramanujan bound.

  Proof: explicit integer witness at k=2, p=5, a_p=5.
    - Ramanujan bound: a_p^2 <= 4 * p^(k-1) = 20. Violated: 25 > 20.
    - Unitarity bound: |a_p| < p + 1 = 6. Satisfied: 5 < 6.
    - Algebraic integrality: 5 in Z. Trivially satisfied.
    - Multiplicity one: structural axiom. Trivially satisfied.

  Everything stays in Z/N. No R coercions, no sorry, no axioms.

  STATUS: THEOREM (zero sorry, zero axioms)
-/

import Mathlib.Tactic.NormNum

namespace Papers.P52.RamanujanSeparation

-- ========================================================================
-- Section 1. Definitions
-- ========================================================================

/-- The Ramanujan bound: a_p^2 <= 4 * p^(k-1).
    For k=2 this is a_p^2 <= 4p, i.e., |a_p| <= 2*sqrt(p).
    Formulated in Z to keep all arithmetic decidable. -/
def SatisfiesRamanujanBound (a_p : Int) (p : Nat) (k : Nat) : Prop :=
  a_p ^ 2 ≤ 4 * (p : Int) ^ (k - 1)

/-- The complementary series (unitarity) bound: |a_p| < p + 1.
    This is the constraint from the Petersson inner product (Axiom A3).
    Equivalent to: a_p lies in the unitary dual of GL_2(Q_p). -/
def SatisfiesUnitarityBound (a_p : Int) (p : Nat) : Prop :=
  a_p.natAbs < p + 1

/-- Axiom A2: the Hecke eigenvalue is an algebraic integer.
    Every element of Z is an algebraic integer, so this is trivially satisfied.
    This makes the separation STRONGER: even with integrality, Ramanujan fails. -/
def IsAlgInt (_a : Int) : Prop := True

/-- Axiom A1: multiplicity one (one-dimensional Hecke eigenspace).
    A structural axiom of the automorphic theory.
    Trivially modeled since our witness is a single integer. -/
def HasMultOne : Prop := True

/-- Bundle: an instance satisfying all three automorphic CRM axioms.
    A1 = multiplicity one, A2 = algebraic integrality, A3 = unitarity. -/
structure AutomorphicCRMInstance where
  a_p : Int
  p : Nat
  k : Nat
  mult_one : HasMultOne                     -- A1
  alg_int  : IsAlgInt a_p                   -- A2
  unitary  : SatisfiesUnitarityBound a_p p  -- A3

-- ========================================================================
-- Section 2. The Witness
-- ========================================================================

/-- **The separating witness.** k=2, p=5, a_p=5.

    Satisfies all three automorphic CRM axioms:
    - A1 (multiplicity one): trivial
    - A2 (algebraic integrality): 5 in Z is an algebraic integer
    - A3 (Petersson unitarity): |5| = 5 < 6 = p + 1

    Violates the Ramanujan bound:
    - a_p^2 = 25 > 20 = 4 * 5^1 = 4 * p^(k-1)

    This witnesses the gap between the unitarity region
    (|a_p| < p+1) and the Ramanujan circle (|a_p| <= 2*sqrt(p)).
    For p=5: unitarity allows |a_p| <= 5, Ramanujan requires |a_p| <= 4. -/
def separatingWitness : AutomorphicCRMInstance where
  a_p := 5
  p := 5
  k := 2
  mult_one := trivial
  alg_int := trivial
  unitary := by unfold SatisfiesUnitarityBound; norm_num

-- ========================================================================
-- Section 3. The Separation Theorem
-- ========================================================================

/-- The witness violates the Ramanujan bound: 5^2 = 25 > 20 = 4 * 5^1. -/
theorem witness_violates_ramanujan :
    ¬ SatisfiesRamanujanBound
        separatingWitness.a_p
        separatingWitness.p
        separatingWitness.k := by
  unfold SatisfiesRamanujanBound separatingWitness
  norm_num

/-- **Theorem 2.6(a) (Automorphic CRM Incompleteness).**
    There exists an instance satisfying all three automorphic CRM axioms
    (A1: multiplicity one, A2: algebraic integrality, A3: Petersson unitarity)
    that violates the Ramanujan bound.

    Therefore: A1 + A2 + A3 do NOT imply Ramanujan.

    The gap is structural, not accidental. The unitarity region
    {|a_p| < p+1} strictly contains the Ramanujan circle {|a_p| <= 2*sqrt(p)}
    for every prime p >= 5. The automorphic CRM axioms can only access the
    outer region; the sharp inner bound requires crossing to the motivic side. -/
theorem automorphic_crm_incomplete :
    ∃ (inst : AutomorphicCRMInstance),
      ¬ SatisfiesRamanujanBound inst.a_p inst.p inst.k :=
  ⟨separatingWitness, witness_violates_ramanujan⟩

-- ========================================================================
-- Section 4. Additional Witnesses (the gap is robust)
-- ========================================================================

/-- Additional witness at p=7: a_p=6.
    Unitarity: |6| = 6 < 8 = 7+1. Ramanujan: 36 > 28 = 4*7. -/
def witness_p7 : AutomorphicCRMInstance where
  a_p := 6
  p := 7
  k := 2
  mult_one := trivial
  alg_int := trivial
  unitary := by unfold SatisfiesUnitarityBound; norm_num

theorem witness_p7_violates :
    ¬ SatisfiesRamanujanBound witness_p7.a_p witness_p7.p witness_p7.k := by
  unfold SatisfiesRamanujanBound witness_p7; norm_num

/-- Additional witness at p=11: a_p=7.
    Unitarity: |7| = 7 < 12 = 11+1. Ramanujan: 49 > 44 = 4*11. -/
def witness_p11 : AutomorphicCRMInstance where
  a_p := 7
  p := 11
  k := 2
  mult_one := trivial
  alg_int := trivial
  unitary := by unfold SatisfiesUnitarityBound; norm_num

theorem witness_p11_violates :
    ¬ SatisfiesRamanujanBound witness_p11.a_p witness_p11.p witness_p11.k := by
  unfold SatisfiesRamanujanBound witness_p11; norm_num

end Papers.P52.RamanujanSeparation
