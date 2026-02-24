/-
  Paper 70: The Archimedean Principle — Ramanujan Asymmetry
  Automorphic CRM incompleteness: the automorphic axioms are too weak
  to recover the Ramanujan bound.

  The separating witness: a_p = 5, p = 5, k = 2.
    Unitarity: |5| = 5 < 6 = 5 + 1.  ✓
    Ramanujan: 5² = 25 > 20 = 4·5.    ✗

  Pure ℤ-arithmetic. Zero custom axioms.
  Reference: Paper 52 (original); Paper 70, Theorem 5.3.
-/
import Mathlib.Tactic.Linarith

-- ============================================================
-- Automorphic CRM Instance
-- ============================================================

/-- An automorphic CRM instance: Hecke eigenvalue a_p at prime p, weight k,
    satisfying the three automorphic CRM axioms:
    (A1) Strong Multiplicity One — satisfied by assumption
    (A2) Shimura algebraicity — a_p ∈ ℤ, satisfied by type
    (A3) Petersson/unitarity — |a_p| < p + 1

    The unitarity bound |a_p| < p + 1 is the strongest consequence
    of these three axioms alone. Kim–Sarnak improved to p^{7/64}
    but cannot reach Ramanujan. No improvement in twenty years. -/
structure AutomorphicCRMInstance where
  a_p : Int
  p   : Nat
  k   : Nat
  unitary : a_p.natAbs < p + 1

-- ============================================================
-- The Ramanujan bound
-- ============================================================

/-- The Ramanujan bound: a_p² ≤ 4·p^{k-1}.
    For weight k = 2: a_p² ≤ 4p.
    This is the sharp bound from the motivic side (Deligne 1974).
    The automorphic side alone cannot prove it. -/
def SatisfiesRamanujan (a_p : Int) (p k : Nat) : Prop :=
  a_p * a_p ≤ 4 * (p ^ (k - 1) : Int)

-- ============================================================
-- The separating witness
-- ============================================================

/-- The separating witness: a_p = 5, p = 5, k = 2.
    Unitarity: |5| = 5 < 6 = 5 + 1. ✓
    Ramanujan: 5² = 25 > 20 = 4·5.  ✗ -/
def separatingWitness : AutomorphicCRMInstance where
  a_p := 5
  p   := 5
  k   := 2
  unitary := by native_decide

/-- The witness violates the Ramanujan bound: 25 > 20. -/
theorem witness_violates_ramanujan :
    ¬ SatisfiesRamanujan 5 5 2 := by
  unfold SatisfiesRamanujan
  omega

-- ============================================================
-- Automorphic CRM Incompleteness
-- ============================================================

/-- **THEOREM (Automorphic CRM Incompleteness):**
    There exists an instance satisfying all three automorphic CRM axioms
    that violates the Ramanujan bound.

    This is the key asymmetry: the motivic side proves |α|² = q^w from
    a single axiom (Rosati). The automorphic side would need an infinite
    schema: unitarity of Sym^m(π) for all m.

    Deligne used exactly this strategy: he crossed to the motivic side
    because the automorphic side lacks sharp bounds (Deligne 1974).

    Pure ℤ-arithmetic. Zero custom axioms. -/
theorem automorphic_crm_incomplete :
    ∃ (inst : AutomorphicCRMInstance),
      ¬ SatisfiesRamanujan inst.a_p inst.p inst.k :=
  ⟨separatingWitness, witness_violates_ramanujan⟩

/-- **The gap is structural, not accidental.**
    The trivial unitarity bound exceeds Ramanujan for all p ≥ 2:
    (p+1)² = p² + 2p + 1 > 4p when (p-1)² > 0, i.e., p ≠ 1.
    So every prime admits a gap between unitarity and Ramanujan. -/
theorem unitary_exceeds_ramanujan (p : Nat) (hp : p ≥ 2) :
    (p + 1) * (p + 1) > 4 * p := by nlinarith

/-- For any prime p ≥ 5, we can construct a witness satisfying unitarity
    but violating Ramanujan (using a_p = p, k = 2).
    The bound p ≥ 5 ensures p² > 4p (equivalently, p > 4). -/
theorem witness_family (p : Nat) (hp : p ≥ 5) :
    (p : Int).natAbs < p + 1 ∧ ¬ SatisfiesRamanujan (p : Int) p 2 := by
  refine ⟨?_, ?_⟩
  · simp [Int.natAbs_natCast]
  · unfold SatisfiesRamanujan
    push_cast
    nlinarith
