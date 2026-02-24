/-
  Paper 62: The Hodge Level Boundary
  File 1/10: Basic types, constructive logic, and core definitions

  Merges Paper 63's foundational types (HodgeData, SmoothProjectiveData)
  with Paper 62's infrastructure (heights, Northcott, GradedCycleSpace).

  LPO/MP are defined in Bool form (primary) with ℤ-valued equivalents.

  Zero `sorry`s. No custom axioms in this file.
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Paper62

-- ============================================================
-- §1. Constructive Logic Principles
-- ============================================================

/-- Limited Principle of Omniscience: every binary sequence is
    identically false or has a true entry somewhere. -/
def LPO : Prop :=
  ∀ (f : ℕ → Bool), (∀ n, f n = false) ∨ (∃ n, f n = true)

/-- Markov's Principle: if a binary sequence is not identically
    false, then it has a true entry somewhere. -/
def MP : Prop :=
  ∀ (f : ℕ → Bool), ¬(∀ n, f n = false) → (∃ n, f n = true)

/-- LPO implies MP. Standard and easy. -/
theorem lpo_implies_mp : LPO → MP := by
  intro hlpo f hnot
  cases hlpo f with
  | inl hall => exact absurd hall hnot
  | inr hex => exact hex

-- ============================================================
-- §1b. Integer-Valued LPO (equivalent formulation)
-- ============================================================

/-- Integer-valued LPO: for any integer sequence, either all terms
    are zero or there exists a nonzero term. -/
def LPO_Z : Prop :=
  ∀ (f : ℕ → ℤ), (∀ n, f n = 0) ∨ (∃ n, f n ≠ 0)

/-- Integer-valued MP. -/
def MP_Z : Prop :=
  ∀ (f : ℕ → ℤ), ¬(∀ n, f n = 0) → ∃ n, f n ≠ 0

/-- Bool-valued LPO is equivalent to ℤ-valued LPO. -/
theorem lpo_iff_lpo_z : LPO ↔ LPO_Z := by
  constructor
  · -- Bool LPO → ℤ LPO
    intro hlpo f
    rcases hlpo (fun n => !decide (f n = 0)) with hall | ⟨n, hn⟩
    · left; intro n
      have := hall n
      simp at this
      exact this
    · right
      refine ⟨n, ?_⟩
      simp at hn
      exact hn
  · -- ℤ LPO → Bool LPO
    intro hlpo f
    rcases hlpo (fun n => if f n = true then (1 : ℤ) else 0) with hall | ⟨n, hn⟩
    · left; intro n
      have := hall n
      split_ifs at this with h
      · exact absurd this one_ne_zero
      · exact Bool.eq_false_iff.mpr h
    · right
      refine ⟨n, ?_⟩
      by_contra hne
      have hf : f n = false := Bool.eq_false_iff.mpr hne
      simp [hf] at hn

-- ============================================================
-- §2. Hodge-Theoretic Data
-- ============================================================

/-- Hodge numbers of a smooth projective variety in a given
    cohomological degree. -/
structure HodgeData where
  /-- Total cohomological degree (e.g., 3 for H³) -/
  degree : ℕ
  /-- Hodge numbers h^{p,q} with p + q = degree.
      Indexed by p, so h(p) = h^{p, degree - p}. -/
  h : Fin (degree + 1) → ℕ
  /-- Hodge symmetry: h^{p,q} = h^{q,p} -/
  symmetry : ∀ (p : Fin (degree + 1)),
    h p = h ⟨degree - p.val, by omega⟩

/-- The critical test: does h^{degree, 0} ≥ 1? -/
def HodgeData.hasTopHodgeNumber (hd : HodgeData) : Prop :=
  hd.h ⟨hd.degree, by omega⟩ ≥ 1

/-- The dimension of the intermediate Jacobian:
    g = Σ_{p > degree/2} h^{p, degree-p} -/
noncomputable def HodgeData.ijDim (hd : HodgeData) : ℕ :=
  Finset.sum (Finset.filter (fun p : Fin (hd.degree + 1) =>
    2 * p.val > hd.degree) Finset.univ) hd.h

-- ============================================================
-- §3. Variety Data
-- ============================================================

/-- A smooth projective variety over ℚ with its Hodge data. -/
structure SmoothProjectiveData where
  name : String
  dim : ℕ
  cohDegree : ℕ
  hodge : HodgeData
  degree_consistent : hodge.degree = cohDegree

-- ============================================================
-- §4. Height Functions and Northcott Property
-- ============================================================

/-- Abstract height function on a cycle group. -/
structure HeightFunction (α : Type*) where
  ht : α → ℚ
  ht_nonneg : ∀ x, 0 ≤ ht x

/-- The Northcott property: for any bound B, {x : ht(x) ≤ B} is finite. -/
structure NorthcottProperty (α : Type*) extends HeightFunction α where
  finite_bounded : ∀ (B : ℚ), ∃ (N : ℕ), ∀ (S : Finset α),
    (∀ x ∈ S, ht x ≤ B) → S.card ≤ N

/-- Northcott failure: bounded-height region is infinite. -/
def NorthcottFails (α : Type*) (h : HeightFunction α) : Prop :=
  ∃ (B : ℚ), ∀ (N : ℕ), ∃ (S : Finset α),
    (∀ x ∈ S, h.ht x ≤ B) ∧ S.card > N

-- ============================================================
-- §5. Abel-Jacobi Target Classification
-- ============================================================

/-- Classification of intermediate Jacobian targets. -/
inductive AJTarget where
  | abelianVariety
  | nonAlgebraic
  | noAJMap
  deriving DecidableEq, Repr

/-- Hodge number criterion: h^{3,0} = 0 → abelian; h^{3,0} ≥ 1 → non-algebraic. -/
def hodgeDeterminesTarget (h30 : ℕ) : AJTarget :=
  if h30 = 0 then AJTarget.abelianVariety
  else AJTarget.nonAlgebraic

-- ============================================================
-- §6. Hodge Level (on List form)
-- ============================================================

/-- Hodge level: max |p - q| among nonzero h^{p,q}.
    Input: list of triples (p, q, h^{p,q}). -/
def hodgeLevel (hodge_numbers : List (ℕ × ℕ × ℕ)) : ℕ :=
  hodge_numbers.foldl (fun acc ⟨p, q, h⟩ =>
    if h > 0 then max acc (if p ≥ q then p - q else q - p) else acc) 0

-- ============================================================
-- §7. Degree-Graded Cycle Spaces (for No Weak Northcott)
-- ============================================================

/-- A degree-graded cycle space: cycles indexed by degree d ∈ ℕ.
    Each degree-d slice is decidable (BISH). -/
structure GradedCycleSpace where
  inSpan : ℕ → Prop
  decidable_graded : ∀ d, Decidable (inSpan d)

/-- Lattice saturation: generators span the FULL lattice at ALL degrees. -/
def latticeSaturated (G : GradedCycleSpace) : Prop :=
  ∀ d, G.inSpan d

/-- Decidability of saturation expressed as a Prop. -/
def SaturationDecidable (G : GradedCycleSpace) : Prop :=
  latticeSaturated G ∨ ¬latticeSaturated G

end Paper62
