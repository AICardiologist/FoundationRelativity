/-
  Paper 62: The Northcott Boundary — Hodge Level and the MP/LPO Frontier
  Defs.lean — Core definitions: decidability principles, Northcott property,
              Hodge level, Abel-Jacobi target classification

  Zero `sorry`s. Zero custom axioms in this file.
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace P62

-- ============================================================================
-- §1. Decidability Principles (self-contained, no Paper 61 dependency)
-- ============================================================================

/-- The Limited Principle of Omniscience (LPO):
    For any integer-valued sequence, either all terms are zero
    or there exists a nonzero term. -/
def LPO : Prop :=
  ∀ (f : ℕ → ℤ), (∀ n, f n = 0) ∨ (∃ n, f n ≠ 0)

/-- Markov's Principle (MP):
    If it is impossible that no witness exists, then a witness exists.
    Weaker than LPO: MP follows from LPO but not conversely. -/
def MP : Prop :=
  ∀ (f : ℕ → ℤ), ¬(∀ n, f n = 0) → ∃ n, f n ≠ 0

/-- LPO implies MP: the stronger principle subsumes the weaker. -/
theorem lpo_implies_mp : LPO → MP := by
  intro hlpo f hne
  rcases hlpo f with h | ⟨n, hn⟩
  · exact absurd h hne
  · exact ⟨n, hn⟩

/-- BISH decidability: a bounded search suffices.
    For a decidable predicate with a computable bound,
    the search is constructively valid (no omniscience needed). -/
def BISHDecidable (P : ℕ → Prop) [DecidablePred P] : Prop :=
  ∃ B : ℕ, ∀ n, P n → n ≤ B

-- ============================================================================
-- §2. Height Functions and the Northcott Property
-- ============================================================================

/-- Abstract height function on a cycle group.
    In practice: Néron-Tate height on an abelian variety,
    or Beilinson-Bloch height on a Chow group. -/
structure HeightFunction (α : Type*) where
  /-- The height of an element (rational-valued) -/
  ht : α → ℚ
  /-- Height is non-negative -/
  ht_nonneg : ∀ x, 0 ≤ ht x

/-- The Northcott property: for any bound B, the set {x : ht(x) ≤ B} is finite.
    This is the key finiteness condition enabling decidable enumeration. -/
structure NorthcottProperty (α : Type*) extends HeightFunction α where
  /-- For any height bound, bounded-height elements form a finite set -/
  finite_bounded : ∀ (B : ℚ), ∃ (N : ℕ), ∀ (S : Finset α),
    (∀ x ∈ S, ht x ≤ B) → S.card ≤ N

/-- Northcott FAILURE: there exists a height bound B such that
    for any proposed finite count N, there are more than N elements
    of height ≤ B. The bounded-height region is infinite. -/
def NorthcottFails (α : Type*) (h : HeightFunction α) : Prop :=
  ∃ (B : ℚ), ∀ (N : ℕ), ∃ (S : Finset α),
    (∀ x ∈ S, h.ht x ≤ B) ∧ S.card > N

-- ============================================================================
-- §3. Abel-Jacobi Target Classification
-- ============================================================================

/-- Classification of intermediate Jacobian targets.
    The algebraicity of J^k(X) determines the constructive complexity. -/
inductive AJTarget where
  /-- J^k(X) is an abelian variety: algebraic polarization exists.
      Néron-Tate height is positive-definite. Northcott holds. -/
  | abelianVariety
  /-- J^k(X) is a complex torus but NOT an abelian variety.
      No algebraic polarization. Periods are transcendental. -/
  | nonAlgebraic
  /-- No well-defined Abel-Jacobi map (higher K-theory, etc.) -/
  | noAJMap
  deriving DecidableEq, Repr

/-- Hodge number criterion: h^{3,0} = 0 implies abelian variety target;
    h^{3,0} ≥ 1 implies non-algebraic complex torus.
    Reference: Griffiths (1968), Griffiths-Harris Ch. 3. -/
def hodgeDeterminesTarget (h30 : ℕ) : AJTarget :=
  if h30 = 0 then AJTarget.abelianVariety
  else AJTarget.nonAlgebraic

-- ============================================================================
-- §4. Hodge Level
-- ============================================================================

/-- Hodge level of a Hodge structure: max |p - q| among nonzero h^{p,q}.
    Input: list of triples (p, q, h^{p,q}).
    Reference: Definition 1.2 of the paper. -/
def hodgeLevel (hodge_numbers : List (ℕ × ℕ × ℕ)) : ℕ :=
  hodge_numbers.foldl (fun acc ⟨p, q, h⟩ =>
    if h > 0 then max acc (if p ≥ q then p - q else q - p) else acc) 0

-- ============================================================================
-- §5. Degree-Graded Cycle Spaces
-- ============================================================================

/-- A degree-graded cycle space: cycles indexed by degree d ∈ ℕ.
    Each degree-d slice is a finite-dimensional variety (Chow variety). -/
structure GradedCycleSpace where
  /-- Decidable membership in ℤ-span of generators, for each degree -/
  inSpan : ℕ → Prop
  /-- Each graded piece is decidable (BISH) -/
  decidable_graded : ∀ d, Decidable (inSpan d)

/-- Lattice saturation: generators span the FULL lattice at ALL degrees.
    This is the ∀d ∈ ℕ quantification that causes LPO. -/
def latticeSaturated (G : GradedCycleSpace) : Prop :=
  ∀ d, G.inSpan d

end P62
