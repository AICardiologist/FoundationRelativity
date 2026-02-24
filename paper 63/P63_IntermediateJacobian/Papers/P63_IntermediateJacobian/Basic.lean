/-
  Paper 63: The Intermediate Jacobian Obstruction
  File 1/8: Basic types and constructive logic definitions

  This file establishes the foundational types shared across the
  formalization. Constructive principles (BISH, MP, LPO) follow
  the standard CRM definitions from Papers 60–62.
-/

import Mathlib.Tactic

namespace Paper63

-- ============================================================
-- Constructive Logic Principles
-- ============================================================

/-- Limited Principle of Omniscience: every binary sequence is
    identically zero or has a 1 somewhere. -/
def LPO : Prop :=
  ∀ (f : ℕ → Bool), (∀ n, f n = false) ∨ (∃ n, f n = true)

/-- Markov's Principle: if a binary sequence is not identically
    zero, then it has a 1 somewhere. -/
def MP : Prop :=
  ∀ (f : ℕ → Bool), ¬(∀ n, f n = false) → (∃ n, f n = true)

/-- LPO implies MP. Standard and easy. -/
theorem lpo_implies_mp : LPO → MP := by
  intro hlpo f hnot
  cases hlpo f with
  | inl hall => exact absurd hall hnot
  | inr hex => exact hex

-- BISH-decidability: a proposition is BISH-decidable if it is
-- decidable without any omniscience principle. In Lean, this
-- is simply `Decidable`.
-- (We use Lean's built-in Decidable typeclass for BISH.)

-- ============================================================
-- Hodge-Theoretic Data
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

/-- The Hodge level of a Hodge structure is the length of the
    Hodge filtration minus 1. Equivalently, max{|p - q| : h^{p,q} ≠ 0}.
    For our purposes: ℓ ≥ 2 iff h^{n,0} ≥ 1 where n = degree. -/
def HodgeData.hodgeLevel (hd : HodgeData) : ℕ :=
  hd.degree  -- This is the maximum possible; refined below

/-- The critical test: does h^{degree, 0} ≥ 1? -/
def HodgeData.hasTopHodgeNumber (hd : HodgeData) : Prop :=
  hd.h ⟨hd.degree, by omega⟩ ≥ 1

/-- The dimension of the intermediate Jacobian:
    g = Σ_{p > degree/2} h^{p, degree-p} -/
noncomputable def HodgeData.ijDim (hd : HodgeData) : ℕ :=
  Finset.sum (Finset.filter (fun p : Fin (hd.degree + 1) =>
    2 * p.val > hd.degree) Finset.univ) hd.h

-- ============================================================
-- Variety Data
-- ============================================================

/-- A smooth projective variety over ℚ with its Hodge data,
    together with claims about its intermediate Jacobian. -/
structure SmoothProjectiveData where
  /-- Name/label for the variety -/
  name : String
  /-- Dimension of the variety -/
  dim : ℕ
  /-- The relevant cohomological degree for the intermediate
      Jacobian (typically 2p-1 for CH^p) -/
  cohDegree : ℕ
  /-- Hodge data in the relevant degree -/
  hodge : HodgeData
  /-- Consistency: cohDegree matches -/
  degree_consistent : hodge.degree = cohDegree

end Paper63
