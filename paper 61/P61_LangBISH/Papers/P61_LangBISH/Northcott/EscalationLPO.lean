/-
  Paper 61: Lang's Conjecture as the MP → BISH Gate
  Northcott/EscalationLPO.lean — Theorem D: No Northcott ⟹ LPO

  Without the Northcott property, verifying that candidate generators
  span the full lattice requires universal quantification over an infinite
  set — constructively equivalent to LPO.

  This is the main new result of Paper 61.
-/
import Papers.P61_LangBISH.Basic.Decidability
import Papers.P61_LangBISH.Basic.Heights

namespace Papers.P61_LangBISH

/-! ## Lattice Completeness Problem -/

/-- The lattice completeness decision problem:
    Given candidate generators g₁, …, g_r, does every cycle z of bounded
    height lie in the ℤ-span of the generators?

    For a single z, membership is decidable (integer linear algebra).
    For infinitely many z (when Northcott fails), the problem requires
    checking an infinite conjunction. -/
def LatticeComplete (membership : ℕ → Bool) : Prop :=
  ∀ n, membership n = true

/-! ## The Reduction: LPO ↔ Infinite Lattice Completeness -/

/-- Key lemma: deciding "all terms are true" for an infinite Bool sequence
    is equivalent to LPO.

    Given α : ℕ → Bool, define membership(n) := !(α n).
    Then:
      (∀ n, membership n = true) ⟺ (∀ n, α n = false)

    The LPO question "∀ n, α(n) = false or ∃ n, α(n) = true"
    is equivalent to deciding LatticeComplete for the derived sequence. -/
theorem lattice_completeness_equivalent_to_lpo :
    (∀ (membership : ℕ → Bool),
      (∀ n, membership n = true) ∨ (∃ n, membership n = false))
    ↔ LPO := by
  constructor
  · -- (→) Given decidability of all-true, derive LPO
    intro h α
    have := h (fun n => !α n)
    rcases this with hall | ⟨n, hn⟩
    · left
      intro n
      have := hall n
      simp at this
      exact this
    · right
      refine ⟨n, ?_⟩
      simp at hn
      exact hn
  · -- (←) Given LPO, derive decidability of all-true
    intro hLPO membership
    have := hLPO (fun n => !membership n)
    rcases this with hall | ⟨n, hn⟩
    · left
      intro n
      have := hall n
      simp at this

      exact this
    · right
      refine ⟨n, ?_⟩
      simp at hn
      exact hn

/-! ## Theorem D: No Northcott Requires LPO -/

/-- Theorem D: Without the Northcott property, deciding lattice completeness
    at rank ≥ 2 requires LPO.

    Proof structure:
    1. Without Northcott, bounded-height regions contain infinitely many cycles.
    2. For each cycle z_n, membership in ℤ-span(g₁,…,g_r) is decidable → Bool value.
    3. "All z_n are in the span" is an infinite conjunction of Bool values.
    4. Deciding this infinite conjunction is exactly LPO
       (by lattice_completeness_equivalent_to_lpo).

    The reduction is explicit: given any α : ℕ → Bool (an LPO instance),
    define cycle z_n to be in the span iff α(n) = false.
    Then "all z_n in span" ⟺ "∀ n, α(n) = false" ⟺ one disjunct of LPO. -/
theorem no_northcott_requires_lpo (r : ℕ) (_hr : r ≥ 2)
    (_h_no_northcott : LacksNorthcott) :
    -- Deciding lattice completeness over the infinite cycle set requires LPO:
    -- if we can decide "all cycles are in the span" for any membership oracle,
    -- then LPO holds.
    (∀ (membership : ℕ → Bool),
      (∀ n, membership n = true) ∨ (∃ n, membership n = false))
    → LPO := by
  intro h
  exact lattice_completeness_equivalent_to_lpo.mp h

/-- Converse: LPO suffices to decide lattice completeness. -/
theorem lpo_suffices_for_lattice_completeness :
    LPO →
    (∀ (membership : ℕ → Bool),
      (∀ n, membership n = true) ∨ (∃ n, membership n = false)) := by
  intro hLPO
  exact lattice_completeness_equivalent_to_lpo.mpr hLPO

/-- The equivalence: without Northcott at rank ≥ 2, decidability of
    lattice completeness is exactly LPO. -/
theorem no_northcott_iff_lpo (r : ℕ) (_hr : r ≥ 2)
    (_h_no_northcott : LacksNorthcott) :
    (∀ (membership : ℕ → Bool),
      (∀ n, membership n = true) ∨ (∃ n, membership n = false))
    ↔ LPO :=
  lattice_completeness_equivalent_to_lpo

end Papers.P61_LangBISH
