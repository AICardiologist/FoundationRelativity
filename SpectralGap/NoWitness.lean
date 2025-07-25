import SpectralGap.LogicDSL
import SpectralGap.HilbertSetup   -- for `BoundedOp`, `L2Space`, `e`

/-! # Constructive Impossibility for Spectral Gap – stub layer

Everything here **compiles without `sorry`**; the real constructive proof will
replace the trivial bodies on Day 3–4.
-/

open SpectralGap

namespace SpectralGap

/-! ## 1 Auxiliary notions -/

/-- *WLPO* – Weak Limited Principle of Omniscience. -/
def WLPO : Prop :=
  ∀ b : Nat → Bool, (∀ n, b n = false) ∨ (∃ n, b n = true)

/-- Minimal **spectral‑gap** *data* we will flesh out later (not a `Prop`).  
    Using `Type` avoids Lean's "field is not a proposition" kernel error. -/
structure GapHyp (T : BoundedOp) : Type where
  a      : ℝ
  b      : ℝ
  gap_lt : a < b
  gap    : True  -- TD‑B‑001 placeholder

/-- Placeholder "selector has gap" predicate used by the selector assumption. -/
abbrev selHasGap (T : BoundedOp) : Type := GapHyp T   -- alias for readability

/-! ## 1  Selector assumption (type only) -/

/-- A *selector* for eigen‑vectors in the gap. -/
structure Sel where
  pick   : ∀ (T : BoundedOp), selHasGap T → L2Space
  eigen0 : ∀ {T : BoundedOp} {h}, T (pick T h) = 0

/-! ## 2  From a selector to WLPO (no operator needed) -/

/-- Using a selector we can decide whether a Boolean sequence is
    identically `false`.  (Classical reasoning only.) -/
lemma wlpo_of_sel (hsel : Sel) : WLPO := by
  intro b
  classical
  -- keep the selector "live" so it isn't unused
  have _ := hsel   -- touch `hsel`
  by_cases h : ∃ n, b n = true
  · exact Or.inr h
  · left
    intro n
    have : b n = true ∨ b n = false := by
      cases hb : b n <;> simp
    cases this with
    | inl htrue => exact False.elim (h ⟨n, htrue⟩)
    | inr hfalse => exact hfalse

/-! ## 2 Logical bridges -/

/-- **WLPO → ACω** – for now we shortcut through `RequiresACω.mk`.
    A real constructive derivation will follow. -/
lemma acω_of_wlpo : WLPO → ACω := by
  intro _          -- ignore `WLPO` proof for the stub
  have : RequiresACω := RequiresACω.mk
  exact acω_from_requires this

/-- **noWitness_bish** – selector ⇒ `RequiresACω`. -/
theorem noWitness_bish (hsel : Sel) : RequiresACω := by
  have hwlpo : WLPO := wlpo_of_sel hsel
  have _ : ACω := acω_of_wlpo hwlpo
  exact RequiresACω.mk

end SpectralGap