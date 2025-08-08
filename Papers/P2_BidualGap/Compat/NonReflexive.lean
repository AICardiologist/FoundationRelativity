/-
  Papers/P2_BidualGap/Compat/NonReflexive.lean
  Compatibility layer for non-reflexive witnesses.

  This file exposes:
  * `NonReflexiveWitness 𝕂`    -- an existence proposition
  * `witness_to_BidualGap`     -- repackaging to `BidualGap`

  We intentionally do NOT register global instances here.
  Fill `c0_or_l1_witness` with the concrete math when ready.
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Group.Completeness
import Papers.P2_BidualGap.Basic

namespace Papers.P2.Compat
open Papers.P2

/-- Existence of a non-reflexive Banach space over `𝕂`. -/
def NonReflexiveWitness (𝕂 : Type*) [NontriviallyNormedField 𝕂] : Prop :=
  ∃ (X : Type*) (_ : NormedAddCommGroup X) (_ : NormedSpace 𝕂 X) (_ : CompleteSpace X),
    ¬ Function.Surjective (NormedSpace.inclusionInDoubleDual 𝕂 X)

/-- Repackage a real witness as `BidualGap`. -/
lemma witness_to_BidualGap (h : NonReflexiveWitness ℝ) : BidualGap := by
  rcases h with ⟨X, hX₁, hX₂, hX₃, hNot⟩
  exact ⟨X, hX₁, hX₂, hX₃, hNot⟩

/-- (Stub) A concrete witness: e.g. via `c₀` or `ℓ¹`.
    Fill this with the actual mathlib statement when available. -/
lemma c0_or_l1_witness : NonReflexiveWitness ℝ := by
  -- TODO: Provide the standard construction (professor's Option B).
  -- Suggested route:
  --   * Take `X := c0(ℕ, ℝ)` with sup norm.
  --   * Identify `X* = ℓ¹` and `X** = ℓ^∞`.
  --   * Exhibit an element of `ℓ^∞ \ image(c0)`; conclude `¬ surj`.
  sorry -- SORRY(P2-c0-witness)

end Papers.P2.Compat