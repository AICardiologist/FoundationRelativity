/-
  Option B – Core (sorry-free, toolchain-agnostic)

  What this file does:
  --------------------
  • Declares two tiny typeclasses that capture the Option‑B contract.
    - HasNonzeroQuotFunctional X C0 : Prop
        "WLPO gives a nonzero continuous linear functional on the quotient X ⧸ C0."
    - QuotToGapBridge X C0 : Prop
        "From such a functional one can produce a bidual gap for X."

  • Proves the one-line combination theorem:
        [HasNonzeroQuotFunctional] [QuotToGapBridge] ⟹ GapX

  • Makes no assumptions about how X, C0 are modelled (you can later instantiate
    with your existing ℓ∞ and c₀). No sorries; no ultrafilters; no HB in this file.

  How to use:
  -----------
  1) For your concrete X := ℓ∞ and C0 := c₀-as-a-closed-submodule, provide:
     - an instance `[HasNonzeroQuotFunctional X C0]` (the WLPO output), AND
     - an instance `[QuotToGapBridge X C0]` (the analytic bridge, probably classical).

  2) Then `gap_of_optionB` gives you the bidual gap for X with no further edits.

  3) If you already have a lemma
       quotient_functional_to_bidual_gap :
         (∃ Φ : (X ⧸ C0) →L[ℝ] ℝ, Φ ≠ 0) → ∃ G : X**, G ∉ range(J),
     just wrap it as an instance of `QuotToGapBridge X C0`.
-/

import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Topology.Algebra.Module.Basic

open Classical

namespace Papers.P2_BidualGap.HB.OptionB

/-- We work over `ℝ` by default. -/
variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (C0 : Submodule ℝ X)

/-- The normed-space quotient `X ⧸ C0`. -/
abbrev Q := X ⧸ C0

/-- The quotient map `X →L[ℝ] X ⧸ C0`. -/
noncomputable
def qQuot : X →L[ℝ] Q X C0 := Submodule.mkQ C0

/-- The canonical embedding `J : X →L[ℝ] X**`. -/
noncomputable
def J : X →L[ℝ] ((X →L[ℝ] ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.evalCLM ℝ X

/-- "There is a bidual gap for `X`" (i.e. `J` is not surjective). -/
def GapX : Prop :=
  ∃ G : (X →L[ℝ] ℝ) →L[ℝ] ℝ, G ∉ Set.range (J X)

/-! ---------------------------------------------------------------------------
    OPTION‑B TYPECLASSES
    --------------------------------------------------------------------------- -/

/-- **WLPO output (packaged):** there exists a nonzero continuous linear functional
    on the quotient `X ⧸ C0`.  This is exactly the ingredient Option‑B asks WLPO to supply. -/
class HasNonzeroQuotFunctional : Prop where
  exists_nonzero : ∃ Φ : (Q X C0) →L[ℝ] ℝ, Φ ≠ 0

/-- **Analytic bridge (packaged):** from any nonzero functional on `X ⧸ C0`, build
    an element of `X**` that is *not* in the range of `J : X → X**`.  This is the
    functional-analytic heart of Option‑B; you can provide it classically (HB), or
    reuse your existing in‑repo lemma. -/
class QuotToGapBridge : Prop where
  from_nonzero :
    ∀ {Φ : (Q X C0) →L[ℝ] ℝ}, Φ ≠ 0 →
      ∃ G : (X →L[ℝ] ℝ) →L[ℝ] ℝ, G ∉ Set.range (J X)

/-! ---------------------------------------------------------------------------
    ONE‑LINE OPTION‑B THEOREM
    --------------------------------------------------------------------------- -/

/-- **Option‑B, Core**: if WLPO gives a nonzero quotient functional and you have
    the analytic bridge, then `X` has a bidual gap.  Sorry‑free. -/
theorem gap_of_optionB
  [HasNonzeroQuotFunctional X C0] [QuotToGapBridge X C0] :
  GapX X := by
  obtain ⟨Φ, hΦ⟩ := HasNonzeroQuotFunctional.exists_nonzero (X := X) (C0 := C0)
  obtain ⟨G, hG⟩ := QuotToGapBridge.from_nonzero (X := X) (C0 := C0) hΦ
  exact ⟨G, hG⟩

/-!
  Integration hints:

  • To recover your paper's result for `X = ℓ∞` and `C0 = c₀`, make a tiny file:

      namespace Papers.P2_BidualGap.HB.Instances

      -- Open your concrete ℓ∞ and c₀:
      -- abbrev Linf := …      -- your ℓ∞ type
      -- def C0 : Submodule ℝ Linf := … -- your closed c₀ submodule

      -- (1) WLPO output instance:
      noncomputable
      instance : OptionB.HasNonzeroQuotFunctional Linf C0 :=
      ⟨ by
          -- your WLPO construction of a nonzero Φ : (Linf ⧸ C0) →L[ℝ] ℝ
          -- `exact ⟨Φ, hΦ⟩`
          sorry ⟩

      -- (2) Analytic bridge instance (classical or by your in‑repo lemma):
      noncomputable
      instance : OptionB.QuotToGapBridge Linf C0 :=
      ⟨ by
          intro Φ hΦ
          -- If you already have a lemma in your repo like:
          --   quotient_functional_to_bidual_gap Φ hΦ : ∃ G, G ∉ Set.range (J Linf)
          -- then just:
          --   exact quotient_functional_to_bidual_gap Φ hΦ
          sorry ⟩

      -- (3) The gap is immediate:
      example : OptionB.GapX Linf := OptionB.gap_of_optionB (X := Linf) (C0 := C0)

      end Papers.P2_BidualGap.HB.Instances

  • No ultrafilters or Banach limits are required in this file. If your bridge
    instance uses Hahn–Banach, that lives in the instance file, not here.
-/

end Papers.P2_BidualGap.HB.OptionB