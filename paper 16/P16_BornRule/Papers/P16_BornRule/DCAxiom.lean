/-
Papers/P16_BornRule/DCAxiom.lean
Paper 16: The Born Rule as a Logical Artefact.

Definition of Dependent Choice over ℕ (DC_ω) and its axiom.
Following the pattern of bmc_of_lpo in Papers 14-15.
-/
import Mathlib.Data.Complex.Basic

namespace Papers.P16

-- ========================================================================
-- Dependent Choice over ℕ
-- ========================================================================

/-- DC_ω: For any type α, any total binary relation R on α,
    and any starting point a₀, there exists an infinite chain
    a₀, a₁, a₂, ... with R(aₙ, aₙ₊₁) for all n.
    This is strictly weaker than full AC but stronger than countable choice. -/
def DC_omega : Prop :=
  ∀ (α : Type) (R : α → α → Prop) (a₀ : α),
    (∀ a, ∃ b, R a b) →
    ∃ f : ℕ → α, f 0 = a₀ ∧ ∀ n, R (f n) (f (n + 1))

/-- DC_ω holds (axiomatized — standard in classical mathematics,
    provable from AC, and the precise choice principle needed
    for the strong law of large numbers).
    Citing: Bridges & Vîță 2006, Bishop & Bridges 1985. -/
axiom dc_omega_holds : DC_omega

end Papers.P16
