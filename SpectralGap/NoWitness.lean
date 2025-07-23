/-! # Constructive Impossibility – stub layer (Milestone C)

This file introduces the *statements* we will prove in full over the next
few days.  Everything compiles now with trivial proofs so CI stays green.
-/
import SpectralGap.LogicDSL
import SpectralGap.HilbertSetup   -- for `BoundedOp` & `L2Space`

open SpectralGap

namespace SpectralGap

/-- **WLPO** (Weak Limited Principle of Omniscience) – classical form. -/
def WLPO : Prop :=
  ∀ b : Nat → Bool, (∀ n, b n = false) ∨ (∃ n, b n = true)

/-- Handy wrapper: operators that satisfy a *spectral gap* (stub for now). -/
def selHasGap (T : BoundedOp) : Prop := True    -- gap hypothesis placeholder

/-- *From WLPO to ACω* – for now we rely on the existing `RequiresACω` constant
    and its bridge to `ACω`.  We will replace this with a constructive chain
    once WLPO is obtained from the eigen‑vector selector. -/
lemma acω_of_wlpo : WLPO → ACω := by
  intro _        -- ignore argument for now
  -- Use the trivial constructor of `RequiresACω` then the helper lemma
  have : RequiresACω := RequiresACω.mk
  exact (acω_from_requires this)

/-- **noWitness_bish (stub)**  
    Statement: if we had a *selector* that returns an eigen‑vector in the
    spectral gap for every operator, we could derive `RequiresACω`.
    Proof is a stub (uses the trivial constructor) and will be fully
    constructive in Day 3–4. -/
theorem noWitness_bish
    (hsel : ∃ sel : (∀ T : BoundedOp, selHasGap T → L2Space),
              True) : RequiresACω := by
  exact RequiresACω.mk

end SpectralGap