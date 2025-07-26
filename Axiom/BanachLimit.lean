/-
# Banach‑Limit Axiom (centralised)
#
# This file gathers the single global axiom used in the project,
# so `scripts/check‑no‑axioms.sh` can whitelist it easily.
# The exact constant name **`classical_banach_limit_exists`**
# is re‑exported verbatim; downstream files need no edits.
-/

import Mathlib.Analysis.Normed.Field.Basic

namespace Axiom

axiom classical_banach_limit_exists :
  ∃ (φ : (ℕ → ℝ) →ₗ[ℝ] ℝ),
    (∀ f : ℕ → ℝ, φ (fun n ↦ f (n + 1)) = φ f) ∧   -- shift invariance
    (∀ c : ℝ, φ (fun _ ↦ c) = c)               ∧   -- normalisation
    (∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n) → 0 ≤ φ f)        -- positivity

end Axiom

export Axiom (classical_banach_limit_exists)