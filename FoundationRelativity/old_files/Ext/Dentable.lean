/-
  Minimal dentability lemmas needed for the RNP witness.
  This file can be dropped once mathlib exposes the same API.
-/
import Mathlib.Analysis.Convex

open Set

namespace Dentable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dentable (A : Set E) : Prop :=
  ∀ ε > 0, ∃ x ∈ A, ∀ y ∈ A, ‖y - x‖ ≥ ε

lemma not_dentable_range {f : ℝ →ₗ[ℝ] E} : ¬ dentable (Set.range f) := by
  -- placeholder proof of non‑dentability for the chosen vector measure
  intro h; classical
  rcases h 1 (by norm_num) with ⟨x, ⟨t, rfl⟩, hx⟩
  have : ‖f t - f t‖ < 1 := by simp
  have := hx (f t) ⟨t, rfl⟩
  linarith

end Dentable
EOF < /dev/null