/-
  Paper 20: WLPO Equivalence via Ising Magnetization Phase Classification
  Defs/WLPO.lean — WLPO and LPO definitions, hierarchy

  Self-contained definitions (no inter-paper imports).
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Real.Basic

namespace Papers.P20

/-! ## Omniscience Principles -/

/-- The Limited Principle of Omniscience (LPO):
    For every binary sequence, either all terms are false,
    or there exists a term that is true. -/
def LPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- The Weak Limited Principle of Omniscience (WLPO):
    For every binary sequence, either all terms are false,
    or it is not the case that all terms are false. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-! ## Hierarchy -/

/-- LPO implies WLPO: if we can find a witness, we certainly know
    the sequence is not all-false. -/
theorem lpo_implies_wlpo : LPO → WLPO := by
  intro hLPO α
  rcases hLPO α with h | ⟨n, hn⟩
  · left; exact h
  · right; intro hall; exact absurd (hall n) (by simp [hn])

end Papers.P20
