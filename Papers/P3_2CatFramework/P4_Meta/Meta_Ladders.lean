/-
  Papers/P4_Meta/Meta_Ladders.lean
  Height calculus (sorry-free).
-/
import Papers.P3_2CatFramework.P4_Meta.Meta_Signature
import Papers.P3_2CatFramework.P4_Meta.Meta_Witnesses

namespace Papers.P4Meta
open Papers.P4Meta

/-- Height of a proof of `φ` over `T`: 0 = already provable; succ = one extension step. -/
inductive ProofHeight : Theory → Formula → Nat → Prop where
  | base {T φ} : T.Provable φ → ProofHeight T φ 0
  | step {T φ n ψ} :
      ProofHeight T φ n →
      ProofHeight (Extend T ψ) φ (n+1)

attribute [simp] ProofHeight.base

/-- One-step monotonicity: extending by any `ψ` raises height by at most 1. -/
theorem height_monotonic (T : Theory) (ψ φ : Formula) {n : Nat} :
    ProofHeight T φ n → ProofHeight (Extend T ψ) φ (n+1) :=
  fun h => ProofHeight.step h

/-- Extension adds at most 1 to the minimal height (existential bound form). -/
theorem extend_height_bound (T : Theory) (ψ φ : Formula) {n : Nat} :
    ProofHeight T φ n → ∃ m, m ≤ n + 1 ∧ ProofHeight (Extend T ψ) φ m := by
  intro h
  refine ⟨n+1, Nat.le_refl _, ?_⟩
  exact ProofHeight.step h

end Papers.P4Meta