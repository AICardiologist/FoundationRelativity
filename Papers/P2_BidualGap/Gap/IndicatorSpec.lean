/-
Papers/P2_BidualGap/Gap/IndicatorSpec.lean

§3.1 skeleton (pin‑safe): a spec-level notion that A ≡ B "mod c₀"
is defined to mean "A △ B is finite". We'll later replace the spec
with the real indicator/c₀ formulation and prove equivalence.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Papers.P2.Gap.BooleanSubLattice

variable (A B : Set ℕ)

/-- Symmetric difference. We spell it ourselves to stay pin‑friendly. -/
def symmDiff (A B : Set ℕ) : Set ℕ := (A \ B) ∪ (B \ A)

/-- "A and B differ only finitely many times." -/
def finiteSymmDiff (A B : Set ℕ) : Prop := (symmDiff A B).Finite

/-- Spec placeholder for "indicator equivalence mod c₀".  **Definitionally**
    equal to finite symmetric difference, so we get an `Iff.rfl` now and
    can swap the definition later without touching callers. -/
def indicatorEqModC0Spec (A B : Set ℕ) : Prop := finiteSymmDiff A B

@[simp] theorem indicatorEqModC0_spec_iff :
  indicatorEqModC0Spec A B ↔ finiteSymmDiff A B := Iff.rfl

/-! ## Exact symmetric difference formulas

These crisp identities make congruence proofs one-liners. -/

lemma symmDiff_union_right_eq (A B C : Set ℕ) :
    symmDiff (A ∪ C) (B ∪ C) = symmDiff A B \ C := by
  -- if x ∈ C both unions contain x → not in △; if x ∉ C, reduce to A △ B
  ext x; by_cases hC : x ∈ C <;> simp [symmDiff, hC]

lemma symmDiff_inter_right_eq (A B C : Set ℕ) :
    symmDiff (A ∩ C) (B ∩ C) = symmDiff A B ∩ C := by
  -- if x ∉ C both intersections miss x → not in △; if x ∈ C, reduce to A △ B
  ext x; by_cases hC : x ∈ C <;> simp [symmDiff, hC]

lemma symmDiff_compl_eq (A B : Set ℕ) :
    symmDiff (Aᶜ) (Bᶜ) = symmDiff A B := by
  ext x; simp only [symmDiff, Set.mem_union, Set.mem_diff, Set.mem_compl_iff]
  tauto

/-! ## Congruence lemmas for finite symmetric difference

These show the spec behaves well under ∪, ∩, and ᶜ with a fixed third set.
Pure set-theory, no analysis required. -/

/-- Finite symmetric difference is preserved by union with a fixed set on the right. -/
lemma indicatorEqModC0Spec.union_right
    {A B C : Set ℕ} (h : indicatorEqModC0Spec A B) :
    indicatorEqModC0Spec (A ∪ C) (B ∪ C) := by
  -- unfold to "finite symmDiff …"
  unfold indicatorEqModC0Spec finiteSymmDiff at h ⊢
  -- (symmDiff A B) \ C ⊆ symmDiff A B, so finite subset of finite
  rw [symmDiff_union_right_eq A B C]
  exact h.subset Set.diff_subset

/-- Finite symmetric difference is preserved by intersection with a fixed set on the right. -/
lemma indicatorEqModC0Spec.inter_right
    {A B C : Set ℕ} (h : indicatorEqModC0Spec A B) :
    indicatorEqModC0Spec (A ∩ C) (B ∩ C) := by
  unfold indicatorEqModC0Spec finiteSymmDiff at h ⊢
  -- (… ∩ C) is a subset of (…); use inter ⊆ left
  have : (symmDiff A B ∩ C).Finite := h.subset (by intro x hx; exact hx.1)
  simpa [symmDiff_inter_right_eq A B C] using this

/-- Finite symmetric difference is preserved by complement. -/
lemma indicatorEqModC0Spec.compl
    {A B : Set ℕ} (h : indicatorEqModC0Spec A B) :
    indicatorEqModC0Spec (Aᶜ) (Bᶜ) := by
  unfold indicatorEqModC0Spec finiteSymmDiff at h ⊢
  simpa [symmDiff_compl_eq A B] using h

/-! ## Left-hand congruence lemmas

Symmetric variants via commutativity. -/

lemma indicatorEqModC0Spec.union_left
    {A B C : Set ℕ} (h : indicatorEqModC0Spec A B) :
    indicatorEqModC0Spec (C ∪ A) (C ∪ B) := by
  simpa [Set.union_comm] using (indicatorEqModC0Spec.union_right (A:=A) (B:=B) (C:=C) h)

lemma indicatorEqModC0Spec.inter_left
    {A B C : Set ℕ} (h : indicatorEqModC0Spec A B) :
    indicatorEqModC0Spec (C ∩ A) (C ∩ B) := by
  simpa [Set.inter_comm] using (indicatorEqModC0Spec.inter_right (A:=A) (B:=B) (C:=C) h)

end Papers.P2.Gap.BooleanSubLattice