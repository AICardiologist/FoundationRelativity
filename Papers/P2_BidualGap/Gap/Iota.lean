/-
Papers/P2_BidualGap/Gap/Iota.lean
§3.2/3.4/3.5: the indicator embedding ι, injectivity (mod c₀-spec),
and lattice-homomorphism identities for χ (union/intersection/complement).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Papers.P2_BidualGap.Gap.Indicator
import Papers.P2_BidualGap.Gap.IndicatorSpec
import Papers.P2_BidualGap.Gap.IndicatorEventual
import Papers.P2_BidualGap.Gap.C0Spec

namespace Papers.P2.Gap.BooleanSubLattice
open Classical

/-- Our embedding is literally `χ`. We just give it the name `ι` for the paper narrative. -/
noncomputable abbrev ι (A : Set ℕ) : ℕ → ℝ := χ A

@[simp] lemma iota_def (A : Set ℕ) : ι A = χ A := rfl

/-- Equality modulo c₀-spec for sequences. -/
def EqModC0Spec (f g : ℕ → ℝ) : Prop := c0Spec (fun n => f n - g n)

notation:50 f " ≈₀ " g => EqModC0Spec f g

/-- Bridge: `ι A ≈₀ ι B` iff the symmetric difference is finite (the §3.1 equivalence). -/
lemma iota_eq_iff_spec (A B : Set ℕ) :
    EqModC0Spec (ι A) (ι B) ↔ indicatorEqModC0Spec A B := by
  -- `ι` is `χ`, and your §3.1 theorem does the rest.
  simp [EqModC0Spec, iota_def]
  exact (indicatorEqModC0_spec_iff_c0Spec A B).symm

/-- "Injectivity mod c₀": if `ι A` and `ι B` are c₀-spec equal, then
    `A` and `B` are equal mod finite symmetric difference. -/
lemma iota_injective_mod {A B : Set ℕ} :
    EqModC0Spec (ι A) (ι B) → indicatorEqModC0Spec A B :=
  (iota_eq_iff_spec A B).1

/-- Conversely, finite symmetric difference implies `ι A ≈₀ ι B`. -/
lemma spec_implies_iota_eq {A B : Set ℕ} :
    indicatorEqModC0Spec A B → EqModC0Spec (ι A) (ι B) :=
  (iota_eq_iff_spec A B).2

/-! ## Lattice homomorphism laws for χ (hence for ι)
These hold *as equalities of functions*, so they also hold modulo c₀-spec. -/

@[simp] lemma chi_empty : χ (∅ : Set ℕ) = fun _ => (0 : ℝ) := by
  funext n; simp [χ]

@[simp] lemma chi_univ : χ (Set.univ : Set ℕ) = fun _ => (1 : ℝ) := by
  funext n; simp [χ]

@[simp] lemma chi_compl (A : Set ℕ) :
    χ (Aᶜ) = fun n => 1 - χ A n := by
  funext n; by_cases h : n ∈ A <;> simp [χ, h]

@[simp] lemma chi_union (A B : Set ℕ) :
    χ (A ∪ B) = fun n => max (χ A n) (χ B n) := by
  funext n
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp [χ, hA, hB]

@[simp] lemma chi_inter (A B : Set ℕ) :
    χ (A ∩ B) = fun n => min (χ A n) (χ B n) := by
  funext n
  by_cases hA : n ∈ A <;> by_cases hB : n ∈ B <;> simp [χ, hA, hB]

/-- (Optional) A nice identity you already used implicitly:
    the absolute indicator difference is the indicator of `A △ B`. -/
lemma abs_chi_diff_eq_chi_symmDiff (A B : Set ℕ) :
    (fun n => |χ A n - χ B n|) = χ (symmDiff A B) := by
  funext n
  classical
  -- you had: `abs_indicator_diff_eq` as an `ite`; this packages it as `χ`.
  have := abs_indicator_diff_eq A B n
  -- rewrite `ite` as χ of the set:
  by_cases h : n ∈ symmDiff A B
  · simpa [this, χ, h]
  · simpa [this, χ, h]

/-! ### "Lattice homomorphism" modulo c₀
Because the equalities above are pointwise, the corresponding c₀-spec equalities are immediate. -/
lemma iota_union_hom (A B : Set ℕ) :
    ι (A ∪ B) ≈₀ (fun n => max (ι A n) (ι B n)) := by
  change c0Spec (fun n => (χ (A ∪ B) n - max (χ A n) (χ B n)))
  -- pointwise equality ⇒ tail is 0
  have : (fun n => χ (A ∪ B) n - max (χ A n) (χ B n)) = (fun _ => 0) := by
    funext n; simp [chi_union]
  -- tails of 0 are ≤ ε
  intro ε hε; refine ⟨0, ?_⟩; intro n hn; simp; exact hε.le

lemma iota_inter_hom (A B : Set ℕ) :
    ι (A ∩ B) ≈₀ (fun n => min (ι A n) (ι B n)) := by
  -- identical proof pattern
  change c0Spec (fun n => χ (A ∩ B) n - min (χ A n) (χ B n))
  have : (fun n => χ (A ∩ B) n - min (χ A n) (χ B n)) = (fun _ => 0) := by
    funext n; simp [chi_inter]
  intro ε hε; refine ⟨0, ?_⟩; intro n hn; simp; exact hε.le

lemma iota_compl_hom (A : Set ℕ) :
    ι (Aᶜ) ≈₀ (fun n => 1 - ι A n) := by
  change c0Spec (fun n => χ (Aᶜ) n - (1 - χ A n))
  have : (fun n => χ (Aᶜ) n - (1 - χ A n)) = (fun _ => 0) := by
    funext n; simp [chi_compl]
  intro ε hε; refine ⟨0, ?_⟩; intro n hn; simp; exact hε.le

/-! ## Congruence lemmas lifted to ι

These are instant via the §3.1 bridge: spec congruence ⇔ ι congruence. -/

lemma iota_union_congr_right {A B C : Set ℕ}
    (h : EqModC0Spec (ι A) (ι B)) :
    EqModC0Spec (ι (A ∪ C)) (ι (B ∪ C)) := by
  -- unwrap to spec, use union_right, rewrap
  have hs : indicatorEqModC0Spec A B := (iota_eq_iff_spec A B).1 h
  exact (iota_eq_iff_spec (A ∪ C) (B ∪ C)).2 (hs.union_right)

lemma iota_inter_congr_right {A B C : Set ℕ}
    (h : EqModC0Spec (ι A) (ι B)) :
    EqModC0Spec (ι (A ∩ C)) (ι (B ∩ C)) := by
  have hs : indicatorEqModC0Spec A B := (iota_eq_iff_spec A B).1 h
  exact (iota_eq_iff_spec (A ∩ C) (B ∩ C)).2 (hs.inter_right)

lemma iota_compl_congr {A B : Set ℕ}
    (h : EqModC0Spec (ι A) (ι B)) :
    EqModC0Spec (ι (Aᶜ)) (ι (Bᶜ)) := by
  have hs : indicatorEqModC0Spec A B := (iota_eq_iff_spec A B).1 h
  exact (iota_eq_iff_spec (Aᶜ) (Bᶜ)).2 (hs.compl)

/-! ## Left-hand congruence lemmas lifted to ι

Symmetric variants via commutativity. -/

lemma iota_union_congr_left {A B C : Set ℕ}
    (h : EqModC0Spec (ι A) (ι B)) :
    EqModC0Spec (ι (C ∪ A)) (ι (C ∪ B)) := by
  simpa [Set.union_comm] using iota_union_congr_right (A:=A) (B:=B) (C:=C) h

lemma iota_inter_congr_left {A B C : Set ℕ}
    (h : EqModC0Spec (ι A) (ι B)) :
    EqModC0Spec (ι (C ∩ A)) (ι (C ∩ B)) := by
  simpa [Set.inter_comm] using iota_inter_congr_right (A:=A) (B:=B) (C:=C) h

end Papers.P2.Gap.BooleanSubLattice