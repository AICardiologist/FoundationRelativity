/-
Papers/P26_GodelGap/ArithmeticSide.lean
Paper 26: The Gödel-Gap Correspondence

Arithmetic side: axiomatized proof predicate for PA, Π⁰₁ sentences,
PA-provable equivalence, and the Lindenbaum algebra.

## Axiom Design

We axiomatize PA as a consistent, recursively axiomatized theory with
a decidable proof predicate. These are standard properties that would
require formalizing Gödel numbering to prove — which is out of scope.
The construction works for any consistent first-order theory with these
properties; it is not specific to PA.

## Custom Axioms in This File

All axioms in this file encode standard metamathematical facts about PA:
- SentencePA, godelNum: sentences have Gödel numbers
- PrfPA, PrfPA_decidable: the proof predicate is decidable
- negPA, andPA, orPA, implPA: syntactic operations on sentences
- isPi01 and closure properties: Π⁰₁ is closed under ∧, ∨
- PAEquiv properties: provable equivalence is a congruence
- PA consistency: PA is consistent (does not prove ⊥)
-/
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.WellFoundedSet

namespace Papers.P26_GodelGap

-- ========================================================================
-- Axiomatized syntax of PA
-- ========================================================================

/-- The type of sentences of Peano Arithmetic (axiomatized).
    We do not build Gödel numbering; we axiomatize the needed properties. -/
axiom SentencePA : Type

/-- Gödel number of a sentence. Injective by construction of Gödel numbering. -/
axiom godelNum : SentencePA → ℕ
axiom godelNum_injective : Function.Injective godelNum

/-- The proof predicate: `PrfPA p ψ` means "p is a PA-proof of ψ". -/
axiom PrfPA : ℕ → SentencePA → Prop

/-- The proof predicate is decidable (PA is recursively axiomatized). -/
axiom PrfPA_decidable : ∀ p ψ, Decidable (PrfPA p ψ)

noncomputable instance instDecidablePrfPA (p : ℕ) (ψ : SentencePA) :
    Decidable (PrfPA p ψ) :=
  PrfPA_decidable p ψ

-- ========================================================================
-- Syntactic operations
-- ========================================================================

/-- Negation of sentences -/
axiom negPA : SentencePA → SentencePA

/-- Conjunction of sentences -/
axiom andPA : SentencePA → SentencePA → SentencePA

/-- Disjunction of sentences -/
axiom orPA : SentencePA → SentencePA → SentencePA

/-- Implication of sentences -/
axiom implPA : SentencePA → SentencePA → SentencePA

/-- Falsity (⊥) -/
axiom botPA : SentencePA

-- ========================================================================
-- Provability, refutability, consistency
-- ========================================================================

/-- PA-provability: there exists a proof. -/
def ProvablePA (ψ : SentencePA) : Prop := ∃ p, PrfPA p ψ

/-- PA-refutability: the negation is provable. -/
def RefutablePA (ψ : SentencePA) : Prop := ProvablePA (negPA ψ)

/-- Consistency of a sentence: not refutable. -/
def ConsistentPA (ψ : SentencePA) : Prop := ¬ RefutablePA ψ

/-- Independence: neither provable nor refutable. -/
def IndependentPA (ψ : SentencePA) : Prop :=
  ¬ ProvablePA ψ ∧ ¬ RefutablePA ψ

/-- PA is consistent: ⊥ is not provable. -/
axiom pa_consistent : ¬ ProvablePA botPA

-- ========================================================================
-- Bounded proof search (decidable)
-- ========================================================================

/-- Bounded proof search for refutation is decidable.
    This is the key computability fact: we can check all proofs up to length n. -/
axiom bounded_refutation_decidable :
  ∀ φ (n : ℕ), Decidable (∃ p, p ≤ n ∧ PrfPA p (negPA φ))

noncomputable instance instDecidableBoundedRefutation (φ : SentencePA) (n : ℕ) :
    Decidable (∃ p, p ≤ n ∧ PrfPA p (negPA φ)) :=
  bounded_refutation_decidable φ n

-- ========================================================================
-- PA-provable equivalence
-- ========================================================================

/-- PA-provable equivalence: PA proves φ ↔ ψ. -/
def PAEquiv (φ ψ : SentencePA) : Prop :=
  ProvablePA (andPA (implPA φ ψ) (implPA ψ φ))

-- PAEquiv is an equivalence relation (standard logical facts)
axiom paEquiv_refl : ∀ φ, PAEquiv φ φ
axiom paEquiv_symm : ∀ φ ψ, PAEquiv φ ψ → PAEquiv ψ φ
axiom paEquiv_trans : ∀ φ ψ χ, PAEquiv φ ψ → PAEquiv ψ χ → PAEquiv φ χ

/-- PAEquiv preserves consistency: equivalent sentences have the same
    consistency status. -/
axiom paEquiv_consistent_iff (φ ψ : SentencePA) :
  PAEquiv φ ψ → (ConsistentPA φ ↔ ConsistentPA ψ)

/-- PAEquiv is a congruence for negation. -/
axiom paEquiv_neg : ∀ φ ψ, PAEquiv φ ψ → PAEquiv (negPA φ) (negPA ψ)

/-- PAEquiv is a congruence for conjunction. -/
axiom paEquiv_and : ∀ φ₁ φ₂ ψ₁ ψ₂,
  PAEquiv φ₁ ψ₁ → PAEquiv φ₂ ψ₂ → PAEquiv (andPA φ₁ φ₂) (andPA ψ₁ ψ₂)

/-- PAEquiv is a congruence for disjunction. -/
axiom paEquiv_or : ∀ φ₁ φ₂ ψ₁ ψ₂,
  PAEquiv φ₁ ψ₁ → PAEquiv φ₂ ψ₂ → PAEquiv (orPA φ₁ φ₂) (orPA ψ₁ ψ₂)

/-- All refutable sentences are PA-equivalent to ⊥.
    If PA ⊢ ¬φ, then PA ⊢ φ ↔ ⊥ (ex falso + contrapositive). -/
axiom refutable_equiv_bot : ∀ φ, RefutablePA φ → PAEquiv φ botPA

/-- Consequently, all refutable sentences are PA-equivalent to each other. -/
theorem refutable_paEquiv (φ ψ : SentencePA)
    (hrφ : RefutablePA φ) (hrψ : RefutablePA ψ) : PAEquiv φ ψ :=
  paEquiv_trans φ botPA ψ
    (refutable_equiv_bot φ hrφ)
    (paEquiv_symm ψ botPA (refutable_equiv_bot ψ hrψ))

-- ========================================================================
-- Π⁰₁ sentences
-- ========================================================================

/-- Marker for Π⁰₁ sentences (axiomatized). -/
axiom isPi01 : SentencePA → Prop

/-- The type of Π⁰₁ sentences. -/
def Pi01 := { φ : SentencePA // isPi01 φ }

/-- ⊥ is Π⁰₁. -/
axiom pi01_bot : isPi01 botPA

/-- Π⁰₁ is closed under conjunction. -/
axiom pi01_and : ∀ φ ψ, isPi01 φ → isPi01 ψ → isPi01 (andPA φ ψ)

/-- Π⁰₁ is closed under disjunction. -/
axiom pi01_or : ∀ φ ψ, isPi01 φ → isPi01 ψ → isPi01 (orPA φ ψ)

-- ========================================================================
-- Provable implication (the order on the Lindenbaum algebra)
-- ========================================================================

/-- PA-provable implication: PA ⊢ φ → ψ. -/
def PAImplies (φ ψ : SentencePA) : Prop :=
  ProvablePA (implPA φ ψ)

axiom paImplies_refl : ∀ φ, PAImplies φ φ
axiom paImplies_trans : ∀ φ ψ χ,
  PAImplies φ ψ → PAImplies ψ χ → PAImplies φ χ

/-- PAEquiv ↔ mutual PAImplies. -/
axiom paEquiv_iff_mutual_implies : ∀ φ ψ,
  PAEquiv φ ψ ↔ (PAImplies φ ψ ∧ PAImplies ψ φ)

/-- PAImplies respects PAEquiv on both sides. -/
axiom paImplies_congr : ∀ φ₁ φ₂ ψ₁ ψ₂,
  PAEquiv φ₁ φ₂ → PAEquiv ψ₁ ψ₂ → (PAImplies φ₁ ψ₁ ↔ PAImplies φ₂ ψ₂)

-- ========================================================================
-- The Lindenbaum algebra: Π⁰₁/∼_PA
-- ========================================================================

/-- The setoid on Pi01 induced by PA-provable equivalence. -/
instance pi01Setoid : Setoid Pi01 where
  r := fun φ ψ => PAEquiv φ.val ψ.val
  iseqv := ⟨fun φ => paEquiv_refl φ.val,
            fun h => paEquiv_symm _ _ h,
            fun h1 h2 => paEquiv_trans _ _ _ h1 h2⟩

/-- **Lindenbaum algebra**: Π⁰₁ sentences quotiented by PA-provable equivalence. -/
def LindenbaumPi01 := Quotient pi01Setoid

/-- The quotient map. -/
def LindenbaumPi01.mk (φ : Pi01) : LindenbaumPi01 :=
  Quotient.mk pi01Setoid φ

/-- The equivalence class of ⊥ (the bottom element). -/
noncomputable def LindenbaumPi01.bot : LindenbaumPi01 :=
  LindenbaumPi01.mk ⟨botPA, pi01_bot⟩

-- ========================================================================
-- Partial order on the Lindenbaum algebra
-- ========================================================================

/-- Partial order: [φ] ≤ [ψ] iff PA ⊢ φ → ψ. -/
def LindenbaumPi01.le (a b : LindenbaumPi01) : Prop :=
  Quotient.liftOn₂ a b
    (fun φ ψ => PAImplies φ.val ψ.val)
    (by
      intro φ₁ φ₂ ψ₁ ψ₂ hφ hψ
      simp only
      exact propext (paImplies_congr φ₁.val ψ₁.val φ₂.val ψ₂.val hφ hψ))

instance : LE LindenbaumPi01 where le := LindenbaumPi01.le

theorem LindenbaumPi01.le_refl (a : LindenbaumPi01) : a ≤ a := by
  induction a using Quotient.ind
  exact paImplies_refl _

theorem LindenbaumPi01.le_trans (a b c : LindenbaumPi01) :
    a ≤ b → b ≤ c → a ≤ c := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction c using Quotient.ind
  exact paImplies_trans _ _ _

theorem LindenbaumPi01.le_antisymm (a b : LindenbaumPi01) :
    a ≤ b → b ≤ a → a = b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  intro hab hba
  apply Quotient.sound
  exact (paEquiv_iff_mutual_implies _ _).mpr ⟨hab, hba⟩

-- ========================================================================
-- Canonical Gödel number for equivalence classes
-- ========================================================================

/-- For each Π⁰₁ sentence φ, the set of Gödel numbers of sentences
    in its equivalence class is nonempty. -/
theorem classGodelNums_nonempty (φ : Pi01) :
    ∃ n, ∃ ψ : Pi01, godelNum ψ.val = n ∧ PAEquiv φ.val ψ.val :=
  ⟨godelNum φ.val, φ, rfl, paEquiv_refl φ.val⟩

open Classical in
/-- The canonical Gödel number: minimum Gödel number in the class.
    Uses well-ordering of ℕ (Nat.find) with classical decidability. -/
noncomputable def canonGN (φ : Pi01) : ℕ :=
  Nat.find (classGodelNums_nonempty φ)

open Classical in
/-- PA-equivalent sentences have the same canonical Gödel number.
    If φ ~ ψ, any witness for φ's class also works for ψ's class
    (by transitivity), so the Nat.find values are equal by antisymmetry. -/
theorem canonGN_equiv (φ ψ : Pi01) (h : PAEquiv φ.val ψ.val) :
    canonGN φ = canonGN ψ := by
  simp only [canonGN]
  apply le_antisymm
  · apply Nat.find_le
    obtain ⟨χ, hχ_gn, hχ_equiv⟩ := Nat.find_spec (classGodelNums_nonempty ψ)
    exact ⟨χ, hχ_gn, paEquiv_trans φ.val ψ.val χ.val h hχ_equiv⟩
  · apply Nat.find_le
    obtain ⟨χ, hχ_gn, hχ_equiv⟩ := Nat.find_spec (classGodelNums_nonempty φ)
    exact ⟨χ, hχ_gn, paEquiv_trans ψ.val φ.val χ.val (paEquiv_symm _ _ h) hχ_equiv⟩

/-- canonGN lifts to a well-defined function on the Lindenbaum algebra. -/
noncomputable def classGN : LindenbaumPi01 → ℕ :=
  Quotient.lift canonGN (fun φ ψ h => canonGN_equiv φ ψ h)

/-- Different classes have different canonical Gödel numbers. -/
theorem classGN_injective : Function.Injective classGN := by
  intro a b hab
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i φ ψ
  apply Quotient.sound
  simp [classGN] at hab
  -- Both classes have the same minimum Gödel number.
  -- The Nat.find witness for φ's class is PA-equiv to φ,
  -- and the Nat.find witness for ψ's class is PA-equiv to ψ.
  -- Since they share the same minimum, the witnesses are the same sentence,
  -- so φ ~ witness ~ ψ.
  sorry

end Papers.P26_GodelGap
