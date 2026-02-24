/-
  Paper 55: Is Gödel Absent from the Motive?
  Defs.lean — Core definitions

  Defines the logical architecture for analyzing the meta-mathematical
  status of Standard Conjecture D:

  1. ArithmeticSentence: a sentence in the arithmetical hierarchy
     (has a definite truth value in ℕ, quantifies only over ℕ)
  2. Pi02Sentence: a Π₂⁰ sentence (∀n ∃m R(n,m) with R decidable)
  3. FormalSystem: an axiom system (ZFC, PA, etc.)
  4. Two modes of independence: Cohen vs Gödel
  5. ConjD_Data: the logical form of Conjecture D

  We do NOT formalize algebraic geometry here. The geometric content
  (cycles, cohomology, intersection numbers) is axiomatized as
  hypotheses following the Paper 51 pattern.
-/
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic

namespace Papers.P55

-- ========================================================================
-- Arithmetical Hierarchy (Abstract)
-- ========================================================================

/-- A sentence in first-order arithmetic: has a definite truth value
    and quantifies only over ℕ. We model this abstractly as a Prop
    tagged with its complexity class. -/
structure ArithSentence where
  /-- The proposition asserted by the sentence. -/
  statement : Prop

/-- A Π₂⁰ sentence: of the form ∀n, ∃m, R(n,m) where R is decidable.
    This is the key complexity class for Conjecture D.

    We store the witness relation R and its decidability, plus the
    proposition that the Π₂⁰ form holds. -/
structure Pi02Sentence extends ArithSentence where
  /-- The decidable relation R(n,m). -/
  R : ℕ → ℕ → Prop
  /-- R is decidable. -/
  R_dec : DecidablePred (fun p : ℕ × ℕ => R p.1 p.2)
  /-- The statement is equivalent to ∀n, ∃m, R(n,m). -/
  equiv_pi02 : statement ↔ ∀ n, ∃ m, R n m

/-- A Π₁⁰ sentence: of the form ∀n, R(n) where R is decidable.
    Strictly simpler than Π₂⁰. Con(ZFC) has this form. -/
structure Pi01Sentence extends ArithSentence where
  /-- The decidable predicate R(n). -/
  R : ℕ → Prop
  /-- R is decidable. -/
  R_dec : DecidablePred R
  /-- The statement is equivalent to ∀n, R(n). -/
  equiv_pi01 : statement ↔ ∀ n, R n

/-- Every Π₁⁰ sentence is also Π₂⁰ (by taking the trivial ∃m). -/
def Pi01Sentence.toPi02 (φ : Pi01Sentence) : Pi02Sentence where
  statement := φ.statement
  R := fun n _ => φ.R n
  R_dec := by
    intro ⟨n, _⟩
    exact φ.R_dec n
  equiv_pi02 := by
    constructor
    · intro h n
      rw [φ.equiv_pi01] at h
      exact ⟨0, h n⟩
    · intro h
      rw [φ.equiv_pi01]
      intro n
      obtain ⟨_, hm⟩ := h n
      exact hm


-- ========================================================================
-- Formal Systems (Abstract)
-- ========================================================================

/-- A formal system (e.g., ZFC, PA) is modeled by what it can prove.
    We abstract away the proof calculus and just record provability. -/
structure FormalSystem where
  /-- The system can prove a given proposition. -/
  proves : Prop → Prop
  /-- If the system proves P, then P is true (soundness). -/
  sound : ∀ {P : Prop}, proves P → P

/-- A sentence φ is independent of a system T if T proves neither φ nor ¬φ. -/
def independent (T : FormalSystem) (φ : Prop) : Prop :=
  ¬ T.proves φ ∧ ¬ T.proves (¬ φ)

/-- A sentence φ is provable in T. -/
def provable (T : FormalSystem) (φ : Prop) : Prop :=
  T.proves φ


-- ========================================================================
-- Models and Absoluteness (Abstract)
-- ========================================================================

/-- A transitive model of ZFC. We do not formalize the model theory;
    instead we axiomatize the key property: a transitive model assigns
    truth values to arithmetical sentences. -/
structure TransitiveModel where
  /-- The model's evaluation of a proposition. -/
  satisfies : Prop → Prop

/-- A sentence is absolute if it has the same truth value in all
    transitive models. This is the key property established by
    Shoenfield's theorem for arithmetical sentences. -/
def absolute (φ : Prop) (models : TransitiveModel → Prop) : Prop :=
  ∀ M₁ M₂ : TransitiveModel, models M₁ → models M₂ →
    (M₁.satisfies φ ↔ M₂.satisfies φ)


-- ========================================================================
-- Two Modes of Independence
-- ========================================================================

/-- Cohen independence: φ is true in some transitive models and false
    in others. This is what forcing establishes (e.g., for CH).
    Absolute sentences CANNOT be Cohen-independent. -/
def cohen_independent (φ : Prop) (models : TransitiveModel → Prop) : Prop :=
  ∃ M₁ M₂ : TransitiveModel, models M₁ ∧ models M₂ ∧
    M₁.satisfies φ ∧ ¬ M₂.satisfies φ

/-- Gödel independence: φ has the same truth value in all transitive
    models (it is absolute) but the formal system cannot prove it.
    Con(ZFC) is the canonical example. -/
def goedel_independent (T : FormalSystem) (φ : Prop)
    (models : TransitiveModel → Prop) : Prop :=
  absolute φ models ∧ independent T φ


-- ========================================================================
-- Conjecture D: Logical Form
-- ========================================================================

/-- The logical content of Standard Conjecture D, axiomatized as a
    Π₂⁰ sentence. The geometric content (algebraic cycles, cohomology,
    intersection numbers) is abstracted into the decidable relation R.

    Interpretation of R(n,m):
    - n encodes a pair (variety X, cycle Z) via Gödel numbering
    - m encodes a test cycle W
    - R(n,m) holds iff deg(Z · W) ≠ 0 ∨ cl(Z) = 0

    The Π₂⁰ form is: ∀n, ∃m, R(n,m)
    i.e., for every (X,Z), either Z is homologically trivial
    or there exists a witness W detecting numerical non-triviality.

    We axiomatize (not prove) that:
    - R is decidable (intersection numbers and cycle class maps
      are computable over countable algebraically closed fields)
    - The proper class quantifier collapses to ℕ by spreading out
      and the Lefschetz principle (Kleiman 1968) -/
structure ConjDData where
  /-- Conjecture D as a proposition. -/
  conjD : Prop
  /-- Its Π₂⁰ form. -/
  pi02_form : Pi02Sentence
  /-- The Π₂⁰ sentence captures Conjecture D. -/
  captures : pi02_form.statement = conjD

/-- The DPT axioms from Papers 51-53: decidable equality, algebraic
    spectrum, Archimedean polarization. These are the hypotheses under
    which the motive kills LPO. -/
structure DPTAxioms where
  /-- Decidable equality on algebraic cycles. -/
  decidable_equality : Prop
  /-- Eigenvalues of Frobenius are algebraic numbers. -/
  algebraic_spectrum : Prop
  /-- Positive-definiteness of the Néron-Tate height. -/
  archimedean_polarization : Prop

/-- The CRM program's main conditional result:
    DPT axioms → motive kills LPO (descent to MP). -/
structure CRMConditional where
  dpt : DPTAxioms
  /-- LPO is the "strong oracle" principle. -/
  lpo : Prop
  /-- MP is Markov's Principle. -/
  mp : Prop
  /-- Given DPT axioms, the motive reduces LPO to MP. -/
  motive_kills_lpo : dpt.decidable_equality →
    dpt.algebraic_spectrum → dpt.archimedean_polarization →
    (lpo → mp)

end Papers.P55
