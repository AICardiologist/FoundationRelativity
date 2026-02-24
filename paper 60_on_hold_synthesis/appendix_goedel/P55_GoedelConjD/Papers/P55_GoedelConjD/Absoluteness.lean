/-
  Paper 55: Is Gödel Absent from the Motive?
  Absoluteness.lean — Shoenfield absoluteness and its consequences

  Core results:
  1. Shoenfield's theorem (axiomatized): Π₂⁰ sentences are absolute
  2. Cohen immunity: absolute sentences cannot be Cohen-independent
  3. Application to Conjecture D: Cohen forcing cannot affect it
  4. The gap: absoluteness does NOT imply provability (Con(ZFC) witness)

  Shoenfield's theorem is a deep result in model theory (1961).
  We axiomatize it as a hypothesis and derive consequences.
-/
import Papers.P55_GoedelConjD.Defs

namespace Papers.P55

-- ========================================================================
-- Shoenfield Absoluteness (Axiomatized)
-- ========================================================================

/-- Shoenfield's absoluteness theorem (1961), axiomatized.

    The full theorem states: every Σ¹₂ sentence is absolute between
    transitive models of ZFC containing the same ordinals.
    Since every arithmetical sentence is Σ¹₂, this applies to all
    Π₂⁰ sentences.

    We state the restricted version for Π₂⁰ sentences, which is
    all we need for Conjecture D. -/
structure ShoenfieldAbsoluteness where
  /-- The class of transitive models of ZFC. -/
  zfc_models : TransitiveModel → Prop
  /-- At least two transitive models exist (ZFC is consistent). -/
  has_models : ∃ M₁ M₂ : TransitiveModel, zfc_models M₁ ∧ zfc_models M₂
  /-- The absoluteness property: every Π₂⁰ sentence has the same
      truth value in all transitive models of ZFC. -/
  pi02_absolute : ∀ (φ : Pi02Sentence),
    absolute φ.statement zfc_models
  /-- Soundness: transitive models agree with mathematical truth
      on arithmetical sentences. If φ is Π₂⁰ and true, then every
      transitive model satisfies it. -/
  pi02_sound : ∀ (φ : Pi02Sentence) (M : TransitiveModel),
    zfc_models M → φ.statement → M.satisfies φ.statement


-- ========================================================================
-- Cohen Immunity
-- ========================================================================

/-- Absolute sentences cannot be Cohen-independent.
    This is immediate from the definitions. -/
theorem absolute_not_cohen_independent (φ : Prop)
    (models : TransitiveModel → Prop)
    (h_abs : absolute φ models) :
    ¬ cohen_independent φ models := by
  intro ⟨M₁, M₂, hM₁, hM₂, h_sat, h_nsat⟩
  exact h_nsat ((h_abs M₁ M₂ hM₁ hM₂).mp h_sat)

/-- Conjecture D is Cohen-immune: forcing cannot change its truth value.
    This is the main negative result — set theory is irrelevant. -/
theorem conjD_cohen_immune
    (data : ConjDData)
    (SA : ShoenfieldAbsoluteness) :
    ¬ cohen_independent data.conjD SA.zfc_models := by
  have h_abs : absolute data.pi02_form.statement SA.zfc_models :=
    SA.pi02_absolute data.pi02_form
  have h_eq : data.pi02_form.statement = data.conjD := data.captures
  rw [← h_eq]
  exact absolute_not_cohen_independent _ _ h_abs


-- ========================================================================
-- The Gap: Absoluteness ≠ Provability
-- ========================================================================

/-- Gödel's Second Incompleteness Theorem (axiomatized):
    If T is a consistent formal system extending PA, then
    Con(T) is true but unprovable in T. -/
structure GoedelSecondIncompleteness where
  /-- The formal system (e.g., ZFC). -/
  T : FormalSystem
  /-- The consistency statement Con(T). -/
  conT : Pi01Sentence
  /-- Con(T) is true (T is consistent). -/
  consistent : conT.statement
  /-- T does not prove Con(T). -/
  unprovable : ¬ T.proves conT.statement
  /-- T does not prove ¬Con(T) either (since T is sound). -/
  unrefutable : ¬ T.proves (¬ conT.statement)

/-- Con(ZFC) is an absolute sentence that is independent of ZFC.
    This witnesses the gap between absoluteness and provability. -/
theorem goedel_independent_witness
    (G : GoedelSecondIncompleteness)
    (SA : ShoenfieldAbsoluteness) :
    goedel_independent G.T G.conT.statement SA.zfc_models := by
  constructor
  · -- Con(T) is Π₁⁰, hence Π₂⁰, hence absolute
    exact SA.pi02_absolute G.conT.toPi02
  · -- Con(T) is independent of T
    exact ⟨G.unprovable, G.unrefutable⟩

/-- The key distinction: absoluteness does NOT imply provability.
    There exist Π₁⁰ (hence Π₂⁰) sentences that are absolute
    yet independent of ZFC. -/
theorem absoluteness_not_implies_provability
    (G : GoedelSecondIncompleteness)
    (SA : ShoenfieldAbsoluteness) :
    ∃ φ : Pi02Sentence,
      absolute φ.statement SA.zfc_models ∧
      independent G.T φ.statement := by
  exact ⟨G.conT.toPi02, SA.pi02_absolute G.conT.toPi02,
         ⟨G.unprovable, G.unrefutable⟩⟩

end Papers.P55
