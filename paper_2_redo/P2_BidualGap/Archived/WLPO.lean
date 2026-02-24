/-
  Papers/P2_BidualGap/Logic/WLPO.lean
  
  Definition and properties of the Weak Limited Principle of Omniscience (WLPO).
  This is a key constructive principle that will be shown equivalent to the
  existence of Banach spaces with bidual gaps.
-/

import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic
import Papers.P2_BidualGap.Basic

namespace Papers.P2_BidualGap

/-- A binary sequence (used for constructive principles) -/
def BinarySeq := ℕ → Bool

/-- The Weak Limited Principle of Omniscience (WLPO):
    For every binary sequence, either all values are false or not all values are false -/
def WLPO : Prop :=
  ∀ (α : BinarySeq), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- WLPO is classically true (using LEM) -/
theorem wlpo_classical : Classical.choice → WLPO := by
  intro _
  intro α
  exact Classical.em (∀ n, α n = false)

/-- Alternative formulation: WLPO in terms of existence -/
def WLPO' : Prop :=
  ∀ (α : BinarySeq), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- The two formulations of WLPO are equivalent -/
theorem wlpo_iff_wlpo' : WLPO ↔ WLPO' := by
  constructor
  · intro h α
    cases h α with
    | inl hall => left; exact hall
    | inr hnall => 
      right
      -- If not all are false, then at least one is true
      push_neg at hnall
      obtain ⟨n, hn⟩ := hnall
      use n
      cases h' : α n
      · contradiction
      · rfl
  · intro h α
    cases h α with
    | inl hall => left; exact hall
    | inr ⟨n, hn⟩ => 
      right
      intro hall
      specialize hall n
      rw [hall] at hn
      simp at hn

/-- A sequence that is eventually false -/
def eventuallyFalse (α : BinarySeq) : Prop :=
  ∃ N, ∀ n ≥ N, α n = false

/-- A sequence that has infinitely many true values -/
def infinitelyOftenTrue (α : BinarySeq) : Prop :=
  ∀ N, ∃ n ≥ N, α n = true

/-- Under WLPO, every sequence is either all false or has a true value -/
theorem wlpo_dichotomy (h : WLPO) (α : BinarySeq) :
  (∀ n, α n = false) ∨ (∃ n, α n = true) := by
  have h' : WLPO' := wlpo_iff_wlpo'.mp h
  exact h' α

/-- A constructive implication: if we can decide all-false for bounded sequences, we get WLPO -/
theorem bounded_decision_implies_wlpo :
  (∀ (α : BinarySeq) (N : ℕ), Decidable (∀ n < N, α n = false)) → WLPO := by
  intro hdec α
  -- The idea: if we can decide for all finite prefixes, we can handle the infinite case
  -- This is a key connection to computability
  sorry -- TODO: Implement the proof

section Computability

/-- A binary sequence is computable if there's an algorithm to compute its values -/
def isComputable (α : BinarySeq) : Prop :=
  ∃ (f : ℕ → Bool), ∀ n, f n = α n  -- Simplified definition for now

/-- WLPO restricted to computable sequences -/
def ComputableWLPO : Prop :=
  ∀ (α : BinarySeq), isComputable α → (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- Computable WLPO is weaker than full WLPO -/
theorem computable_wlpo_weaker : WLPO → ComputableWLPO := by
  intro h α _
  exact h α

end Computability

section SequenceConstructions

/-- Given a sequence α, construct a related sequence that's useful for gap constructions -/
noncomputable def gapSequence (α : BinarySeq) : ℕ → ℝ :=
  fun n => if α n then (1 : ℝ) / (n + 1) else 0

/-- The gap sequence converges to 0 -/
theorem gapSequence_tendsto_zero (α : BinarySeq) :
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |gapSequence α n| < ε := by
  -- Whether α has infinitely many trues or not, the sequence tends to 0
  sorry -- TODO: Implement convergence proof

/-- The sum of the gap sequence would be finite if we had summability -/
theorem gapSequence_would_be_summable (α : BinarySeq) :
  -- The series ∑ 1/(n+1) for true positions converges
  True := by trivial -- Placeholder until we have proper summability

/-- Under WLPO, we can decide properties about the gap sequence -/
theorem gap_sequence_decision (h : WLPO) (α : BinarySeq) :
  (∀ n, gapSequence α n = 0) ∨ (∃ n, gapSequence α n > 0) := by
  cases h α with
  | inl hall =>
    left
    intro n
    simp [gapSequence]
    rw [hall n]
    simp
  | inr hex =>
    right
    push_neg at hex
    obtain ⟨n, hn⟩ := hex
    use n
    simp [gapSequence]
    rw [hn]
    sorry -- Need to show 1/(n+1) > 0

end SequenceConstructions

end Papers.P2_BidualGap