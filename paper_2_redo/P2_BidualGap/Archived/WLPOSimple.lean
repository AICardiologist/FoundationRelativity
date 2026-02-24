/-
  Papers/P2_BidualGap/Logic/WLPOSimple.lean
  
  Simplified definition of WLPO that compiles without advanced dependencies.
-/

import Papers.P2_BidualGap.Basic

namespace Papers.P2_BidualGap

/-- A binary sequence -/
def BinarySeq := ℕ → Bool

/-- The Weak Limited Principle of Omniscience -/
def WLPO : Prop :=
  ∀ (α : BinarySeq), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- Alternative formulation -/
def WLPO' : Prop :=
  ∀ (α : BinarySeq), (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- The two formulations are equivalent -/
theorem wlpo_iff_wlpo' : WLPO ↔ WLPO' := by
  constructor
  · intro h α
    cases h α with
    | inl hall => left; exact hall
    | inr hnall => 
      right
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
      -- hn says α n = true, but hall says α n = false
      -- This is a contradiction
      exact Bool.false_ne_true hn

/-- A computable sequence for examples -/
def isComputable (α : BinarySeq) : Prop :=
  ∃ (f : ℕ → Bool), ∀ n, f n = α n

/-- WLPO restricted to computable sequences -/
def ComputableWLPO : Prop :=
  ∀ (α : BinarySeq), isComputable α → (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- Computable WLPO is weaker than full WLPO -/
theorem computable_wlpo_weaker : WLPO → ComputableWLPO := by
  intro h α _
  exact h α

/-- Under WLPO, we can decide sequence properties -/
theorem wlpo_sequence_dichotomy (h : WLPO) (α : BinarySeq) :
  (∀ n, α n = false) ∨ (∃ n, α n = true) := by
  have h' : WLPO' := wlpo_iff_wlpo'.mp h
  exact h' α

end Papers.P2_BidualGap