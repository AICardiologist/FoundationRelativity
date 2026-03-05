/-
  OmnisciencePrinciples.lean — Part I

  Omniscience principles as propositions about binary sequences,
  following Bishop-Bridges and Troelstra-van Dalen.
-/
import Mathlib.Tactic

namespace P103

/-- A binary sequence is a function ℕ → Bool -/
def BinSeq := ℕ → Bool

/-- Limited Principle of Omniscience (LPO):
    For every binary sequence, either some term equals true,
    or all terms equal false. -/
def LPO : Prop :=
  ∀ (α : BinSeq), (∃ n, α n = true) ∨ (∀ n, α n = false)

/-- Weak Limited Principle of Omniscience (WLPO):
    For every binary sequence, either all terms are false,
    or it is not the case that all terms are false. -/
def WLPO : Prop :=
  ∀ (α : BinSeq), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- Lesser Limited Principle of Omniscience (LLPO):
    For a binary sequence with at most one true term,
    either all even-indexed terms are false,
    or all odd-indexed terms are false. -/
def LLPO : Prop :=
  ∀ (α : BinSeq),
    (∀ m n, α m = true → α n = true → m = n) →
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)

/-- Markov's Principle (MP):
    If it is not the case that all terms of a binary sequence
    are false, then there exists a term that is true. -/
def MarkovPrinciple : Prop :=
  ∀ (α : BinSeq), ¬(∀ n, α n = false) → ∃ n, α n = true

/-- LPO implies WLPO -/
theorem LPO_implies_WLPO : LPO → WLPO := by
  intro hLPO α
  rcases hLPO α with ⟨n, hn⟩ | hall
  · right
    intro hfalse
    simp [hfalse n] at hn
  · left
    exact hall

/-- LPO implies MP -/
theorem LPO_implies_MP : LPO → MarkovPrinciple := by
  intro hLPO α hne
  rcases hLPO α with ⟨n, hn⟩ | hall
  · exact ⟨n, hn⟩
  · exact absurd hall hne

/-- LPO implies LLPO -/
theorem LPO_implies_LLPO : LPO → LLPO := by
  intro hLPO α _huniq
  rcases hLPO (fun n => α (2 * n)) with ⟨n, hn⟩ | hall
  · right
    intro m
    rcases hLPO (fun n => α (2 * n + 1)) with ⟨k, hk⟩ | hall_odd
    · -- Both even and odd have a true term; use uniqueness
      have h1 := _huniq (2 * n) (2 * k + 1) hn hk
      omega
    · exact hall_odd m
  · left
    exact hall

end P103
