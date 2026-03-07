/-
  OmnisciencePrinciples.lean — Part I

  Omniscience principles as propositions about binary sequences,
  following Bishop-Bridges and Troelstra-van Dalen.

  Paper 105, Clinical Sub-Series Paper C,
  of the Constructive Reverse Mathematics Series

  Extends the P103/P104 hierarchy with WKL (Weak König's Lemma).
-/
import Mathlib.Tactic

namespace P105

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
    For every binary sequence with at most one true term,
    either all even-indexed terms are false or all odd-indexed
    terms are false. -/
def LLPO : Prop :=
  ∀ (α : BinSeq),
    (∀ m n, α m = true → α n = true → m = n) →
    (∀ n, α (2 * n) = false) ∨ (∀ n, α (2 * n + 1) = false)

/-- Markov's Principle (MP):
    If it is not the case that all terms of a binary sequence
    are false, then there exists a term that is true. -/
def MarkovPrinciple : Prop :=
  ∀ (α : BinSeq), ¬(∀ n, α n = false) → ∃ n, α n = true

/-- Weak König's Lemma (WKL): modeled as a proposition.
    Every infinite finitely-branching tree has an infinite path.
    We axiomatize it as a Prop since the tree-theoretic content
    is not directly used in the CRM decomposition. -/
def WKL : Prop :=
  ∀ (T : List Bool → Prop),
    -- T is a tree (prefix-closed)
    (∀ (s : List Bool) (b : Bool), T (s ++ [b]) → T s) →
    -- T is infinite (arbitrarily long nodes exist)
    (∀ n : ℕ, ∃ s : List Bool, s.length = n ∧ T s) →
    -- Then T has an infinite path
    ∃ f : ℕ → Bool, ∀ n : ℕ, T (List.ofFn (fun (i : Fin n) => f i))

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

/-- WLPO implies LLPO -/
theorem WLPO_implies_LLPO : WLPO → LLPO := by
  intro hWLPO α huniq
  -- Define αₑ(n) = α(2n)
  let αₑ : BinSeq := fun n => α (2 * n)
  rcases hWLPO αₑ with heven | heven
  · left; exact heven
  · right
    intro n
    by_contra h
    -- h : α(2n+1) ≠ false, so α(2n+1) = true
    have h_true : α (2 * n + 1) = true := by
      cases hb : α (2 * n + 1) with
      | true => rfl
      | false => exact absurd hb h
    -- Since heven says ¬(∀ m, α(2m) = false), ∃ m with α(2m) = true
    have ⟨m, hm⟩ : ∃ m, αₑ m = true := by
      by_contra hall
      push_neg at hall
      exact heven (fun m => by
        have := hall m
        simp [αₑ, BinSeq] at this ⊢
        exact this)
    -- Now α(2m) = true and α(2n+1) = true, so 2m = 2n+1 by uniqueness
    have : 2 * m = 2 * n + 1 := huniq (2 * m) (2 * n + 1) hm h_true
    omega

/-! ## CRM Level Enumeration -/

/-- CRM classification levels for the dynamical systems decomposition. -/
inductive CRMLevel
  | BISH     -- Bishop's constructive mathematics
  | BISH_MP  -- BISH + Markov's Principle
  | BISH_WLPO -- BISH + Weak Limited Principle of Omniscience
  | BISH_WKL -- BISH + Weak König's Lemma
  | BISH_LPO -- BISH + Limited Principle of Omniscience
  | CLASS    -- Full classical mathematics
  deriving DecidableEq, Repr

/-- CRM levels are linearly ordered by logical strength.
    BISH < BISH+MP < BISH+WLPO < BISH+WKL < BISH+LPO < CLASS -/
instance : LE CRMLevel where
  le a b := match a, b with
    | .BISH, _ => True
    | .BISH_MP, .BISH => False
    | .BISH_MP, _ => True
    | .BISH_WLPO, .BISH => False
    | .BISH_WLPO, .BISH_MP => False
    | .BISH_WLPO, _ => True
    | .BISH_WKL, .BISH => False
    | .BISH_WKL, .BISH_MP => False
    | .BISH_WKL, .BISH_WLPO => False
    | .BISH_WKL, _ => True
    | .BISH_LPO, .CLASS => True
    | .BISH_LPO, .BISH_LPO => True
    | .BISH_LPO, _ => False
    | .CLASS, .CLASS => True
    | .CLASS, _ => False

instance : DecidableRel (α := CRMLevel) (· ≤ ·) :=
  fun a b => match a, b with
    | .BISH, _ => isTrue trivial
    | .BISH_MP, .BISH => isFalse not_false
    | .BISH_MP, .BISH_MP => isTrue trivial
    | .BISH_MP, .BISH_WLPO => isTrue trivial
    | .BISH_MP, .BISH_WKL => isTrue trivial
    | .BISH_MP, .BISH_LPO => isTrue trivial
    | .BISH_MP, .CLASS => isTrue trivial
    | .BISH_WLPO, .BISH => isFalse not_false
    | .BISH_WLPO, .BISH_MP => isFalse not_false
    | .BISH_WLPO, .BISH_WLPO => isTrue trivial
    | .BISH_WLPO, .BISH_WKL => isTrue trivial
    | .BISH_WLPO, .BISH_LPO => isTrue trivial
    | .BISH_WLPO, .CLASS => isTrue trivial
    | .BISH_WKL, .BISH => isFalse not_false
    | .BISH_WKL, .BISH_MP => isFalse not_false
    | .BISH_WKL, .BISH_WLPO => isFalse not_false
    | .BISH_WKL, .BISH_WKL => isTrue trivial
    | .BISH_WKL, .BISH_LPO => isTrue trivial
    | .BISH_WKL, .CLASS => isTrue trivial
    | .BISH_LPO, .BISH => isFalse not_false
    | .BISH_LPO, .BISH_MP => isFalse not_false
    | .BISH_LPO, .BISH_WLPO => isFalse not_false
    | .BISH_LPO, .BISH_WKL => isFalse not_false
    | .BISH_LPO, .BISH_LPO => isTrue trivial
    | .BISH_LPO, .CLASS => isTrue trivial
    | .CLASS, .BISH => isFalse not_false
    | .CLASS, .BISH_MP => isFalse not_false
    | .CLASS, .BISH_WLPO => isFalse not_false
    | .CLASS, .BISH_WKL => isFalse not_false
    | .CLASS, .BISH_LPO => isFalse not_false
    | .CLASS, .CLASS => isTrue trivial

/-- Join (maximum) of two CRM levels -/
def CRMLevel.join : CRMLevel → CRMLevel → CRMLevel
  | .CLASS, _ => .CLASS
  | _, .CLASS => .CLASS
  | .BISH_LPO, _ => .BISH_LPO
  | _, .BISH_LPO => .BISH_LPO
  | .BISH_WKL, _ => .BISH_WKL
  | _, .BISH_WKL => .BISH_WKL
  | .BISH_WLPO, _ => .BISH_WLPO
  | _, .BISH_WLPO => .BISH_WLPO
  | .BISH_MP, _ => .BISH_MP
  | _, .BISH_MP => .BISH_MP
  | .BISH, .BISH => .BISH

/-- Join of a list of CRM levels -/
def CRMLevel.joinList : List CRMLevel → CRMLevel
  | [] => .BISH
  | [x] => x
  | x :: xs => x.join (joinList xs)

end P105
