/-
Papers/P26_GodelGap/Basic.lean
Paper 26: The Gödel-Gap Correspondence

Core definitions: WLPO, sequence spaces ℓ∞ and c₀, the quotient ℓ∞/c₀.

This module provides the analytic infrastructure for the Gödel-Gap
correspondence. The bidual gap ℓ∞/c₀ was calibrated against WLPO in
Paper 2. Here we redefine the essential structures for self-containment.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Pairing

namespace Papers.P26_GodelGap

-- ========================================================================
-- WLPO: Weak Limited Principle of Omniscience
-- ========================================================================

/-- **WLPO (Weak Limited Principle of Omniscience)**: For every binary sequence,
    either it is identically zero or it is not identically zero.
    Constructively non-trivial; classically true. -/
def WLPO : Prop :=
  ∀ (α : ℕ → Bool), (∀ n, α n = false) ∨ ¬(∀ n, α n = false)

/-- WLPO is classically true. -/
theorem wlpo_classical : WLPO := fun α => by
  by_cases h : ∀ n, α n = false
  · exact Or.inl h
  · exact Or.inr h

-- ========================================================================
-- Sequence spaces: ℓ∞ and c₀
-- ========================================================================

/-- **ℓ∞**: the space of bounded real sequences. -/
def BddSeq := { f : ℕ → ℝ // ∃ M : ℝ, ∀ n, |f n| ≤ M }

/-- **c₀**: the space of real sequences converging to 0. -/
def NullSeq := { f : ℕ → ℝ // Filter.Tendsto f Filter.atTop (nhds 0) }

-- ========================================================================
-- The quotient ℓ∞/c₀
-- ========================================================================

/-- Two bounded sequences are equivalent mod c₀ iff their difference
    converges to 0. -/
def bddSeqEquiv (f g : BddSeq) : Prop :=
  Filter.Tendsto (fun n => f.val n - g.val n) Filter.atTop (nhds 0)

/-- bddSeqEquiv is reflexive. -/
theorem bddSeqEquiv_refl (f : BddSeq) : bddSeqEquiv f f := by
  simp only [bddSeqEquiv, sub_self]
  exact tendsto_const_nhds

theorem bddSeqEquiv_symm {f g : BddSeq} (h : bddSeqEquiv f g) :
    bddSeqEquiv g f := by
  simp only [bddSeqEquiv] at *
  have heq : (fun n => g.val n - f.val n) = (fun n => -(f.val n - g.val n)) := by
    ext n; ring
  rw [heq, show (0 : ℝ) = -0 from by ring]
  exact Filter.Tendsto.neg h

theorem bddSeqEquiv_trans {f g k : BddSeq} (hfg : bddSeqEquiv f g)
    (hgk : bddSeqEquiv g k) : bddSeqEquiv f k := by
  simp only [bddSeqEquiv] at *
  have heq : (fun n => f.val n - k.val n) =
         (fun n => (f.val n - g.val n) + (g.val n - k.val n)) := by
    ext n; ring
  rw [heq]
  have h0 : (0 : ℝ) = 0 + 0 := by ring
  rw [h0]
  exact Filter.Tendsto.add hfg hgk

/-- The setoid on BddSeq induced by c₀-equivalence. -/
instance bddSeqSetoid : Setoid BddSeq where
  r := bddSeqEquiv
  iseqv := ⟨bddSeqEquiv_refl, fun h => bddSeqEquiv_symm h,
            fun h1 h2 => bddSeqEquiv_trans h1 h2⟩

/-- **ℓ∞/c₀**: the bidual gap, i.e., bounded sequences modulo null sequences. -/
def BidualGap := Quotient bddSeqSetoid

/-- Quotient map: send a bounded sequence to its equivalence class in ℓ∞/c₀. -/
def BidualGap.mk (f : BddSeq) : BidualGap := Quotient.mk bddSeqSetoid f

/-- The zero element of ℓ∞/c₀. -/
def BidualGap.zero : BidualGap :=
  BidualGap.mk ⟨fun _ => 0, ⟨0, fun _ => by simp⟩⟩

-- ========================================================================
-- Key lemma: {0,1}-valued sequences on disjoint infinite sets
-- ========================================================================

/-- A {0,1}-valued sequence with infinitely many 1s does NOT converge to 0. -/
theorem not_null_of_infinite_ones {f : ℕ → ℝ}
    (_hf01 : ∀ n, f n = 0 ∨ f n = 1)
    (hinf : Set.Infinite {n | f n = 1}) :
    ¬ Filter.Tendsto f Filter.atTop (nhds 0) := by
  intro htends
  rw [Metric.tendsto_atTop] at htends
  obtain ⟨N, hN⟩ := htends (1/2) (by positivity)
  obtain ⟨n, hn_mem, hn_ge⟩ := hinf.exists_gt N
  have hndist := hN n (le_of_lt hn_ge)
  rw [Set.mem_setOf_eq] at hn_mem
  simp [dist_comm, Real.dist_eq, hn_mem] at hndist
  linarith

end Papers.P26_GodelGap
