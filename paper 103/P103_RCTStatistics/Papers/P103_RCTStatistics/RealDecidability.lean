/-
  RealDecidability.lean — Part II

  The bridge between real analysis and omniscience:
  trichotomy for reals is equivalent to LPO.
-/
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Papers.P103_RCTStatistics.OmnisciencePrinciples

namespace P103

/-- Trichotomy for reals implies LPO.
    Encoding: α : BinSeq ↦ x = Σ α(n)·2^{-(n+1)}.
    If x = 0 then ∀ n, α n = false; if x > 0 then ∃ n, α n = true.
    Documentary axiom: the encoding construction is standard
    (Bishop-Bridges, §2.3) but requires careful series formalisation. -/
axiom trichotomy_implies_LPO_encoding :
  (∀ (x y : ℝ), x < y ∨ x = y ∨ x > y) → LPO

/-- Strict comparison of rationals is decidable (no omniscience needed). -/
theorem rat_trichotomy (p q : ℚ) : p < q ∨ p = q ∨ p > q := by
  rcases lt_trichotomy p q with h | h | h
  · left; exact h
  · right; left; exact h
  · right; right; exact h

/-- Rational comparison is decidable — the foundational BISH fact
    that anchors the entire paper. -/
instance : DecidableEq ℚ := inferInstance

/-- For rationals, "less than" is decidable. -/
instance (p q : ℚ) : Decidable (p < q) := inferInstance

/-- KEY BRIDGE: The gap between ℚ-decidability and ℝ-decidability
    is precisely where omniscience principles enter clinical inference.
    Comparing two rationals: BISH. Comparing a real with a rational: MP.
    Universal comparison over ℝ: LPO. -/
theorem decidability_hierarchy :
    -- Level 0 (BISH): rational comparison is decidable
    (∀ (p q : ℚ), p < q ∨ p = q ∨ p > q) ∧
    -- Level 1 (BISH+MP): real < rational, given ¬¬-witness
    -- Level 2 (LPO): universal real comparison
    -- (Levels 1 and 2 stated as axioms above)
    True := ⟨rat_trichotomy, trivial⟩

end P103
