/-
Papers/P25_ChoiceAxis/MeanErgodicReverse.lean
Paper 25: Mean Ergodic Theorem → Countable Choice (Reverse Direction)

This module establishes the reverse direction of the CC calibration:
the mean ergodic theorem implies countable choice.

## Lean proof vs. constructive content

In classical Lean, CC_N is provable outright via `Classical.choice`,
so `MeanErgodicTheorem → CC_N` holds trivially. The mathematical
content — that the mean ergodic theorem *constructively* implies CC —
is a claim about BISH (Bishop's constructive mathematics), not about
Lean's classical logic. The Lean proof witnesses the classical validity;
the constructive calibration is documented below.

## Constructive proof sketch (for the paper, over BISH)

Given a countable choice problem P : ℕ → ℕ → Prop with ∀ n, ∃ m, P n m:

1. Build H = ℓ²(ℕ) with an orthogonal direct sum decomposition
   H = ⊕_n H_n where each H_n encodes the choice set {m : P n m}.

2. Define a unitary operator U on H that cyclically shifts within
   each block H_n. The structure of U ensures:
   - Fix(U) ∩ H_n is nontrivial iff S_n = {m : P n m} is nonempty
   - The projection onto Fix(U) restricted to H_n selects an element

3. Apply the mean ergodic theorem: Cesàro averages of a suitable
   starting vector converge to the projection onto Fix(U).

4. Read off the limit's components in each block to extract choices
   from each S_n, yielding the choice function.

The critical subtlety: step (4) must not smuggle in CC through the
back door. The convergence of Cesàro averages (in norm) provides the
limit as a single element of H, and extracting its components is a
purely algebraic operation (orthogonal projection onto each H_n).

**References**:
- Bishop & Bridges, *Constructive Analysis* (1985), Ch. 7
- The encoding technique is inspired by reverse mathematics of
  Hilbert space theory (Avigad & Simic)
-/
import Papers.P25_ChoiceAxis.MeanErgodic

namespace Papers.P25_ChoiceAxis

/-- **Mean Ergodic Theorem implies Countable Choice.**

    In classical Lean, CC_N is provable from `Classical.choice` alone,
    so this implication holds trivially — the antecedent is unused.

    The mathematical content is a constructive claim (over BISH):
    if Cesàro averages of every isometry on a Hilbert space converge
    in norm (the mean ergodic theorem), then countable families of
    nonempty sets admit choice functions (CC). The proof encodes
    countable choice problems into specific Hilbert spaces and
    isometries; see module docstring for the encoding strategy.

    This Lean proof witnesses classical validity; the constructive
    calibration is at paper level. -/
theorem meanErgodic_implies_cc : MeanErgodicTheorem → CC_N := by
  intro _
  -- In classical Lean, CC_N is provable without any hypothesis.
  -- Classical.choice extracts witnesses from (A n).Nonempty.
  intro A hA
  exact ⟨fun n => (hA n).some, fun n => (hA n).some_mem⟩

/-- **Mean Ergodic Theorem is equivalent to CC** (over BISH).
    Combines the forward and reverse directions.

    In classical Lean, both directions are proved, yielding a clean
    axiom profile [propext, Classical.choice, Quot.sound].
    The constructive content is that CC is the precise choice principle
    needed for the mean ergodic theorem, documented at paper level. -/
theorem meanErgodic_iff_cc : CC_N ↔ MeanErgodicTheorem :=
  ⟨meanErgodic_of_cc, meanErgodic_implies_cc⟩

end Papers.P25_ChoiceAxis
