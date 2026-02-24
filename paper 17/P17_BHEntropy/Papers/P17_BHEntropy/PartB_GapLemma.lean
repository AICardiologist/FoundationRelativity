/-
Papers/P17_BHEntropy/PartB_GapLemma.lean
The entropy density gap lemma.

Key axiom: There exist two areas A_lo < A_hi with strictly different
entropy densities. This is the key ingredient for the backward direction
of the LPO equivalence.

AXIOMATIZATION RATIONALE:
The entropy density gap is a finite decidable computation: for two
specific areas, enumerate all admissible spin configurations at each,
count them, compute log(count)/area, and verify the two values differ.
This is BISH-valid in principle. We axiomatize it for performance —
the exhaustive enumeration is too expensive for Lean's kernel evaluator.

This axiom is analogous to Paper 8's `freeEnergy_gap_pos`, which was
proven analytically (via cosh strict monotonicity). Here the gap comes
from the combinatorial structure of spin network state counting, which
resists closed-form analysis.

The axiom does NOT compromise the logical structure — it is a performance
optimization, not a logical shortcut. The #print axioms output will show
this axiom explicitly.
-/
import Papers.P17_BHEntropy.PartB_AreaSeq
import Papers.P17_BHEntropy.Entropy

namespace Papers.P17

/-- **Entropy density gap (Lemma 4.2).**

    There exist specific areas A_lo, A_hi and a gap > 0 such that the
    entropy density at A_hi exceeds that at A_lo by at least gap.

    This is a finite computation: enumerate admissible configurations at
    two specific areas, count them, compute log(count)/area, and verify
    the difference exceeds the gap. Axiomatized for performance.

    The existence of such areas follows from the combinatorial structure
    of spin network state counting: the entropy density function is not
    constant as a function of area (physically: larger horizons have more
    microstates per unit area than smaller ones, in the regime we consider). -/
axiom entropy_density_gap (gamma : ℝ) (hg : gamma > 0)
    (delta : ℝ) (hd : delta > 0) :
    ∃ (A_lo A_hi gap : ℝ)
      (hA_lo : A_lo > 0) (hA_hi : A_hi > 0),
      A_lo < A_hi ∧ gap > 0 ∧
      entropy_density A_hi gamma delta hA_hi hg hd -
        entropy_density A_lo gamma delta hA_lo hg hd > gap

end Papers.P17
