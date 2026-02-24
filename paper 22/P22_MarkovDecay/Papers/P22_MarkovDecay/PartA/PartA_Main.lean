/-
  Paper 22: Markov's Principle and the Constructive Cost of Eventual Decay
  PartA/PartA_Main.lean — Part A summary and axiom audit

  Part A (BISH): With an explicit lower bound on the decay rate,
  the detection time is constructively computable. No MP required.
-/
import Papers.P22_MarkovDecay.PartA.DetectionTime

namespace Papers.P22

/-- Part A summary: detection time works for known bounds (BISH). -/
theorem partA_summary :
    -- Detection time is positive
    (∀ q eps : ℝ, 0 < q → 0 < eps → eps < 1 → 0 < detectionTime eps q) ∧
    -- Detection time achieves the threshold
    (∀ lambda_ q eps : ℝ, 0 < q → q ≤ lambda_ → 0 < eps → eps < 1 →
      survivalProb lambda_ (detectionTime eps q) ≤ eps) :=
  ⟨fun q eps => detectionTime_pos q eps,
   fun lambda_ q eps => detection_time_works lambda_ q eps⟩

-- Axiom audit: Part A is BISH (no custom axioms)
-- Expected: [propext, Classical.choice, Quot.sound]
#print axioms detectionTime_pos
#print axioms detection_time_works
#print axioms detection_with_witness
#print axioms partA_summary

end Papers.P22
