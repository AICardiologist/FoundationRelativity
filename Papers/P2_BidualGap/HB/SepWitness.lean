import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

noncomputable section

-- Define the spaces
abbrev ι := ℕ
abbrev E := BoundedContinuousFunction ι ℝ

-- The embedding map (check if it's already a ContinuousLinearMap or needs to be lifted)
#check ZeroAtInftyContinuousMap.toBCF
#check @ZeroAtInftyContinuousMap.toBCF ℕ ℝ

-- Define constOne in the target space
def constOne : E := BoundedContinuousFunction.const ι (1 : ℝ)

-- Define the subspace S as the closed linear span of the range of the c₀ embedding
def S : Submodule ℝ E := 
  Submodule.span ℝ (Set.range (ZeroAtInftyContinuousMap.toBCF : ZeroAtInftyContinuousMap ι ℝ → E))

-- Two key facts about the subspace (statements only, proofs by sorry as requested)

-- Fact 1: S is closed (very likely already available in library)  
lemma isClosed_S : IsClosed (S : Set E) := by
  sorry -- TODO: search for closedness of c₀ in ℓ∞

-- Fact 2: constOne is not in S (from Fact A in SimpleFacts.lean)
lemma constOne_not_mem : constOne ∉ S := by 
  sorry -- Will follow from constOne_not_in_c0_image in SimpleFacts.lean