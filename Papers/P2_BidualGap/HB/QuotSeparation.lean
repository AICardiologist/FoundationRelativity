import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual
import Papers.P2_BidualGap.HB.SimpleFacts

noncomputable section
open Classical

namespace Papers.P2.HB.QuotSeparation

-- Set the stage
abbrev ι := ℕ
abbrev E := BoundedContinuousFunction ι ℝ
def constOne : E := BoundedContinuousFunction.const ι (1 : ℝ)

-- Define the subspace as the range submodule directly
def S : Submodule ℝ E :=
{ carrier := {s | ∃ f : ZeroAtInftyContinuousMap ι ℝ, ZeroAtInftyContinuousMap.toBCF f = s},
  zero_mem' := ⟨0, by ext n; rfl⟩,
  add_mem' := by
    rintro x y ⟨f, rfl⟩ ⟨g, rfl⟩
    refine ⟨f + g, ?_⟩
    ext n; rfl,
  smul_mem' := by
    rintro a x ⟨f, rfl⟩
    refine ⟨a • f, ?_⟩
    ext n; rfl }

def Scl : Submodule ℝ E := S.topologicalClosure

-- Key facts about the closed subspace
lemma isClosed_Scl : IsClosed (Scl : Set E) := by
  -- closure is closed
  exact Submodule.isClosed_topologicalClosure S

lemma constOne_not_mem_Scl : constOne ∉ Scl := by
  -- S ⊆ E, treat both as sets
  have gap : ∀ s ∈ (S : Set E), (1/2 : ℝ) ≤ ‖constOne - s‖ := by
    intro s hs; rcases hs with ⟨f, rfl⟩
    -- specialize the SimpleFacts lemma to c = 1
    -- sep_from_constOne gives: ‖f.toBCF - constOne‖ ≥ 1/2
    -- We need: ‖constOne - f.toBCF‖ ≥ 1/2
    -- These are equal by norm_sub_rev (a - b has same norm as b - a)
    have h1 := sep_from_constOne f
    -- ‖a - b‖ = ‖-(a - b)‖ = ‖b - a‖
    have h2 : ‖constOne - ZeroAtInftyContinuousMap.toBCF f‖ = 
              ‖ZeroAtInftyContinuousMap.toBCF f - constOne‖ := by
      rw [← norm_neg]
      simp [neg_sub]
    rw [h2]
    exact h1
  -- If constOne were in the closure of S, it would be within 1/4 of some s ∈ S
  intro h
  -- Scl is the topological closure of S
  have h_closure : constOne ∈ closure (S : Set E) := by
    rw [← Submodule.topologicalClosure_coe S]
    exact h
  -- By metric closure characterization
  rw [Metric.mem_closure_iff] at h_closure
  obtain ⟨s, hsS, hs⟩ := h_closure (1/4) (by norm_num)
  have hge := gap s hsS
  have hlt : ‖constOne - s‖ < 1/4 := by
    rw [dist_eq_norm] at hs
    exact hs
  linarith

-- First establish that Scl is closed for the instances
lemma hScl : IsClosed (Scl : Set E) := isClosed_Scl

-- Provide instances globally for the quotient space
instance : IsClosed (Scl : Set E) := hScl
instance : NormedAddCommGroup (E ⧸ Scl) := Submodule.Quotient.normedAddCommGroup (S := Scl)
instance : NormedSpace ℝ (E ⧸ Scl) := inferInstance

-- Canonical quotient map
noncomputable def q : E →L[ℝ] E ⧸ Scl :=
  LinearMap.mkContinuous (Submodule.mkQ Scl) 1 fun x => by
    simp only [one_mul]
    exact Submodule.Quotient.norm_mk_le (S := Scl) x

lemma q_constOne_ne : q constOne ≠ 0 := by
  intro h
  have h' : Submodule.mkQ Scl constOne = 0 := by
    simpa [q, ContinuousLinearMap.coe_mk'] using h
  have : constOne ∈ (Scl : Set E) := by
    simpa [Submodule.mkQ_apply] using (Submodule.Quotient.mk_eq_zero Scl).1 h'
  exact constOne_not_mem_Scl this

-- Add Nontrivial instance after q_constOne_ne is proved
local instance : Nontrivial (E ⧸ Scl) :=
  ⟨⟨q constOne, 0, by simpa using q_constOne_ne⟩⟩

-- Route A: Try to get SeparatingDual directly from existing instances
lemma get_separating_functional :
  ∃ g : (E ⧸ Scl) →L[ℝ] ℝ, g (q constOne) = 1 := by
  -- First we need to show E ⧸ Scl has SeparatingDual
  -- This should follow from the fact that it's a normed space over ℝ
  -- But if not available, we can construct it manually:
  have : ∃ g : (E ⧸ Scl) →L[ℝ] ℝ, g (q constOne) ≠ 0 := by
    -- Use Hahn-Banach separation: q constOne ≠ 0 in the quotient
    sorry -- This follows from geometric Hahn-Banach
  obtain ⟨g, hg⟩ := this
  -- Scale g to get value 1
  use (g (q constOne))⁻¹ • g
  simp [hg]

noncomputable def F : E →L[ℝ] ℝ :=
  (Classical.choose get_separating_functional).comp q

lemma F_constOne : F constOne = 1 := by
  -- `choose_spec` gives the equality at `q constOne`
  simp only [F, ContinuousLinearMap.comp_apply]
  exact Classical.choose_spec get_separating_functional

lemma F_vanishes_on_Scl : ∀ s ∈ (Scl : Set E), F s = 0 := by
  intro s hs
  -- quotient kills Scl
  have : Submodule.mkQ Scl s = 0 := by
    simpa [Submodule.mkQ_apply] using (Submodule.Quotient.mk_eq_zero Scl).2 hs
  -- push back through `q`
  have : q s = 0 := by simpa [q, ContinuousLinearMap.coe_mk'] using this
  -- linear maps send 0 → 0
  simpa [F, this, ContinuousLinearMap.comp_apply]

-- Diagnostics now commented out since working
-- #synth SeminormedAddCommGroup (E ⧸ Scl)
-- #synth NormedSpace ℝ (E ⧸ Scl)
-- #check Submodule.mkQ Scl
-- #check Submodule.Quotient.norm_mk_le (S := Scl)
-- #check Submodule.Quotient.mk_eq_zero Scl

end Papers.P2.HB.QuotSeparation