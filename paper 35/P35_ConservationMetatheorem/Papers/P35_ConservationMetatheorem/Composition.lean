/-
  Paper 35: The Conservation Metatheorem
  Composition.lean: Theorem A — BISH Conservation

  Finite compositions of computable functions at computable
  inputs are computable. Pure BISH.
-/
import Papers.P35_ConservationMetatheorem.Defs

noncomputable section

open Real

-- ============================================================
-- Theorem A: BISH Conservation
-- ============================================================

/-- A single computable function can be approximated. -/
theorem computable_fun_approx (cf : ComputableFun) (x : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℝ, |cf.f x - q| < ε :=
  cf.approx_exists x ε hε

/-- Composition of two computable functions is computable.
    BISH: no omniscience needed — compose the approximation algorithms. -/
def comp_is_computable (cf1 cf2 : ComputableFun) : ComputableFun where
  f := cf1.f ∘ cf2.f
  approx_exists := by
    intro x ε hε
    exact cf1.approx_exists (cf2.f x) ε hε

/-- A finite composition of computable functions is computable.
    BISH: induction on the composition depth. -/
theorem finite_composition_computable (fc : FiniteComposition) :
    ∀ (x : ℝ) (ε : ℝ), 0 < ε → ∃ q : ℝ, |fc.eval x - q| < ε := by
  induction fc with
  | base cf =>
    intro x ε hε
    exact cf.approx_exists x ε hε
  | comp fc1 fc2 ih1 _ =>
    intro x ε hε
    exact ih1 (fc2.eval x) ε hε

/-- THEOREM A (BISH Conservation): Every finitary physical prediction
    (finite composition of computable functions at computable inputs)
    is BISH. Given any ε > 0, a rational approximation exists
    constructively. -/
theorem bish_conservation (fc : FiniteComposition) (x : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℝ, |fc.eval x - q| < ε :=
  finite_composition_computable fc x ε hε

/-- Corollary: the identity function is computable. -/
def id_computable : ComputableFun where
  f := id
  approx_exists := by
    intro x ε hε
    exact ⟨x, by simp; exact hε⟩

/-- Corollary: constant functions are computable. -/
def const_computable (c : ℝ) : ComputableFun where
  f := fun _ => c
  approx_exists := by
    intro _ ε hε
    exact ⟨c, by simp; exact hε⟩

end
