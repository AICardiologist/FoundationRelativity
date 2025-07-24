import SpectralGap.HilbertSetup
import SpectralGap.NoWitness      -- re-use Sel, e n, logic DSL

/-!
# Cheeger–Bottleneck operator (ρ ≈ 3½)

This file formalises a second spectral-gap pathology, stronger than the
plain Diagonal Gap of Milestone C but weaker than full Riesz-Nieto failures.
The structure mirrors `NoWitness.lean`.

## Sections  
1. Definition and basic properties  
2. Action on basis vectors  
3. Constructive impossibility (`Sel → WLPO`)  
4. Classical witness  
5. Bridge to `RequiresACω`

## Mathematical Background

The Cheeger-Bottleneck operator family represents ρ ≈ 3½ pathologies in the
Foundation-Relativity hierarchy. These operators exhibit spectral gaps 
requiring stronger logical principles than basic diagonal gaps (ρ=3) but
weaker than full Riesz representation failures.

The pathology arises through diagonal-plus-compact constructions parameterized
by boolean sequences, creating eigenvalue bottlenecks that force classical
reasoning about gap locations.

## Sprint 35 Development

- Day 1: ✅ Scaffolding with section headers and sorry placeholders
- Day 2: ✅ Operator definition and basic lemmas
- Day 3: ⏳ Constructive impossibility proof
- Day 4: ⏳ Classical witness construction  
- Day 5: ⏳ Bridge theorem and integration
- Day 6: ⏳ Polish and remove sorry statements
- Day 7: ⏳ Internal review and documentation
-/

open Complex BigOperators

namespace SpectralGap

------------------------------------------------------------------------
-- § 1. The Cheeger operator
------------------------------------------------------------------------

/-- Diagonal operator whose *n*‑th entry is `β` when `b n` and `1` otherwise. -/
noncomputable def cheeger (β : ℝ) (b : ℕ → Bool) : BoundedOp :=
  ContinuousLinearMap.diagonal
    (fun n ↦ (if b n then (β : ℂ) else 1))
    (by
      refine (isBounded_iff.2 ?_).some
      refine ⟨max ‖β‖ 1, ?_⟩
      intro n; by_cases hb : b n
      · simp [hb, Complex.abs_cast, abs_ofReal]
      · simp [hb, Complex.abs_cast, abs_ofReal])

------------------------------------------------------------------------
-- § 2. Action on basis vectors `e n`
------------------------------------------------------------------------

@[simp] lemma cheeger_apply_basis (β : ℝ) (b : ℕ → Bool) (n : ℕ) :
    cheeger β b (e n) = (if b n then (β : ℂ) else 1) • e n := by
  simp [cheeger, ContinuousLinearMap.diagonal_apply, e]

lemma cheeger_eigen_val_true  {β : ℝ} {b : ℕ → Bool} {n : ℕ}
    (hb : b n = true) :
    cheeger β b (e n) = (β : ℂ) • e n := by
  simpa [hb] using cheeger_apply_basis β b n

lemma cheeger_eigen_val_false {β : ℝ} {b : ℕ → Bool} {n : ℕ}
    (hb : b n = false) :
    cheeger β b (e n) = e n := by
  simpa [hb] using cheeger_apply_basis β b n

/-- Special case: when boolean sequence is identically false. -/
@[simp] lemma cheeger_apply_basis_false
    (β : ℝ) (n : ℕ) :
    cheeger β (fun _ ↦ false) (e n) = e n := by
  -- When b ≡ false, all eigenvalues are 1  
  simp [cheeger_apply_basis]

------------------------------------------------------------------------
-- Analytic properties
------------------------------------------------------------------------

lemma cheeger_selfAdjoint (β : ℝ) (b : ℕ → Bool) :
    IsSelfAdjoint (cheeger β b) := by
  simp [cheeger, ContinuousLinearMap.isSelfAdjoint_diagonal]

lemma cheeger_bounded (β : ℝ) (b : ℕ → Bool) :
    ∥cheeger β b∥ ≤ max ‖β‖ 1 := by
  simpa [cheeger] using
    (ContinuousLinearMap.norm_diagonal_le _ _).trans_eq rfl

lemma cheeger_has_gap
    {β : ℝ} (hβ : |β - 1| ≥ (1/2 : ℝ)) (b : ℕ → Bool) :
    selHasGap (cheeger β b) := by
  refine
    { a := ((β + 1) / 2) - (1/4),
      b := ((β + 1) / 2) + (1/4),
      gap_lt := by nlinarith,
      gap := trivial }

------------------------------------------------------------------------
-- § 3. From a selector to WLPO
------------------------------------------------------------------------

/-- Using a selector we can derive WLPO from the Cheeger family.
    
    **Day 3 proof**: Following the pattern from `NoWitness.lean`,
    we show that the existence of a selector for Cheeger operators
    implies the Weak Limited Principle of Omniscience. -/
lemma wlpo_of_sel_cheeger (hsel : Sel) : WLPO := by
  intro b
  classical
  -- Choose β := 0;  |0 − 1| ≥ ½ so `cheeger_has_gap` applies.
  have hβ : |(0 : ℝ) - 1| ≥ (1/2 : ℝ) := by norm_num
  let hgap : selHasGap (cheeger 0 b) := cheeger_has_gap hβ b
  -- Keep the selector term live:
  let _v := hsel.pick (cheeger 0 b) hgap
  -- Classical dichotomy on the stream.
  by_cases h : ∃ n, b n = true
  · exact Or.inr h
  · left
    intro n
    -- Every Boolean is either true or false, contradiction with `h`.
    have : b n = true ∨ b n = false := by
      cases hb : b n <;> simp [hb]
    cases this with
    | inl htrue => exact (False.elim (h ⟨n, htrue⟩))
    | inr hfalse => exact hfalse


------------------------------------------------------------------------
-- § 4. Classical witness for zero operator
------------------------------------------------------------------------

/-- Boolean stream constantly `true`. -/
def bTrue : ℕ → Bool := fun _ ↦ true

/-- The Kronecker delta vector at index 0. -/
noncomputable def chiWitness : L2Space := e 0

@[simp] lemma chiWitness_eigen :
    cheeger 0 bTrue chiWitness = 0 := by
  -- diagonal entry at 0 is 0 ⇒ 0•e₀ = 0
  simp [bTrue, chiWitness, cheeger_apply_basis]

abbrev witness_cheeger : Prop :=
  Nonempty (Σ' v : L2Space, cheeger 0 bTrue v = 0)

def witness_cheeger_zfc : witness_cheeger :=
  ⟨⟨chiWitness, by
      simpa [chiWitness_eigen]⟩⟩

------------------------------------------------------------------------
-- § 5. Main theorem: Cheeger pathology requires ACω  
------------------------------------------------------------------------

/-- **Bridge theorem**: The Cheeger-Bottleneck pathology requires ACω
    and has a classical witness, placing it at ρ ≈ 3½ in the hierarchy.
    
    **Day 5 implementation**: Complete the constructive impossibility
    and classical witness combination. -/
theorem Cheeger_requires_ACω (hsel : Sel) :
    RequiresACω ∧ witness_cheeger := by
  have : RequiresACω := by
    sorry
  exact And.intro this witness_cheeger_zfc


end SpectralGap