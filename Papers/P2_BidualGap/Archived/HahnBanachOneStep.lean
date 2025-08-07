/-
  Papers/P2_BidualGap/Constructive/HahnBanachOneStep.lean
  
  One-step Hahn-Banach extension following senior professor's guidance:
  "The construction does not rely on maximal extension. It relies on 
  the one-step extension: extending g from Y to Y + span(x)."
-/

import Papers.P2_BidualGap.Constructive.RegularReal
import Papers.P2_BidualGap.Constructive.NormedSpace

namespace Papers.P2_BidualGap.Constructive

open RegularReal

/-- The Approximate Supremum Property (constructive version) -/
def ASP : Prop :=
  ∀ (S : Set RegularReal), 
  (∃ b, ∀ s ∈ S, le s b) →  -- S is bounded above
  (∃ x ∈ S, True) →         -- S is nonempty
  ∃ (sup : RegularReal), 
    (∀ s ∈ S, le s sup) ∧   -- sup is an upper bound
    (∀ ε > 0, ∃ s ∈ S, lt (sup - from_rat ε) s)  -- sup is least

/-- A linear functional on a subspace -/
structure LinearFunctional (Y : Set RegularReal) where
  f : Y → RegularReal
  is_linear : ∀ y₁ y₂ : Y, ∀ a b : ℚ,
    f ⟨a • y₁.val + b • y₂.val, sorry⟩ = from_rat a * f y₁ + from_rat b * f y₂
  is_bounded : ∃ M : RegularReal, ∀ y : Y, le (abs (f y)) M

/-- One-step extension data -/
structure OneStepExtension (Y : Set RegularReal) (x : RegularReal) where
  x_not_in_Y : x ∉ Y
  -- Y + span(x) = {y + λx : y ∈ Y, λ ∈ ℚ}

/-- The key lemma: bounds for the extension value -/
lemma extension_bounds (Y : Set RegularReal) (g : LinearFunctional Y) 
    (x : RegularReal) (hx : x ∉ Y) :
  ∃ (lower upper : RegularReal),
    (∀ y₁ y₂ : Y, le (g y₁ - g y₂) (upper - lower)) ∧
    (∀ v : RegularReal, le lower v → le v upper → 
      ∃ g' : LinearFunctional (Y ∪ {z | ∃ y : Y, ∃ λ : ℚ, z = y.val + from_rat λ * x}),
        (∀ y : Y, g' ⟨y.val, sorry⟩ = g y) ∧ 
        g' ⟨x, sorry⟩ = v) := by
  -- The bounds come from:
  -- lower = sup {g(y) - ‖y - x‖ : y ∈ Y}
  -- upper = inf {g(y) + ‖y - x‖ : y ∈ Y}
  sorry

/-- One-step Hahn-Banach extension theorem -/
theorem hahn_banach_one_step (hasp : ASP) 
    (Y : Set RegularReal) (g : LinearFunctional Y)
    (x : RegularReal) (hx : x ∉ Y) :
  ∃ g' : LinearFunctional (Y ∪ {z | ∃ y : Y, ∃ λ : ℚ, z = y.val + from_rat λ * x}),
    (∀ y : Y, g' ⟨y.val, sorry⟩ = g y) ∧
    (∃ M : RegularReal, ∀ z, le (abs (g'.f z)) M) := by
  -- Step 1: Get the bounds
  obtain ⟨lower, upper, h_bound, h_ext⟩ := extension_bounds Y g x hx
  
  -- Step 2: Use ASP to find a value v ∈ [lower, upper]
  -- This is where we need ASP! Classical math would just pick any value.
  -- Constructively, we need to build a Cauchy sequence converging to it.
  have h_interval : ∃ v, le lower v ∧ le v upper := by
    sorry -- TODO: Use ASP here
  obtain ⟨v, hlv, hvu⟩ := h_interval
  
  -- Step 3: Apply the extension with this v
  obtain ⟨g', hg'_extends, hg'_at_x⟩ := h_ext v hlv hvu
  
  use g'
  constructor
  · exact hg'_extends
  · -- The bound is preserved
    sorry

/-- Special case for c₀ ⊆ ℓ∞ -/
theorem hahn_banach_c_zero_located (hasp : ASP) :
  -- c₀ is located in ℓ∞
  ∀ (x : ℕ → RegularReal), 
  (∃ M, ∀ n, le (abs (x n)) M) →  -- x ∈ ℓ∞
  ∃ (d : RegularReal),
    (∀ y : ℕ → RegularReal, 
      (∀ ε > 0, ∃ N, ∀ n ≥ N, lt (abs (y n)) (from_rat ε)) →  -- y ∈ c₀
      le (dist_seq x y) d) ∧
    (∀ ε > 0, ∃ y : ℕ → RegularReal,
      (∀ ε' > 0, ∃ N, ∀ n ≥ N, lt (abs (y n)) (from_rat ε')) ∧  -- y ∈ c₀
      lt (dist_seq x y) (d + from_rat ε))
  where dist_seq (x y : ℕ → RegularReal) : RegularReal := sorry := by
  sorry -- TODO: Use MCT and one-step extension

end Papers.P2_BidualGap.Constructive