/-
Papers/P7_PhysicalBidualGap/ReflexiveDual.lean
Module 1 (Lemma A): If X is reflexive, then X* is reflexive.

Proof idea: Given φ ∈ (X*)** = X***, construct f = φ ∘ J_X ∈ X*.
Then J_{X*}(f) = φ because for all Ψ ∈ X**, by surjectivity of J_X,
Ψ = J_X(x) for some x, and J_{X*}(f)(Ψ) = Ψ(f) = J_X(x)(f) = f(x)
= φ(J_X(x)) = φ(Ψ).
-/
import Papers.P7_PhysicalBidualGap.Basic

noncomputable section
namespace Papers.P7

open NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- If X is reflexive, then X* is reflexive.
    Proof: for φ ∈ X***, take f = φ ∘ J_X ∈ X*. Then J_{X*}(f) = φ
    by checking on the (surjective) image of J_X. -/
theorem reflexive_dual_of_reflexive
    (hX : IsReflexive 𝕜 X) :
    IsReflexive 𝕜 (StrongDual 𝕜 X) := by
  intro φ
  -- Construct f := φ ∘ J_X : X → 𝕜, which is in X*
  let f : StrongDual 𝕜 X := φ.comp (inclusionInDoubleDual 𝕜 X)
  use f
  -- Need: J_{X*}(f) = φ, i.e., ∀ Ψ : X**, Ψ(f) = φ(Ψ)
  ext Ψ
  -- Use surjectivity of J_X: obtain x with J_X(x) = Ψ
  obtain ⟨x, hx⟩ := hX Ψ
  -- J_{X*}(f)(Ψ) = Ψ(f) = J_X(x)(f) = f(x) = φ(J_X(x)) = φ(Ψ)
  -- Goal: (inclusionInDoubleDual 𝕜 (StrongDual 𝕜 X)) f Ψ = φ Ψ
  -- LHS = Ψ(f)  and  Ψ = J_X(x) = inclusionInDoubleDual 𝕜 X x  so  Ψ(f) = f(x)
  -- f = φ ∘ J_X  so  f(x) = φ(J_X(x)) = φ(Ψ)
  change Ψ f = φ Ψ
  rw [← hx]
  rfl

/-- Contrapositive: if X* is not reflexive, then X is not reflexive. -/
theorem not_reflexive_of_dual_not_reflexive
    (h : ¬ IsReflexive 𝕜 (StrongDual 𝕜 X)) : ¬ IsReflexive 𝕜 X :=
  fun hX => h (reflexive_dual_of_reflexive hX)

end Papers.P7
