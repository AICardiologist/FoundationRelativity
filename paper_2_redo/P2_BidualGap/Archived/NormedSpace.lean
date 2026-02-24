/-
  Papers/P2_BidualGap/Constructive/NormedSpace.lean
  
  Constructive normed spaces built on CReal.
  This avoids the classical assumptions in mathlib's normed spaces.
-/

import Papers.P2_BidualGap.Constructive.CReal

namespace Papers.P2_BidualGap.Constructive

open CReal

/-- A constructive normed space over CReal -/
class CNormedSpace (E : Type*) extends AddCommGroup E where
  norm : E → CReal
  norm_zero : equiv (norm 0) zero
  norm_add_le : ∀ x y, ¬lt (add (norm x) (norm y)) (norm (x + y))
  norm_smul : ∀ (a : CReal) (x : E), equiv (norm (a • x)) (mul (abs a) (norm x))
  -- Note: We cannot prove norm_pos without decidability

/-- Continuous linear maps between constructive normed spaces -/
structure ContinuousLinearMap (E F : Type*) [CNormedSpace E] [CNormedSpace F] where
  toFun : E → F
  map_add : ∀ x y, toFun (x + y) = toFun x + toFun y
  map_smul : ∀ (a : CReal) x, toFun (a • x) = a • toFun x
  bound : CReal
  bound_pos : lt zero bound
  le_bound : ∀ x, ¬lt (mul bound (norm x)) (norm (toFun x))

notation E " →L[" CReal "] " F => ContinuousLinearMap E F

/-- The dual space of a constructive normed space -/
def dual (E : Type*) [CNormedSpace E] := E →L[CReal] CReal

/-- The bidual of a constructive normed space -/
def bidual (E : Type*) [CNormedSpace E] := dual (dual E)

/-- The canonical embedding into the bidual -/
def canonicalEmbedding (E : Type*) [CNormedSpace E] : E → bidual E :=
  fun x => {
    toFun := fun φ => φ.toFun x
    map_add := fun φ ψ => by
      -- eval_x is linear: eval_x(φ + ψ) = eval_x(φ) + eval_x(ψ)
      sorry -- TODO: Need to define addition on dual space first
    map_smul := fun c φ => by
      -- eval_x is linear: eval_x(c • φ) = c • eval_x(φ)
      sorry -- TODO: Need to define scalar multiplication on dual space first
    bound := norm x
    bound_pos := sorry -- Requires showing norm x > 0 when x ≠ 0
    le_bound := sorry -- Requires Hahn-Banach type argument
  }

/-- A space has the bidual gap property if canonical embedding is not surjective -/
def hasBidualGap (E : Type*) [CNormedSpace E] : Prop :=
  ∃ (Φ : bidual E), ∀ (x : E), ¬(equiv (Φ.toFun) ((canonicalEmbedding E x).toFun))

/-- A subspace is located if we can compute distances to it -/
structure Located (E : Type*) [CNormedSpace E] (S : Set E) where
  dist : E → CReal
  dist_property : ∀ x, ∀ ε, lt zero ε → 
    (x ∈ S → lt (dist x) ε) ∧ 
    (∃ y ∈ S, lt (norm (x - y)) (add (dist x) ε))

end Papers.P2_BidualGap.Constructive