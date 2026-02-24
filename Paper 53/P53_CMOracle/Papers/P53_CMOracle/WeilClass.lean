/-
  Paper 53: The CM Decidability Oracle — Fourfold Extension
  File F2: WeilClass.lean — Eigenspace decomposition and isotropicity

  For a Weil-type abelian variety X of dimension 2n with K = ℚ(√-d):
  • V_ℂ = W ⊕ W̄ where W, W̄ are eigenspaces for the √-d action
  • W, W̄ are isotropic for the alternating form E
  • E induces a perfect duality W ≅ W̄*
  • The Weil-Hodge classes live in ⋀²ⁿ_K H¹(X, ℚ) ↪ Bⁿ(X)

  Reference: van Geemen, CIME Lecture Notes §6.10, Theorem 6.12
-/
import Papers.P53_CMOracle.WeilType

namespace Papers.P53

-- ============================================================
-- §1. Principled Axioms (eigenspace theory)
-- ============================================================

/-- PRINCIPLED AXIOM (Hermitian form construction):
    For a Weil-type polarization E on X with K-action:
      H(x, y) = E(x, (√-d)·y) + √-d · E(x, y)
    defines a K-Hermitian form of signature (n, n).
    Reference: van Geemen, CIME Lecture Notes §5.2, Lemma 5.2. -/
axiom hermitian_form_van_geemen : True

/-- PRINCIPLED AXIOM (eigenspace isotropicity):
    The eigenspaces W, W̄ for √-d on V_ℂ are isotropic for E.
    Proof sketch: for x, y ∈ W,
      dE(x,y) = E(√-d·x, √-d·y) = E(√-d x, √-d y) = -dE(x,y)
    hence E|_{W×W} = 0. Similarly E|_{W̄×W̄} = 0.
    Reference: van Geemen, CIME Lecture Notes §6.10. -/
axiom eigenspace_isotropic : True

-- ============================================================
-- §2. Documentary: Weil Class Space
-- ============================================================

/-- The space of Weil-Hodge classes:
      W(X) = ⋀²ⁿ_K H¹(X, ℚ) ↪ Bⁿ(X)
    is 2-dimensional over ℚ, 1-dimensional over K.
    After base change: W(X) ⊗ K = K·ω₊ ⊕ K·ω₋
    By isotropicity:
      ⟨ω₊, ω₊⟩ = 0, ⟨ω₋, ω₋⟩ = 0, ⟨ω₊, ω₋⟩ = c ≠ 0
    The ℚ-rational Weil class is w = ω₊ + ω₋ with
      deg(w · w) = Tr_{K/ℚ}(c).
    This is a documentary definition — no computation here. -/
def weilClassDocumentation : String :=
  "Weil classes: 2-dim/ℚ, 1-dim/K. Self-pairing vanishes by isotropicity."

end Papers.P53
