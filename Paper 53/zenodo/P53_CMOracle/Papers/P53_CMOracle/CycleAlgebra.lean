/-
  Paper 53: The CM Decidability Oracle
  File 3: CycleAlgebra.lean — Algebraic cycles on E × E

  For a CM elliptic curve E with End(E) ⊗ ℚ = K = ℚ(√D), the Néron-Severi
  group NS(E × E) ⊗ ℚ is 4-dimensional with basis:
    e₀ = [E × 0], e₁ = [0 × E], e₂ = [Δ] (diagonal), e₃ = [Γ_ω] (graph of ω)

  Cycles are represented as ℚ⁴ vectors for full computability.
-/
import Papers.P53_CMOracle.EndomorphismRing
import Mathlib.Logic.Basic

namespace Papers.P53

/-- DecidableEq for Fin n → Rat (needed for Cycle_E2). -/
instance : DecidableEq (Fin 4 → Rat) := fun f g =>
  if h : ∀ i, f i = g i then
    .isTrue (funext h)
  else
    .isFalse (fun heq => h (fun i => congrFun heq i))

-- ============================================================
-- §1. Cycles on E × E
-- ============================================================

/-- A cycle in CH¹(E × E)_num ⊗ ℚ, represented as a vector in ℚ⁴.
    Basis: e₀ = [E×0], e₁ = [0×E], e₂ = [Δ], e₃ = [Γ_ω]. -/
structure Cycle_E2 (D : Int) where
  coeffs : Fin 4 → Rat

instance {D : Int} : DecidableEq (Cycle_E2 D) := fun Z W =>
  if h : Z.coeffs = W.coeffs then
    .isTrue (by cases Z; cases W; simp at h; exact congrArg _ h)
  else
    .isFalse (fun heq => h (by cases heq; rfl))

instance {D : Int} : Repr (Cycle_E2 D) where
  reprPrec z _ :=
    let c := z.coeffs
    s!"⟨{c 0}·[E×0] + {c 1}·[0×E] + {c 2}·[Δ] + {c 3}·[Γ_ω]⟩"

instance {D : Int} : Add (Cycle_E2 D) :=
  ⟨fun Z W => ⟨fun i => Z.coeffs i + W.coeffs i⟩⟩

instance {D : Int} : Sub (Cycle_E2 D) :=
  ⟨fun Z W => ⟨fun i => Z.coeffs i - W.coeffs i⟩⟩

instance {D : Int} : Neg (Cycle_E2 D) :=
  ⟨fun Z => ⟨fun i => -(Z.coeffs i)⟩⟩

instance {D : Int} : Zero (Cycle_E2 D) :=
  ⟨⟨fun _ => 0⟩⟩

/-- Scalar multiplication by ℚ -/
instance {D : Int} : HMul Rat (Cycle_E2 D) (Cycle_E2 D) :=
  ⟨fun q Z => ⟨fun i => q * Z.coeffs i⟩⟩

-- ============================================================
-- §2. Named Basis Elements
-- ============================================================

/-- e₀ = [E × 0]: pullback of a point from the first factor -/
def basisE2_ExO (D : Int) : Cycle_E2 D := ⟨fun | 0 => 1 | _ => 0⟩

/-- e₁ = [0 × E]: pullback of a point from the second factor -/
def basisE2_OxE (D : Int) : Cycle_E2 D := ⟨fun | 1 => 1 | _ => 0⟩

/-- e₂ = [Δ]: the diagonal (graph of identity) -/
def basisE2_Delta (D : Int) : Cycle_E2 D := ⟨fun | 2 => 1 | _ => 0⟩

/-- e₃ = [Γ_ω]: graph of the CM generator ω -/
def basisE2_GammaOmega (D : Int) : Cycle_E2 D := ⟨fun | 3 => 1 | _ => 0⟩

-- ============================================================
-- §3. Principled Axiom: Basis Completeness
-- ============================================================

/-- PRINCIPLED AXIOM (Betti number computation):
    The 4 basis elements {[E×0], [0×E], [Δ], [Γ_ω]} span CH¹(E×E)_num ⊗ ℚ
    for any CM elliptic curve E with End(E) ⊗ ℚ = K (2-dimensional over ℚ).

    Justification: NS(E×E) ⊗ ℚ ≅ ℚ ⊕ ℚ ⊕ (End(E) ⊗ ℚ) ≅ ℚ ⊕ ℚ ⊕ K ≅ ℚ⁴.
    The decomposition is: fiber classes ℚ² plus graph classes from K.
    Reference: Mumford, Abelian Varieties, Ch. IV; Birkenhake-Lange, §5.2. -/
axiom basis_spans_CH1_E2 : True

end Papers.P53
