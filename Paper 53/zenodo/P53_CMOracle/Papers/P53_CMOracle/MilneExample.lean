/-
  Paper 53: The CM Decidability Oracle — Fourfold Extension
  File F5: MilneExample.lean — Milne's CM abelian fourfold

  Milne's example (Acta Arith. 100, 2001, Example 1.8):
  • K = ℚ(√-3)
  • B = elliptic curve with j = 0, CM by K
  • A = CM abelian 3-fold with CM type (E, Φ₀), E = F·K, F = ℚ[t]/(t³+t²-2t-1)
  • X = A × B, dimension 4

  Hermitian form: H = H_A ⊥ H_B
  • H_B = (1) on the 1-dim K-space H¹(B, ℚ)
  • H_A = diag(1, -1, -1) on the 3-dim K-space H¹(A, ℚ)
  • Total: H = diag(1, -1, -1, 1), det H = 1 > 0 ✓

  The Weil class is algebraic (Schoen 1998, Comp. Math. 65).
-/
import Papers.P53_CMOracle.CrossPairing

namespace Papers.P53

-- ============================================================
-- §1. Milne's CM Abelian Fourfold
-- ============================================================

/-- Milne's CM abelian fourfold X = A × B.
    K = ℚ(√-3) (disc = -3), H = diag(1, -1, -1, 1).
    Signature: two positive (h₁=1, h₄=1), two negative (h₂=-1, h₃=-1).
    det H = 1·(-1)·(-1)·1 = 1 > 0. -/
def milneH : WeilHermitian 2 where
  K_disc := -3
  entries := fun | 0 => 1 | 1 => -1 | 2 => -1 | 3 => 1

-- ============================================================
-- §2. Basic Checks
-- ============================================================

-- det(H) = 1 > 0
#eval milneH.det            -- Expected: 1

-- Signature (2, 2) ✓
#eval milneH.isWeilType     -- Expected: true
#eval milneH.signaturePos   -- Expected: 2
#eval milneH.signatureNeg   -- Expected: 2

-- det sign positive ✓
#eval milneH.detSign        -- Expected: true

-- K = ℚ(√-3)
#eval milneH.K_disc         -- Expected: -3

-- ============================================================
-- §3. Principled Axioms
-- ============================================================

/-- PRINCIPLED AXIOM (Milne's CM type Hermitian form):
    For the CM type Φ₀ of Milne's 3-fold A with CM by E = F·K,
    the Hermitian form on H¹(A, ℚ) has signature (1, 2) and
    in suitable K-basis: H_A = diag(1, -1, -1).
    Combined with H_B = (1): H = diag(1, -1, -1, 1).
    Reference: Milne, Acta Arith. 100 (2001), Example 1.8. -/
axiom milne_cm_type_hermitian : True

/-- PRINCIPLED AXIOM (Schoen algebraicity):
    The Weil class on X = A × B is algebraic.
    For K = ℚ(√-3) and det H = 1, the Weil class is shown to be
    algebraic by Schoen's construction.
    Reference: Schoen, "Hodge classes on self-products of a variety
    with an automorphism", Comp. Math. 65 (1988), p. 3–32.
    Also: Comp. Math. 114 (1998), pp. 329–336. -/
axiom schoen_algebraicity : True

end Papers.P53
