/-
  Paper 53: The CM Decidability Oracle — Fourfold Extension
  File F1: WeilType.lean — Weil-type Hermitian forms on abelian varieties

  A Weil-type abelian variety X of dimension 2n has K = ℚ(√K_disc) embedding
  in End(X) ⊗ ℚ. The K-Hermitian form H attached to a polarization has
  signature (n, n) and diagonal entries h₁,...,h_{2n} ∈ ℚ.

  Reference: van Geemen, CIME Lecture Notes §5.2
-/
import Papers.P53_CMOracle.CMData

namespace Papers.P53

-- ============================================================
-- §1. Weil-Type Hermitian Form
-- ============================================================

/-- A Weil-type Hermitian form: diagonal over K = ℚ(√K_disc) with 2n entries.
    For an abelian variety of dimension 2n, the form has signature (n,n)
    on the K-vector space V = H¹(X, ℚ) of K-dimension 2n. -/
structure WeilHermitian (n : Nat) where
  K_disc : Int                          -- discriminant of K = ℚ(√K_disc)
  entries : Fin (2 * n) → Rat           -- diagonal entries h₁,...,h_{2n}

-- ============================================================
-- §2. Determinant (computable)
-- ============================================================

/-- Product of diagonal entries: det H = ∏ hᵢ.
    For signature (n,n): det H = (-1)ⁿ · a with a > 0 (van Geemen §5.2).
    Uses explicit fold for computability. -/
def WeilHermitian.det (H : WeilHermitian n) : Rat :=
  let indices := List.finRange (2 * n)
  indices.foldl (fun acc i => acc * H.entries i) 1

-- ============================================================
-- §3. Signature Checks (computable, Bool-valued)
-- ============================================================

/-- Count of positive diagonal entries. -/
def WeilHermitian.signaturePos (H : WeilHermitian n) : Nat :=
  ((List.finRange (2 * n)).filter (fun i => decide (H.entries i > 0))).length

/-- Count of negative diagonal entries. -/
def WeilHermitian.signatureNeg (H : WeilHermitian n) : Nat :=
  ((List.finRange (2 * n)).filter (fun i => decide (H.entries i < 0))).length

/-- Check that H has Weil-type signature (n, n). -/
def WeilHermitian.isWeilType (H : WeilHermitian n) : Bool :=
  H.signaturePos == n && H.signatureNeg == n

/-- For fourfold (n = 2): check det H > 0.
    van Geemen: det H = (-1)ⁿ · a with a > 0; for n = 2, det H = a > 0. -/
def WeilHermitian.detSign (H : WeilHermitian 2) : Bool :=
  decide (H.det > 0)

-- ============================================================
-- §4. Repr instance
-- ============================================================

instance {n : Nat} : Repr (WeilHermitian n) where
  reprPrec H _ :=
    let es := (List.finRange (2 * n)).map (fun i => toString (repr (H.entries i)))
    .text ("WeilHermitian(" ++ toString (repr H.K_disc) ++ ", diag(" ++ String.intercalate ", " es ++ "))")

end Papers.P53
