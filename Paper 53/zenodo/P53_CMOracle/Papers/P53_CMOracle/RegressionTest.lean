/-
  Paper 53: The CM Decidability Oracle — Fourfold Extension
  File F4: RegressionTest.lean — J×J conic verification

  REGRESSION TEST against van Geemen (SIGMA 2022, arXiv:2108.02087):
  For X = J × J (ppav surface J), K = ℚ(i):
  • H = diag(1, 1, -1, -1), det H = 1
  • In basis {ω₁², ω_σ², ω₂²} for B²(X):
    - Weil class conic C_K:  4b² = ac
    - Square-zero locus S₀:  3b² = -ac

  Our intersection form Q(a,b,c) = det(H) · (ac + 3b²) = ac + 3b²
  must match these identities.

  Reference: van Geemen, SIGMA 18 (2022), 011; arXiv:2108.02087
-/
import Papers.P53_CMOracle.CrossPairing

namespace Papers.P53

-- ============================================================
-- §1. J × J Test Case
-- ============================================================

/-- J × J: product of ppav surface with itself.
    K = ℚ(i), disc = -1. H = diag(1, 1, -1, -1). -/
def testH_JxJ : WeilHermitian 2 where
  K_disc := -1
  entries := fun | 0 => 1 | 1 => 1 | 2 => -1 | 3 => -1

-- Basic checks
#eval testH_JxJ.det            -- Expected: 1
#eval testH_JxJ.isWeilType     -- Expected: true
#eval testH_JxJ.detSign        -- Expected: true

-- ============================================================
-- §2. Regression: Square-Zero Locus S₀
-- ============================================================

/-- S₀ = {3b² = -ac} in the (a,b,c) coordinates.
    Our form: Q(a,b,c) = det(H) · (ac + 3b²) = ac + 3b².
    On S₀: ac = -3b², so Q = -3b² + 3b² = 0.  ✓ -/
def checkS0 (a b c : Rat) : Bool :=
  -- If (a,b,c) is on S₀ (i.e., 3b² = -ac), then Q should vanish
  let onS0 := (3 * b ^ 2 == -a * c)
  let QVal := B2_intersectionForm testH_JxJ a b c
  !onS0 || QVal == 0   -- S₀ ⟹ Q = 0

-- Test specific points on S₀: ac = -3b²
-- Point: (3, 1, -1) → ac = 3·(-1) = -3 = -3·1² ✓
#eval checkS0 3 1 (-1)     -- Expected: true

-- Point: (1, 1, -3) → ac = 1·(-3) = -3 = -3·1² ✓
#eval checkS0 1 1 (-3)     -- Expected: true

-- Point: (6, 2, -2) → ac = 6·(-2) = -12 = -3·4 = -3·2² ✓
#eval checkS0 6 2 (-2)     -- Expected: true

-- ============================================================
-- §3. Regression: Weil Class Conic C_K
-- ============================================================

/-- C_K = {4b² = ac} in the (a,b,c) coordinates.
    On C_K: Q = det(H) · (4b² + 3b²) = 7 · det(H) · b².
    For det(H) = 1: Q = 7b² > 0 for b ≠ 0.  ✓ (positive) -/
def checkCK (a b c : Rat) : Bool :=
  -- If (a,b,c) is on C_K (i.e., 4b² = ac), then Q should be 7b² · det(H)
  let onCK := (4 * b ^ 2 == a * c)
  let QVal := B2_intersectionForm testH_JxJ a b c
  let expected := 7 * b ^ 2 * testH_JxJ.det
  !onCK || QVal == expected

-- Test specific points on C_K: ac = 4b²
-- Point: (4, 1, 1) → ac = 4 = 4·1² ✓, Q = 4 + 3 = 7 = 7·1² ✓
#eval checkCK 4 1 1         -- Expected: true

-- Point: (2, 1, 2) → ac = 4 = 4·1² ✓, Q = 4 + 3 = 7 = 7·1² ✓
#eval checkCK 2 1 2         -- Expected: true

-- Point: (1, 1, 4) → ac = 4 = 4·1² ✓, Q = 4 + 3 = 7 = 7·1² ✓
#eval checkCK 1 1 4         -- Expected: true

-- Point: (8, 2, 2) → ac = 16 = 4·4 = 4·2² ✓, Q = 16 + 12 = 28 = 7·4 = 7·2² ✓
#eval checkCK 8 2 2         -- Expected: true

-- ============================================================
-- §4. Self-Intersection Verification
-- ============================================================

-- The self-intersection for J×J:
-- deg(w · w) = 7 · det(H) = 7 · 1 = 7 > 0
#eval weilSelfIntersection testH_JxJ       -- Expected: 7
#eval crossPairing testH_JxJ               -- Expected: 7/2 ∈ ℚ(√-1)

-- ============================================================
-- §5. Comprehensive Regression Check
-- ============================================================

/-- Master regression check: all conditions must hold. -/
def regressionCheck : Bool :=
  -- (1) det H = 1
  testH_JxJ.det == 1
  -- (2) Signature is (2,2)
  && testH_JxJ.isWeilType
  -- (3) S₀ verified at test points
  && checkS0 3 1 (-1)
  && checkS0 1 1 (-3)
  && checkS0 6 2 (-2)
  -- (4) C_K verified at test points
  && checkCK 4 1 1
  && checkCK 2 1 2
  && checkCK 1 1 4
  && checkCK 8 2 2
  -- (5) Self-intersection positive
  && decide (weilSelfIntersection testH_JxJ > 0)
  -- (6) Specific value: deg(w·w) = 7
  && (weilSelfIntersection testH_JxJ == 7)

#eval regressionCheck     -- Expected: true

end Papers.P53
