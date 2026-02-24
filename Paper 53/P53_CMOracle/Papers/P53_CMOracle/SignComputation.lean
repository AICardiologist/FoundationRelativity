/-
  Paper 53: The CM Decidability Oracle — Fourfold Extension
  File F6: SignComputation.lean — Tr(c), sign, and Hodge-Riemann check

  The main computation: for Milne's CM abelian fourfold X = A × B,
  compute deg(w · w) and verify the Hodge-Riemann prediction.

  Hodge-Riemann bilinear relations (n = 4, p = q = 2, real class):
    (-1)^{n(n-1)/2} · i^{p-q} · ∫ α ∧ ᾱ > 0
    = (-1)^6 · 1 · deg(w²) > 0
    ⟹ deg(w · w) > 0

  Result: deg(w · w) = 7 > 0.  ✓ Hodge-Riemann confirmed.
-/
import Papers.P53_CMOracle.RegressionTest
import Papers.P53_CMOracle.MilneExample

namespace Papers.P53

-- ============================================================
-- §1. Milne Fourfold: Self-Intersection Computation
-- ============================================================

-- Cross-pairing for Milne's fourfold: c = 7/2 ∈ ℚ ⊂ ℚ(√-3)
#eval crossPairing milneH         -- Expected: 7/2

-- Self-intersection: deg(w · w) = Tr(c) = 7
#eval weilSelfIntersection milneH  -- Expected: 7

-- ============================================================
-- §2. Hodge-Riemann Sign Check
-- ============================================================

/-- Hodge-Riemann check for a Weil-type fourfold:
    For n = 4, p = q = 2: HR predicts deg(w · w) > 0.
    Returns true iff the prediction holds. -/
def hodgeRiemannCheck (H : WeilHermitian 2) : Bool :=
  decide (weilSelfIntersection H > 0)

-- Milne's fourfold: Hodge-Riemann ✓
#eval hodgeRiemannCheck milneH    -- Expected: true

-- J×J: Hodge-Riemann ✓
#eval hodgeRiemannCheck testH_JxJ -- Expected: true

-- ============================================================
-- §3. Comparative Analysis
-- ============================================================

-- Side-by-side comparison of J×J and Milne
#eval (
  testH_JxJ.det,                    -- J×J det
  milneH.det,                       -- Milne det
  weilSelfIntersection testH_JxJ,   -- J×J deg(w²)
  weilSelfIntersection milneH,      -- Milne deg(w²)
  hodgeRiemannCheck testH_JxJ,      -- J×J HR
  hodgeRiemannCheck milneH          -- Milne HR
)
-- Expected: (1, 1, 7, 7, true, true)

-- ============================================================
-- §4. B²(X) Intersection Form Demonstrations
-- ============================================================

-- Demonstrate the 3×3 form for Milne: Q(a,b,c) = ac + 3b²
-- On the Weil conic C_K (ac = 4b²):
#eval B2_intersectionForm milneH 4 1 1    -- = 1·(4 + 3) = 7
#eval B2_intersectionForm milneH 2 1 2    -- = 1·(4 + 3) = 7
#eval B2_intersectionForm milneH 1 1 4    -- = 1·(4 + 3) = 7

-- On the square-zero locus S₀ (ac = -3b²):
#eval B2_intersectionForm milneH 3 1 (-1) -- = 1·(-3 + 3) = 0
#eval B2_intersectionForm milneH 1 1 (-3) -- = 1·(-3 + 3) = 0

-- ============================================================
-- §5. Summary
-- ============================================================

/-- The complete sign computation result:
    For Milne's CM abelian fourfold X = A × B:
    • K = ℚ(√-3), H = diag(1,-1,-1,1), det H = 1
    • Cross-pairing c = 7/2 ∈ ℚ ⊂ K
    • Self-intersection deg(w · w) = Tr_{K/ℚ}(c) = 7 > 0
    • Hodge-Riemann bilinear relations: confirmed ✓
    • The Weil class is exotic (lies outside the Lefschetz ring)
    • The Weil class is algebraic (Schoen 1998) -/
def signComputationSummary : String :=
  let si := weilSelfIntersection milneH
  let hr := hodgeRiemannCheck milneH
  s!"deg(w·w) = {si}, Hodge-Riemann = {hr}"

#eval signComputationSummary
-- Expected: "deg(w·w) = 7, Hodge-Riemann = true"

end Papers.P53
