/-
  Paper 53: The CM Decidability Oracle
  File 7: Examples.lean — Concrete #eval demonstrations

  The computational certificates: the oracle runs, produces output,
  and the outputs match hand-computed values from CM theory.
-/
import Papers.P53_CMOracle.Decider
import Papers.P53_CMOracle.RosatiCheck

namespace Papers.P53

-- ============================================================
-- §1. QuadFieldQ Arithmetic Tests
-- ============================================================

-- D = -4: ℚ(√-4), elements represent a + b·(2i) where √(-4) = 2i
-- ω = ⟨0, 1⟩ represents 0 + 1·√(-4) = 2i
-- deg(ω) = Nm(2i) = 0² - (-4)·1² = 4
#eval (cmGenerator (-4) : QuadFieldQ (-4))
#eval (cmGenerator (-4)).norm         -- expect: 4

-- id - ω = ⟨1, 0⟩ - ⟨0, 1⟩ = ⟨1, -1⟩ represents 1 - 2i
-- deg(1 - ω) = 1² - (-4)·(-1)² = 1 + 4 = 5
#eval (endId (-4) - cmGenerator (-4) : QuadFieldQ (-4))
#eval (endId (-4) - cmGenerator (-4)).norm  -- expect: 5

-- D = -3: ℚ(√-3), ω = (1+√-3)/2 = ⟨1/2, 1/2⟩ (a cube root of unity)
-- deg(ω) = (1/2)² - (-3)·(1/2)² = 1/4 + 3/4 = 1
#eval (cmGenerator (-3) : QuadFieldQ (-3))
#eval (cmGenerator (-3)).norm         -- expect: 1

-- D = -163: ℚ(√-163), ω = (1+√-163)/2 = ⟨1/2, 1/2⟩
-- deg(ω) = (1/2)² - (-163)·(1/2)² = 1/4 + 163/4 = 164/4 = 41
#eval (cmGenerator (-163) : QuadFieldQ (-163))
#eval (cmGenerator (-163)).norm       -- expect: 41

-- ============================================================
-- §2. Intersection Matrix for D = -4 (j = 1728)
-- ============================================================

-- Expected matrix:
-- ┌  0  1  1  1 ┐
-- │  1  0  1  4 │
-- │  1  1  0  5 │
-- └  1  4  5  0 ┘
-- where deg(ω) = 4 and deg(1-ω) = 5

#eval (intersectionMatrix_E2 (-4) 0 0,
       intersectionMatrix_E2 (-4) 0 1,
       intersectionMatrix_E2 (-4) 0 2,
       intersectionMatrix_E2 (-4) 0 3)
-- expect: (0, 1, 1, 1)

#eval (intersectionMatrix_E2 (-4) 1 0,
       intersectionMatrix_E2 (-4) 1 1,
       intersectionMatrix_E2 (-4) 1 2,
       intersectionMatrix_E2 (-4) 1 3)
-- expect: (1, 0, 1, 4)

#eval (intersectionMatrix_E2 (-4) 2 0,
       intersectionMatrix_E2 (-4) 2 1,
       intersectionMatrix_E2 (-4) 2 2,
       intersectionMatrix_E2 (-4) 2 3)
-- expect: (1, 1, 0, 5)

#eval (intersectionMatrix_E2 (-4) 3 0,
       intersectionMatrix_E2 (-4) 3 1,
       intersectionMatrix_E2 (-4) 3 2,
       intersectionMatrix_E2 (-4) 3 3)
-- expect: (1, 4, 5, 0)

-- ============================================================
-- §3. Oracle Demonstrations
-- ============================================================

-- Test 1: Zero cycle ≡_num zero cycle → true
#eval numericallyEquivalent_E2 (-4)
  (by native_decide)
  ⟨fun _ => 0⟩
  ⟨fun _ => 0⟩
-- expect: true

-- Test 2: Is [Δ] ≡_num [E×0] + [0×E]?
-- Z = [Δ] - [E×0] - [0×E] = (-1, -1, 1, 0)
-- M·Z: row 0 = 0(-1)+1(-1)+1(1)+1(0) = 0
--       row 1 = 1(-1)+0(-1)+1(1)+4(0) = 0
--       row 2 = 1(-1)+1(-1)+0(1)+5(0) = -2
--       row 3 = 1(-1)+4(-1)+5(1)+0(0) = 0
-- M·Z = (0, 0, -2, 0) ≠ 0, so NOT numerically equivalent
#eval numericallyEquivalent_E2 (-4)
  (by native_decide)
  ⟨fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0⟩   -- [Δ]
  ⟨fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0⟩   -- [E×0] + [0×E]
-- expect: false

-- Test 3: A cycle numerically equivalent to itself
#eval numericallyEquivalent_E2 (-4)
  (by native_decide)
  ⟨fun | 0 => 3 | 1 => -2 | 2 => 1 | 3 => 7⟩
  ⟨fun | 0 => 3 | 1 => -2 | 2 => 1 | 3 => 7⟩
-- expect: true

-- ============================================================
-- §4. Intersection Pairing Computations
-- ============================================================

-- deg([Δ] · [E×0]) = M(2,0) = 1
#eval intersect_E2 (-4)
  ⟨fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0⟩  -- [Δ]
  ⟨fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 0⟩  -- [E×0]
-- expect: 1

-- deg([Γ_ω] · [Δ]) = M(3,2) = deg(1-ω) = 5
#eval intersect_E2 (-4)
  ⟨fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1⟩  -- [Γ_ω]
  ⟨fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 0⟩  -- [Δ]
-- expect: 5

-- ============================================================
-- §5. Rosati / Non-Degeneracy Check
-- ============================================================

-- Non-degeneracy of intersection matrix for D = -4
#eval det4 (intersectionMatrix_E2 (-4))
-- expect: nonzero

-- Rosati check for all 13 CM curves
#eval allRosatiCheck
-- expect: all (D, true)

#eval allRosatiPass
-- expect: true

-- ============================================================
-- §6. All CM Curves: Oracle Sanity Check
-- ============================================================

-- The oracle runs on all 13 discriminants (zero ≡_num zero)
#eval allCMDecidable
-- expect: true

-- Degree of ω for each discriminant (informational)
#eval cmDiscriminants.map (fun D => (D, degOmega D))

-- Degree of (1 - ω) for each discriminant (informational)
#eval cmDiscriminants.map (fun D => (D, degIdMinusOmega D))

end Papers.P53
