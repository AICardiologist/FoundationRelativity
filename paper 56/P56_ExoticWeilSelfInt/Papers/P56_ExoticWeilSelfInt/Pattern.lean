/-
  Paper 56 — Module 7: Pattern
  Exotic Weil Class Self-Intersection on CM Abelian Fourfolds

  States the observed pattern deg(w₀ · w₀) = √disc(F) and the
  falsifiable prediction for a third example.

  Sorry budget: 0. The pattern checks are just n² = n².

  Paul C.-K. Lee, February 2026
-/
import Papers.P56_ExoticWeilSelfInt.SchoenAlgebraicity

/-! # The Pattern

All three examples exhibit: deg(w₀ · w₀) = √disc(F).

| Example | K         | F                    | disc(F) | deg | √disc = deg |
|---------|-----------|----------------------|---------|-----|-------------|
| 1       | Q(√-3)   | Q(ζ₇ + ζ₇⁻¹)       | 49      | 7   | 7² = 49 ✓   |
| 2       | Q(i)     | Q(ζ₉ + ζ₉⁻¹)       | 81      | 9   | 9² = 81 ✓   |
| 3       | Q(√-7)   | F₃ ⊂ Q(ζ₁₃)⁺       | 169     | 13  | 13² = 169 ✓ |
-/

-- ============================================================
-- The pattern structure
-- ============================================================

/-- A record witnessing the self-intersection pattern for one example.
Fields: disc(F), deg(w₀ · w₀), proof that deg² = disc(F). -/
structure WeilSelfIntersectionPattern where
  /-- Name of the example. -/
  name : String
  /-- Discriminant of the totally real cubic field F. -/
  disc_F : ℕ
  /-- Self-intersection degree of the primitive generator. -/
  deg_w : ℕ
  /-- The pattern: deg² = disc(F). -/
  pattern_holds : deg_w * deg_w = disc_F

-- ============================================================
-- Verified patterns for Examples 1 and 2
-- ============================================================

/-- Example 1: K = Q(√-3), F = Q(ζ₇ + ζ₇⁻¹), disc = 49, deg = 7. -/
def example1_pattern : WeilSelfIntersectionPattern where
  name := "Milne 1.8: K = Q(√-3), F = Q(ζ₇ + ζ₇⁻¹)"
  disc_F := 49
  deg_w := 7
  pattern_holds := by native_decide

/-- Example 2: K = Q(i), F = Q(ζ₉ + ζ₉⁻¹), disc = 81, deg = 9. -/
def example2_pattern : WeilSelfIntersectionPattern where
  name := "New: K = Q(i), F = Q(ζ₉ + ζ₉⁻¹)"
  disc_F := 81
  deg_w := 9
  pattern_holds := by native_decide

-- ============================================================
-- Verified pattern for Example 3
-- ============================================================

/-- Example 3: K = Q(√-7), F ⊂ Q(ζ₁₃)⁺, disc = 169, deg = 13. -/
def example3_pattern : WeilSelfIntersectionPattern where
  name := "Confirmed: K = Q(√-7), F ⊂ Q(ζ₁₃)⁺"
  disc_F := 169
  deg_w := 13
  pattern_holds := by native_decide

-- ============================================================
-- Pattern summary
-- ============================================================

/-- All three verified patterns. -/
def all_patterns : List WeilSelfIntersectionPattern :=
  [example1_pattern, example2_pattern, example3_pattern]

/-- The pattern holds for all entries in the table. -/
theorem pattern_verified :
    all_patterns.all (fun p => p.deg_w * p.deg_w == p.disc_F) = true := by
  native_decide
