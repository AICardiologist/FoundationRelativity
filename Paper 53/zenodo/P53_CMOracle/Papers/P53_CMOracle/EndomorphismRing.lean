/-
  Paper 53: The CM Decidability Oracle
  File 2: EndomorphismRing.lean — Endomorphism ring generators for each CM discriminant

  For each of the 13 CM discriminants D, the endomorphism ring End(E) is an
  order O_D in K = ℚ(√D). The generator ω (beyond the identity) determines
  the full algebra End(E) ⊗ ℚ = K.
-/
import Papers.P53_CMOracle.CMData

namespace Papers.P53

-- ============================================================
-- §1. CM Generators
-- ============================================================

/-- The CM generator ω for each discriminant.
    For maximal orders (D ≡ 1 mod 4): ω = (1 + √D)/2
    For non-maximal orders (D ≡ 0 mod 4 or non-squarefree): ω = √D

    The generator represents the endomorphism beyond the identity.
    Together {1, ω} forms a ℚ-basis for End(E) ⊗ ℚ = K. -/
def cmGenerator (D : Int) : QuadFieldQ D :=
  match D with
  -- Maximal orders: D squarefree, D ≡ 1 (mod 4)
  -- ω = (1 + √D)/2, i.e., re = 1/2, im = 1/2
  | -3   => ⟨1/2, 1/2⟩   -- ℤ[ζ₃] ⊂ ℚ(√-3)
  | -7   => ⟨1/2, 1/2⟩   -- O_K maximal in ℚ(√-7)
  | -11  => ⟨1/2, 1/2⟩   -- O_K maximal in ℚ(√-11)
  | -19  => ⟨1/2, 1/2⟩   -- O_K maximal in ℚ(√-19)
  | -43  => ⟨1/2, 1/2⟩   -- O_K maximal in ℚ(√-43)
  | -67  => ⟨1/2, 1/2⟩   -- O_K maximal in ℚ(√-67)
  | -163 => ⟨1/2, 1/2⟩   -- O_K maximal in ℚ(√-163)
  -- Non-maximal orders or D ≡ 0 (mod 4):
  -- ω = √D, i.e., re = 0, im = 1
  | -4   => ⟨0, 1⟩        -- ℤ[√-4] = ℤ[2i], order in ℤ[i]
  | -8   => ⟨0, 1⟩        -- ℤ[√-8] = ℤ[2√-2], order in ℤ[√-2]
  | -12  => ⟨0, 1⟩        -- ℤ[√-12] = ℤ[2√-3], order in ℤ[√-3]
  | -16  => ⟨0, 1⟩        -- ℤ[√-16] = ℤ[4i], order in ℤ[i]
  | -27  => ⟨0, 1⟩        -- ℤ[√-27] = ℤ[3√-3], order in ℤ[ζ₃]
  | -28  => ⟨0, 1⟩        -- ℤ[√-28] = ℤ[2√-7], order in ℤ[(1+√-7)/2]
  -- Default (unreachable for valid CM discriminants)
  | _    => ⟨0, 0⟩

-- ============================================================
-- §2. Endomorphism Degree and Trace
-- ============================================================

/-- Degree of an endomorphism α ∈ K: deg(α) = Nm_{K/ℚ}(α) = α·ᾱ.
    For α = a + b√D: deg(α) = a² - Db².
    Since D < 0: deg(α) = a² + |D|b² ≥ 0. -/
def endDeg (z : QuadFieldQ D) : Rat := z.norm

/-- Trace of an endomorphism α ∈ K: Tr(α) = α + ᾱ = 2·re(α). -/
def endTrace (z : QuadFieldQ D) : Rat := z.tr

/-- The identity endomorphism: 1 ∈ End(E) -/
def endId (D : Int) : QuadFieldQ D := ⟨1, 0⟩

/-- The CM endomorphism ω ∈ End(E) -/
def endOmega (D : Int) : QuadFieldQ D := cmGenerator D

-- ============================================================
-- §3. Precomputed Degrees for Each Discriminant
-- ============================================================

/-- deg(ω) = Nm(cmGenerator D) for each D.
    This determines the (1,3) and (3,1) entries of the intersection matrix. -/
def degOmega (D : Int) : Rat := (cmGenerator D).norm

/-- deg(1 - ω) = Nm(1 - cmGenerator D) for each D.
    This determines the (2,3) and (3,2) entries of the intersection matrix. -/
def degIdMinusOmega (D : Int) : Rat := (endId D - cmGenerator D).norm

end Papers.P53
