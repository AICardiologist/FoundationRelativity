/-
  Paper 53: The CM Decidability Oracle
  File 1: CMData.lean — CM discriminants, quadratic field arithmetic, field norm

  The 13 imaginary quadratic fields with class number 1 correspond to the
  13 CM elliptic curves over ℚ. We represent elements of K = ℚ(√D) as
  pairs (re, im) ∈ ℚ × ℚ with fully computable arithmetic, enabling #eval.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Papers.P53

-- ============================================================
-- §1. The 13 CM Discriminants
-- ============================================================

/-- The 13 discriminants of imaginary quadratic orders with class number 1.
    These correspond to the 13 CM elliptic curves over ℚ. -/
def cmDiscriminants : List Int :=
  [-3, -4, -7, -8, -11, -12, -16, -19, -27, -28, -43, -67, -163]

-- ============================================================
-- §2. The Quadratic Field ℚ(√D)
-- ============================================================

/-- Elements of ℚ(√D): pairs (a, b) representing a + b√D with a, b ∈ ℚ.
    Fully computable — no Mathlib NumberField infrastructure needed. -/
structure QuadFieldQ (D : Int) where
  re : Rat
  im : Rat
  deriving DecidableEq, BEq

instance {D : Int} : Repr (QuadFieldQ D) where
  reprPrec z _ :=
    if z.im == 0 then repr z.re
    else if z.re == 0 then repr z.im ++ "*√(" ++ repr D ++ ")"
    else repr z.re ++ " + " ++ repr z.im ++ "*√(" ++ repr D ++ ")"

namespace QuadFieldQ

variable {D : Int}

-- Algebraic instances (all computable)

instance : Zero (QuadFieldQ D) := ⟨⟨0, 0⟩⟩
instance : One (QuadFieldQ D) := ⟨⟨1, 0⟩⟩

instance : Neg (QuadFieldQ D) := ⟨fun z => ⟨-z.re, -z.im⟩⟩

instance : Add (QuadFieldQ D) :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

instance : Sub (QuadFieldQ D) :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

/-- Multiplication: (a + b√D)(c + d√D) = (ac + bdD) + (ad + bc)√D -/
instance : Mul (QuadFieldQ D) :=
  ⟨fun z w => ⟨z.re * w.re + D * z.im * w.im,
               z.re * w.im + z.im * w.re⟩⟩

/-- Scalar multiplication by ℚ -/
instance : HMul Rat (QuadFieldQ D) (QuadFieldQ D) :=
  ⟨fun q z => ⟨q * z.re, q * z.im⟩⟩

/-- Embedding ℚ → ℚ(√D) -/
def ofRat (q : Rat) : QuadFieldQ D := ⟨q, 0⟩

/-- The conjugate: conj(a + b√D) = a - b√D -/
def conj (z : QuadFieldQ D) : QuadFieldQ D := ⟨z.re, -z.im⟩

/-- Field norm: Nm(a + b√D) = a² - D·b².
    For D < 0, this is a² + |D|·b² ≥ 0, with equality iff z = 0. -/
def norm (z : QuadFieldQ D) : Rat :=
  z.re ^ 2 - D * z.im ^ 2

/-- Trace: Tr(a + b√D) = 2a -/
def tr (z : QuadFieldQ D) : Rat := 2 * z.re

-- ============================================================
-- §3. Norm Properties (zero sorry)
-- ============================================================

theorem norm_zero : (0 : QuadFieldQ D).norm = 0 := by
  show (0 : Rat) ^ 2 - ↑D * (0 : Rat) ^ 2 = 0
  ring

theorem norm_sub_comm (z w : QuadFieldQ D) :
    (z - w).norm = (w - z).norm := by
  show (z.re - w.re) ^ 2 - ↑D * (z.im - w.im) ^ 2 =
       (w.re - z.re) ^ 2 - ↑D * (w.im - z.im) ^ 2
  ring

theorem norm_neg (z : QuadFieldQ D) :
    (-z).norm = z.norm := by
  show (-z.re) ^ 2 - ↑D * (-z.im) ^ 2 = z.re ^ 2 - ↑D * z.im ^ 2
  ring

theorem norm_ofRat (q : Rat) :
    (ofRat q : QuadFieldQ D).norm = q ^ 2 := by
  show q ^ 2 - ↑D * (0 : Rat) ^ 2 = q ^ 2
  ring

end QuadFieldQ

-- ============================================================
-- §4. CM Elliptic Curve Data
-- ============================================================

/-- A CM elliptic curve is specified by its discriminant from the list of 13. -/
structure CMEllipticCurve where
  D : Int
  hD : D ∈ cmDiscriminants

/-- The j-invariant for each CM discriminant (informational). -/
def jInvariant : Int → Int
  | -3   => 0
  | -4   => 1728
  | -7   => -3375
  | -8   => 8000
  | -11  => -32768
  | -12  => 54000
  | -16  => 287496
  | -19  => -884736
  | -27  => -12288000
  | -28  => 16581375
  | -43  => -884736000
  | -67  => -147197952000
  | -163 => -262537412640768000
  | _    => 0

end Papers.P53
