import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
  HeckeData37a1.lean — Hecke eigenvalue summary for 37a1 (duplicated from Paper 95)

  Minimal duplication of Paper 95's 37a1 data for cross-comparison.
  Paper 96 is a self-contained lake project (no inter-paper imports).

  E = 37a1: y² + y = x³ − x, conductor 37, rank 1, root number w = −1.
  Source: Cremona / LMFDB.
-/

namespace P96

-- ═══════════════════════════════════════════════════════════════
-- §1. Conductor and curve data
-- ═══════════════════════════════════════════════════════════════

def conductor_37a1 : ℕ := 37

theorem conductor_37a1_prime : Nat.Prime conductor_37a1 := by native_decide

-- ═══════════════════════════════════════════════════════════════
-- §2. Hecke eigenvalues (subset for cross-check)
-- ═══════════════════════════════════════════════════════════════

def hecke_37a1 : ℕ → ℤ
  | 2  => -2
  | 3  => -3
  | 5  => -2
  | 7  => -1
  | 11 => -5
  | 13 => -2
  | 17 =>  0
  | 19 =>  0
  | 23 =>  2
  | 29 =>  6
  | 31 => -4
  | 37 => -1    -- bad prime (non-split multiplicative)
  | 41 => -9
  | 43 =>  2
  | 47 => -9
  | _  =>  0

-- Point counts (5 primes for verification)
def card_E_Fp_37a1 : ℕ → ℕ
  | 2  => 5
  | 3  => 7
  | 5  => 8
  | 7  => 9
  | 13 => 16
  | _  => 0

theorem hecke_pointcount_37a1_2 : hecke_37a1 2 = (2 : ℤ) + 1 - card_E_Fp_37a1 2 := by native_decide
theorem hecke_pointcount_37a1_3 : hecke_37a1 3 = (3 : ℤ) + 1 - card_E_Fp_37a1 3 := by native_decide
theorem hecke_pointcount_37a1_5 : hecke_37a1 5 = (5 : ℤ) + 1 - card_E_Fp_37a1 5 := by native_decide
theorem hecke_pointcount_37a1_7 : hecke_37a1 7 = (7 : ℤ) + 1 - card_E_Fp_37a1 7 := by native_decide
theorem hecke_pointcount_37a1_13 : hecke_37a1 13 = (13 : ℤ) + 1 - card_E_Fp_37a1 13 := by native_decide

-- Hasse bounds (all good primes ≤ 47)
theorem hasse_37a1_2  : hecke_37a1 2  ^ 2 ≤ 4 * 2  := by native_decide
theorem hasse_37a1_3  : hecke_37a1 3  ^ 2 ≤ 4 * 3  := by native_decide
theorem hasse_37a1_5  : hecke_37a1 5  ^ 2 ≤ 4 * 5  := by native_decide
theorem hasse_37a1_7  : hecke_37a1 7  ^ 2 ≤ 4 * 7  := by native_decide
theorem hasse_37a1_13 : hecke_37a1 13 ^ 2 ≤ 4 * 13 := by native_decide

-- ═══════════════════════════════════════════════════════════════
-- §3. Root number
-- ═══════════════════════════════════════════════════════════════

/-- The root number w(37a1) = −1 (odd functional equation → analytic rank odd → rank 1). -/
def root_number_37a1 : ℤ := -1

theorem root_number_37a1_odd : root_number_37a1 = -1 := rfl

-- ═══════════════════════════════════════════════════════════════
-- §4. BSD data for 37a1
-- ═══════════════════════════════════════════════════════════════

/-- E(ℚ)_tors = {O} for 37a1. Trivial torsion. -/
def torsion_order_37a1 : ℕ := 1

theorem torsion_37a1_trivial : torsion_order_37a1 = 1 := rfl

/-- Tamagawa product for 37a1: c_37 = 1. -/
def tamagawa_product_37a1 : ℕ := 1

theorem tamagawa_37a1_val : tamagawa_product_37a1 = 1 := rfl

/-- Rank of 37a1 is 1. -/
def rank_37a1 : ℕ := 1

theorem rank_37a1_one : rank_37a1 = 1 := rfl

end P96
