/-
  Test file for Product Height theorems
  Verifies the parity lemmas and lift proofs work correctly
  Now includes tests for the new k-ary schedule API
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_ProductHeight
import Papers.P3_2CatFramework.P4_Meta.PartIII_Schedule

namespace Papers.P4Meta

open Papers.P4Meta

-- Test the parity lemmas really fire
example {A B : Nat → Formula} (n : Nat) : fuseSteps A B (2*n) = A n := by
  simp [fuseSteps_even]

example {A B : Nat → Formula} (n : Nat) : fuseSteps A B (2*n+1) = B n := by
  simp [fuseSteps_odd]

-- NEW: Test that evenOddSchedule matches fuseSteps behavior
example {A B : Nat → Formula} (n : Nat) :
    scheduleSteps evenOddSchedule (fun i => if i = 0 then A else B) (2*n) = A n := by
  simp [evenOdd_bridge_even]

example {A B : Nat → Formula} (n : Nat) :
    scheduleSteps evenOddSchedule (fun i => if i = 0 then A else B) (2*n+1) = B n := by
  simp [evenOdd_bridge_odd]

-- Test the simp lemmas work
example (n : Nat) : 2 * (n + 1) = 2 * n + 2 := by rw [Nat.mul_succ]
example (n : Nat) : (2 * n + 1) + 1 = 2 * n + 2 := by simp

-- Verify the lift theorems are available and type-check
section LiftTests
  variable {T : Theory} {A B : Nat → Formula} {φ ψ : Formula}
  variable (cφ : HeightCertificate T A φ)
  variable (cψ : HeightCertificate T B ψ)
  
  -- Note: Many of these theorems were renamed or not implemented
  -- Keeping the ones that exist:
  
  -- Basic lifts
  #check liftA_to_fuse_even cφ
  #check liftB_to_fuse_odd cψ
  
  -- The main upper bound theorems (with updated names)
  #check product_height_le_2max_plus1 cφ cψ
  
  -- With independence assumption
  variable [AxisIndependent T A B]
  #check product_height_eq_2max_plus1 cφ cψ
  
  -- Pair utility
  #check pair_on_fuse_upper cφ cψ
  
  -- Note: Many other theorems from the original list don't exist
  -- or have different names in the current implementation
end LiftTests

/-! ## NEW: k-ary Schedule API Tests -/

-- Simple toy axes families to keep the tests concrete
def axes2 : Fin 2 → Nat → Formula
| ⟨0, _⟩, n => Formula.atom (1000 + n)
| ⟨1, _⟩, n => Formula.atom (2000 + n)

def axes3 : Fin 3 → Nat → Formula
| ⟨0, _⟩, n => Formula.atom (1000 + n)
| ⟨1, _⟩, n => Formula.atom (2000 + n)
| ⟨2, _⟩, n => Formula.atom (3000 + n)

/-! ### k = 2: parity bridges -/

example (n : Nat) :
    scheduleSteps evenOddSchedule axes2 (2 * n) = axes2 ⟨0, by decide⟩ n := by
  simp [evenOdd_bridge_even]

example (n : Nat) :
    scheduleSteps evenOddSchedule axes2 (2 * n + 1) = axes2 ⟨1, by decide⟩ n := by
  simp [evenOdd_bridge_odd]

/-! ### Global assignment & quotas -/

-- Assign picks remainder axis
example : (roundRobin 3 (by decide)).assign 5 = ⟨2, by decide⟩ := by
  simp [roundRobin_assign]

-- Closed-form quota: quota(i, 8) for i = 1 when k = 3
example : quota (roundRobin 3 (by decide)) ⟨1, by decide⟩ 8 = 3 := by
  -- 8 / 3 = 2 and 1 < 8 % 3 (= 2) → 2 + 1 = 3
  simp [quota_roundRobin_closed]

/-! ### k = 1 and block-start convenience -/

-- k = 1: always axis 0, local index = time
example (n : Nat) :
    scheduleSteps (roundRobin 1 (by decide)) (fun (_ : Fin 1) m => Formula.atom m) n
      = Formula.atom n := by
  exact roundRobin_k1_bridge _ n

-- Block start for general k
example (k n : Nat) (hk : 0 < k) (axes : Fin k → Nat → Formula) :
    scheduleSteps (roundRobin k hk) axes (k * n) = axes ⟨0, hk⟩ n := by
  exact roundRobin_block_start_bridge hk axes n

end Papers.P4Meta