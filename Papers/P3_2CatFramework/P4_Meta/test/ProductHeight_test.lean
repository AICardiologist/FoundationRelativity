/-
  Test file for Product Height theorems
  Verifies the parity lemmas and lift proofs work correctly
-/
import Papers.P3_2CatFramework.P4_Meta.PartIII_ProductHeight

namespace Papers.P4Meta

open Papers.P4Meta

-- Test the parity lemmas really fire
example {A B : Nat → Formula} (n : Nat) : fuseSteps A B (2*n) = A n := by
  simp [fuseSteps_even]

example {A B : Nat → Formula} (n : Nat) : fuseSteps A B (2*n+1) = B n := by
  simp [fuseSteps_odd]

-- Test the simp lemmas work
example (n : Nat) : 2 * (n + 1) = 2 * n + 2 := by simp
example (n : Nat) : (2 * n + 1) + 1 = 2 * n + 2 := by simp

-- Verify the lift theorems are available and type-check
section LiftTests
  variable {T : Theory} {A B : Nat → Formula} {φ ψ : Formula}
  variable (cφ : HeightCertificate T A φ)
  variable (cψ : HeightCertificate T B ψ)
  
  -- Basic lifts to exact stage 2n
  #check liftA_to_fuse_even cφ
  #check liftB_to_fuse_even cψ
  
  -- Generalized lifts to any stage m ≥ 2n
  #check liftA_to_fuse_le cφ
  #check liftB_to_fuse_le cψ
  
  -- The factored embeddings
  #check embedA_even (T:=T) (A:=A) (B:=B)
  #check embedB_even (T:=T) (A:=A) (B:=B)
  
  -- The main upper bound theorem
  #check product_height_le_2max cφ cψ
  
  -- With independence assumption
  variable [AxisIndependent T A B]
  #check product_height_eq_2max cφ cψ
  
  -- New odd embeddings and lifts
  #check embedA_odd (T:=T) (A:=A) (B:=B)
  #check embedB_odd (T:=T) (A:=A) (B:=B)
  #check liftA_to_fuse_odd cφ
  #check liftB_to_fuse_odd cψ
  
  -- Odd stage ≤-variants
  #check liftA_to_fuse_odd_le cφ
  #check liftB_to_fuse_odd_le cψ
  
  -- Raise pair utility
  variable (c : HeightCertificatePair T (fuseSteps A B) ⟨φ, ψ⟩)
  #check raise_pair c
  #check pair_on_fuse_upper_n cφ cψ
  
  -- Convenience constructors
  #check pair_on_fuse_ge_max cφ cψ
  #check pair_on_fuse_ge_max_n cφ cψ
  #check pair_on_fuse_at_or_above cφ cψ
  #check pair_on_fuse_at_or_above_n cφ cψ
  
  -- Exactness packaging
  #check product_height_exact_2max cφ cψ
  #check no_pair_before_2max cφ cψ
end LiftTests

end Papers.P4Meta