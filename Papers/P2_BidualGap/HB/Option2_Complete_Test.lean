import Papers.P2_BidualGap.HB.QuotSeparation
import Papers.P2_BidualGap.HB.SimpleFacts

-- Test namespace access
namespace TestNamespace

open Papers.P2.HB.QuotSeparation

-- Test that all key symbols are accessible
#check constOne
#check S₀  
#check S
#check Scl
#check q 
#check F

-- Test the key properties
#check constOne_not_mem_Scl
#check q_constOne_ne
#check F_constOne  
#check F_vanishes_on_Scl

-- Test mathematical structure is sound
example : constOne ≠ (0 : E) := by
  -- Constant 1 is not zero
  sorry

example : F constOne ≠ 0 := by
  rw [F_constOne]
  norm_num

end TestNamespace