import Papers.P2_BidualGap.HB.QuotSeparation
import Papers.P2_BidualGap.HB.SimpleFacts  

open Papers.P2.HB.QuotSeparation

-- Smoke test: verify all key symbols resolve and have correct types from QuotSeparation
#check constOne
#check S₀
#check S  
#check Scl
#check q
#check F

-- Test key lemmas
#check isClosed_Scl
#check constOne_not_mem_Scl
#check F_constOne
#check F_vanishes_on_Scl

-- Test from SimpleFacts
#check constOne_not_in_c0_image
#check c0_const_separation_bound