-- Option2_All.lean - Test all Option 2 imports
import Papers.P2_BidualGap.HB.QuotSeparation
import Papers.P2_BidualGap.HB.SimpleFacts
import Papers.P2_BidualGap.HB.WLPO_to_Gap_HB

-- Check that key definitions are available
open Papers.P2.HB.QuotSeparation
#check q
#check F
#check F_constOne
#check F_vanishes_on_Scl