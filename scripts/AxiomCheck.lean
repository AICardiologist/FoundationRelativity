import Papers.P2_BidualGap.Constructive.Ishihara

-- Ask Lean which axioms the following declarations depend on:
#print axioms Papers.P2.Constructive.WLPO_of_gap
#print axioms Papers.P2.Constructive.exists_on_unitBall_gt_half_opNorm
#print axioms Papers.P2.Constructive.hasOpNorm_CLF

-- Double-check the culprit
#print axioms Papers.P2.Constructive.WLPO_of_kernel
#print axioms Papers.P2.Constructive.hasOpNorm_to_hasOperatorNorm
#print axioms Papers.P2.Constructive.IshiharaKernel

-- Silence --run noise
def main : IO Unit := pure ()