import Papers.P2_BidualGap.WLPO_Equiv_Gap

#eval (IO.println "=== Paper 2 Axiom Status ===")
#print axioms Papers.P2.gap_implies_wlpo
#print axioms Papers.P2.wlpo_implies_gap
#print axioms Papers.P2.gap_equiv_WLPO
#eval (IO.println "=== End Axioms ===")

def main : IO Unit := do
  IO.println "Paper 2 axiom check complete - see #print axioms output above"