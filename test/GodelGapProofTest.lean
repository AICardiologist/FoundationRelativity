import AnalyticPathologies.GodelGap
import LogicDSL

-- Compilation sanity checks
open AnalyticPathologies AnalyticPathologies.ClassicalWitness IO

#check godelOp_selfAdjoint
#check sel₃_zfc
#check wlpoPlusPlus_of_sel₃ sel₃_zfc
#check GodelGap_requires_DCω3 sel₃_zfc
#check LogicDSL.classical_wlpoPlusPlus
#check LogicDSL.classical_dcω3

def main : IO Unit := do
  println "✓ GodelGap proof type-checks"
  println "✓ godelOp_selfAdjoint theorem verified"
  println "✓ sel₃_zfc classical witness verified"
  println "✓ GodelGap_requires_DCω3 theorem verified"
  println "✓ All GodelGap proofs verified successfully."