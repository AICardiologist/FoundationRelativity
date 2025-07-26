import AnalyticPathologies.GodelGap

-- Compilation sanity checks
open SpectralGap ClassicalWitness

#check godelOp_selfAdjoint
#check sel₃_zfc
#check wlpoPlusPlus_of_sel₃ sel₃_zfc
#check GodelGap_requires_DCω3 ClassicalWitness.sel₃_zfc
#check LogicDSL.classical_wlpoPlusPlus
#check LogicDSL.classical_dcω3