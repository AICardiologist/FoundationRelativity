/-
  Papers/P3_2CatFramework/P4_Meta/P3_P4_Bridge_test.lean
  
  Smoke tests for the Paper 3 ↔ P4_Meta bridge.
-/
import Papers.P3_2CatFramework.P4_Meta.P3_P4_Bridge

namespace Papers.P3.P4Bridge.Tests

open Papers.P3.Phase1Simple
open Papers.P3.Phase2
open Papers.P3.Phase3
open Papers.P4Meta
open Papers.P3.P4Bridge

-- Test level formulas
#eval levelFormula 0  -- atom 500
#eval levelFormula 1  -- atom 501  
#eval levelFormula 2  -- atom 502

-- Test level certificates
def level0Cert := levelCert Paper3Theory 0
def level1Cert := levelCert Paper3Theory 1

#check level0Cert.n     -- should be 1
#check level1Cert.n     -- should be 2
#eval level0Cert.n
#eval level1Cert.n

-- Test uniformization formulas
#eval uniformFormula "GapFamily" 0
#eval uniformFormula "GapFamily" 1
#eval uniformFormula "TruthFamily" 1

-- Test obstruction formula
#eval obstructFormula "GapFamily" 0

-- Test gap obstruction certificate
def gapObstr := gapObstructionCert Paper3Theory
#check gapObstr.n  -- should be 0 (base theory)
#eval gapObstr.n

-- Test level hierarchy embedding
example : ∃ n, (ExtendIter Paper3Theory (levelLadder Paper3Theory) n).Provable (levelFormula 0) :=
  level_hierarchy_embedding Paper3Theory 0

example : ∃ n, (ExtendIter Paper3Theory (levelLadder Paper3Theory) n).Provable (levelFormula 1) :=
  level_hierarchy_embedding Paper3Theory 1

-- Test pushing to ω-limit
def level0AtOmega : (Extendω Paper3Theory (levelLadder Paper3Theory)).Provable (levelFormula 0) :=
  certToOmega level0Cert

def level1AtOmega : (Extendω Paper3Theory (levelLadder Paper3Theory)).Provable (levelFormula 1) :=
  certToOmega level1Cert

#check level0AtOmega
#check level1AtOmega

-- Test aggregation structure
def testAggregate : UniformizationAggregate Paper3Theory (levelLadder Paper3Theory) :=
{ certs := []
, maxStage := 0
, summary := "Empty test aggregate"
}

#check testAggregate.maxStage
#eval testAggregate.summary

-- Test combined analysis (gap obstruction + truth uniformization)
def gapPair := gapAnalysisPair Paper3Theory
#check gapPair

-- Both components at ω
def gapAtOmega := gapAnalysisAtOmega Paper3Theory
#check gapAtOmega.1  -- obstruction at ω
#check gapAtOmega.2  -- uniformization at ω

#eval "P3-P4 Bridge smoke tests OK!"

end Papers.P3.P4Bridge.Tests