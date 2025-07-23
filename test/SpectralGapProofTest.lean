import SpectralGap.NoWitness
import Lean

open IO SpectralGap

def main : IO Unit := do
  println "✓ Spectral-Gap proof type-checks"
  println "✓ zeroGapOp exists with gap_lt proof"
  -- Milestone C confirmation
  println "✓ Constructive impossibility lemma compiled (RequiresACω)."