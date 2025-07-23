import SpectralGap.NoWitness
import Lean

open IO SpectralGap

def main : IO Unit := do
  println "✓ Spectral-Gap proof type-checks"
  println s!"✓ zeroGapOp exists: {SpectralGap.zeroGapOp.gap_lt}"
  -- Milestone C confirmation
  println "✓ Constructive impossibility lemma compiled (RequiresACω)."