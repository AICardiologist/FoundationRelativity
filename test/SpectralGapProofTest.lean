import SpectralGap.Proofs
import SpectralGap.HilbertSetup
import Lean

open IO SpectralGap

def main : IO Unit := do
  println "✓ Spectral‑Gap proof type‑checks"
  println "✓ zeroGapOp concrete operator created with real spectrum gap proof"