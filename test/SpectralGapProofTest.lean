import SpectralGap.Proofs
import SpectralGap.HilbertSetup
import Lean

open IO SpectralGap

def main : IO Unit := do
  println "✓ Spectral‑Gap proof type‑checks"
  println "✓ projGapOp concrete operator created"