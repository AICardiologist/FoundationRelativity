import SpectralGap.Proofs
import SpectralGap.HilbertSetup
import Lean

open IO
open SpectralGap

def main : IO Unit := do
  println "✓ Spectral‑Gap proof type‑checks"
  println s!"✓ SpectralGapOperator example has gap: {projGapOp.gap_lt}"