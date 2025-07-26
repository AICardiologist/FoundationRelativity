import AnalyticPathologies.HilbertSetup

/-! # Classical witness for the zero operator (Milestone C) -/

open SpectralGap

namespace AnalyticPathologies

/-- A concrete unit vector: `e 0` (Kronecker δ at index 0). -/
noncomputable def zeroWitness : L2Space := e 0

@[simp] lemma zero_op_apply (v : L2Space) : (0 : BoundedOp) v = 0 := by
  simp

@[simp] lemma zeroWitness_eigen : (0 : BoundedOp) zeroWitness = 0 := by
  simp [zeroWitness]

/-- **witness_zfc** – the eigenspace at 0 for the zero operator is non‑empty. -/
def witness_zfc : Nonempty (Σ' v : L2Space, (0 : BoundedOp) v = 0) :=
  ⟨⟨zeroWitness, zeroWitness_eigen⟩⟩

end AnalyticPathologies