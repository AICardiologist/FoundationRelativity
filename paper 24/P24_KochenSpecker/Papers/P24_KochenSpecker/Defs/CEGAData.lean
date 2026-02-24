/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  Defs/CEGAData.lean — CEGA 18-vector KS set (concrete instance)

  The Cabello-Estebaranz-García-Alcaine (CEGA) set:
  18 vectors in ℝ⁴, 9 orthogonal quadruples (contexts).
  Each vector appears in exactly 2 contexts.

  This is the smallest known state-independent Kochen-Specker set.
  The vectors use {0, ±1}⁴ coordinates (unnormalized).

  The KS constraint for ℝ⁴: exactly one vector per quadruple gets
  value 1 (since each context is a 4-element orthonormal basis).

  Uncolorability is verified by native_decide (2^18 = 262,144 search space).

  Source: Cabello, Estebaranz, García-Alcaine,
  "Bell-Kochen-Specker theorem: A proof with 18 vectors,"
  Phys. Lett. A 212, 183–187 (1996).
-/
import Papers.P24_KochenSpecker.Defs.KSGraph
import Mathlib.Tactic.FinCases

namespace Papers.P24

/-- The 9 contexts of the CEGA 18-vector KS set.
    Each context is a set of 4 mutually orthogonal vectors in ℝ⁴.

    Vectors (re-indexed 0-17):
      v0=(1,0,0,0)   v1=(0,1,0,0)   v2=(0,0,1,0)
      v3=(1,1,0,0)   v4=(1,0,1,0)   v5=(1,0,0,1)
      v6=(1,0,0,-1)  v7=(0,1,1,0)   v8=(0,1,0,1)
      v9=(0,1,0,-1)  v10=(0,0,1,1)  v11=(0,0,1,-1)
      v12=(1,1,-1,1) v13=(1,1,-1,-1) v14=(1,-1,1,1)
      v15=(1,-1,1,-1) v16=(1,-1,-1,1) v17=(1,-1,-1,-1)

    Each vector appears in exactly 2 of the 9 contexts. -/
def cegaContexts : Fin 9 → Finset (Fin 18) := fun c =>
  match c with
  | ⟨0, _⟩ => {0, 1, 10, 11}
  | ⟨1, _⟩ => {0, 2, 8, 9}
  | ⟨2, _⟩ => {1, 2, 5, 6}
  | ⟨3, _⟩ => {3, 10, 15, 16}
  | ⟨4, _⟩ => {3, 11, 14, 17}
  | ⟨5, _⟩ => {4, 8, 13, 16}
  | ⟨6, _⟩ => {4, 9, 12, 17}
  | ⟨7, _⟩ => {5, 7, 13, 15}
  | ⟨8, _⟩ => {6, 7, 12, 14}

/-- The CEGA Kochen-Specker graph: 18 vertices, 9 contexts, context size 4. -/
def cegaGraph : KSGraph where
  numVertices := 18
  numContexts := 9
  contextSize := 4
  contexts := cegaContexts
  context_card := by
    intro c; fin_cases c <;> native_decide

end Papers.P24
