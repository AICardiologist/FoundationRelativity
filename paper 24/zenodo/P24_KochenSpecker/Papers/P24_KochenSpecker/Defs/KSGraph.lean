/-
  Paper 24: LLPO Equivalence via Kochen-Specker Contextuality
  Defs/KSGraph.lean — KS graph structure and coloring definitions

  A Kochen-Specker graph abstracts the combinatorial structure of a set
  of measurement contexts. Vertices represent measurements (quantum
  observables), and contexts represent maximal sets of compatible
  measurements (orthogonal bases).

  The KS constraint: in each context (orthogonal basis), exactly one
  measurement yields value 1 (the eigenvalue constraint).
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace Papers.P24

-- ========================================================================
-- KS Graph
-- ========================================================================

/-- A Kochen-Specker graph: vertices (measurements) and contexts
    (maximal sets of compatible measurements / orthogonal bases).
    contextSize is the number of measurements per context
    (= dimension of the Hilbert space). -/
structure KSGraph where
  numVertices : ℕ
  numContexts : ℕ
  contextSize : ℕ
  contexts : Fin numContexts → Finset (Fin numVertices)
  context_card : ∀ c, (contexts c).card = contextSize

-- ========================================================================
-- KS Coloring
-- ========================================================================

/-- A noncontextual value assignment: each vertex (measurement) gets
    true (value 1) or false (value 0).
    Using abbrev so that Fintype/DecidableEq instances are inherited. -/
abbrev KSColoring (G : KSGraph) := Fin G.numVertices → Bool

/-- A coloring satisfies the KS constraint for a context if exactly
    one vertex in the context is colored true.
    This encodes: exactly one measurement in each basis yields value 1. -/
def satisfiesContext (G : KSGraph) (f : KSColoring G) (c : Fin G.numContexts) : Prop :=
  ((G.contexts c).filter (fun v => f v = true)).card = 1

/-- A coloring is KS-valid if it satisfies every context. -/
def isKSValid (G : KSGraph) (f : KSColoring G) : Prop :=
  ∀ c : Fin G.numContexts, satisfiesContext G f c

-- ========================================================================
-- KS-Uncolorability
-- ========================================================================

/-- A KS graph is uncolorable if no valid coloring exists.
    This is the combinatorial content of the Kochen-Specker theorem. -/
def isKSUncolorable (G : KSGraph) : Prop :=
  ∀ f : KSColoring G, ¬ isKSValid G f

-- ========================================================================
-- Decidability instances (needed for native_decide)
-- ========================================================================

instance (G : KSGraph) (f : KSColoring G) (c : Fin G.numContexts) :
    Decidable (satisfiesContext G f c) :=
  inferInstanceAs (Decidable (_ = _))

instance (G : KSGraph) (f : KSColoring G) :
    Decidable (isKSValid G f) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (G : KSGraph) [Fintype (KSColoring G)] :
    Decidable (isKSUncolorable G) :=
  inferInstanceAs (Decidable (∀ _, _))

-- The KS Sign Decision (physical formulation of LLPO) is defined in
-- EncodedAsymmetry.lean after the asymmetry construction.

end Papers.P24
