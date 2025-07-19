/-
  Total‑variation norm for vector measures (temporary vendored copy;
  remove when mathlib merges PR #11802).
-/
import Mathlib.MeasureTheory.VectorMeasure
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Data.SetLike.Basic

open MeasureTheory Set

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β]

def VectorMeasure.variationNorm (ν : VectorMeasure α β) (s : Set α) : ℝ≥0∞ :=
  ⨆ (p : Finset (Set α))
     (hp : ∀ t ∈ p, MeasurableSet t)
     (hdisj : Pairwise (Disjoint on (p : Set (Set α))))
     (hunion : (⋃ t, t ∈ p → t) = s),
     ∑ t in p, ENNReal.ofReal ‖ν t‖

end MeasureTheory
EOF < /dev/null