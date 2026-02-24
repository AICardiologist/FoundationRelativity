/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  PartB/EVTEquiv.lean — EVT_max ↔ EVT_min equivalence

  Proof: apply EVT to -f. If -f attains its max at x,
  then f attains its min at x (and vice versa).
-/
import Papers.P23_FanTheorem.Defs.EVT
import Mathlib.Topology.ContinuousOn

namespace Papers.P23

-- ========================================================================
-- EVT_max → EVT_min (apply to -f)
-- ========================================================================

/-- EVT_max implies EVT_min: apply the max theorem to -f. -/
theorem evt_min_of_evt_max (h : EVT_max) : EVT_min := by
  intro f hf
  -- Apply EVT_max to -f
  obtain ⟨x, hx_mem, hx_max⟩ := h (fun t => -f t) (hf.neg)
  -- If -f attains its max at x, then f attains its min at x
  exact ⟨x, hx_mem, fun y hy => by linarith [hx_max y hy]⟩

-- ========================================================================
-- EVT_min → EVT_max (apply to -f in reverse)
-- ========================================================================

/-- EVT_min implies EVT_max: apply the min theorem to -f. -/
theorem evt_max_of_evt_min (h : EVT_min) : EVT_max := by
  intro f hf
  obtain ⟨x, hx_mem, hx_min⟩ := h (fun t => -f t) (hf.neg)
  exact ⟨x, hx_mem, fun y hy => by linarith [hx_min y hy]⟩

-- ========================================================================
-- The iff
-- ========================================================================

/-- EVT_max and EVT_min are equivalent. -/
theorem evt_max_iff_evt_min : EVT_max ↔ EVT_min :=
  ⟨evt_min_of_evt_max, evt_max_of_evt_min⟩

end Papers.P23
