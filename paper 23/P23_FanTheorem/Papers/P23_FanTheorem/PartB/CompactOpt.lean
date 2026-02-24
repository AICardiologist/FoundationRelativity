/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  PartB/CompactOpt.lean — EVT on [0,1] ↔ CompactOptimization on [a,b]

  Forward: EVT_min → CompactOptimization (rescale [0,1] to [a,b])
  Backward: CompactOptimization → EVT_min (specialize to a=0, b=1)
-/
import Papers.P23_FanTheorem.Defs.EVT
import Papers.P23_FanTheorem.Defs.Rescaling
import Papers.P23_FanTheorem.PartB.EVTEquiv
import Mathlib.Topology.ContinuousOn

namespace Papers.P23

-- ========================================================================
-- EVT_min → CompactOptimization (rescaling proof)
-- ========================================================================

/-- EVT on [0,1] implies compact optimization on arbitrary [a,b].
    This is the rescaling argument: compose f with the affine map
    t ↦ a + t·(b-a) to reduce [a,b] to [0,1]. -/
theorem compact_opt_of_evt_min (h : EVT_min) : CompactOptimization := by
  intro a b hab f hf
  -- Define g(t) = f(rescale a b t) on [0,1]
  let g : ℝ → ℝ := fun t => f (rescale a b t)
  -- g is continuous on [0,1]
  have hg_cont : ContinuousOn g (Set.Icc 0 1) := by
    apply ContinuousOn.comp hf (rescale_continuous a b).continuousOn
    exact rescale_mapsTo a b (le_of_lt hab)
  -- Apply EVT_min to g on [0,1]
  obtain ⟨t_star, ht_mem, ht_min⟩ := h g hg_cont
  -- x_star = rescale a b t_star ∈ [a,b] is the minimizer
  refine ⟨rescale a b t_star, rescale_maps_Icc a b (le_of_lt hab) t_star ht_mem, ?_⟩
  -- For any y ∈ [a,b], f(x_star) ≤ f(y)
  intro y hy
  have hs_mem : unscale a b y ∈ Set.Icc (0 : ℝ) 1 :=
    unscale_maps_Icc a b hab y hy
  have h1 : f (rescale a b t_star) ≤ f (rescale a b (unscale a b y)) :=
    ht_min (unscale a b y) hs_mem
  rw [rescale_unscale a b hab y hy] at h1
  exact h1

-- ========================================================================
-- CompactOptimization → EVT_min (specialize to [0,1])
-- ========================================================================

/-- Compact optimization on [a,b] implies EVT on [0,1].
    Just specialize to a=0, b=1. -/
theorem evt_min_of_compact_opt (h : CompactOptimization) : EVT_min := by
  intro f hf
  exact h 0 1 (by norm_num) f hf

-- ========================================================================
-- EVT_min ↔ CompactOptimization
-- ========================================================================

/-- The equivalence. -/
theorem evt_min_iff_compact_opt : EVT_min ↔ CompactOptimization :=
  ⟨compact_opt_of_evt_min, evt_min_of_compact_opt⟩

end Papers.P23
