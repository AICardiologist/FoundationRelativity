/-
  Paper 23: The Fan Theorem and the Constructive Cost of Optimization
  Defs/Rescaling.lean — Affine rescaling between [0,1] and [a,b]

  The affine map t ↦ a + t·(b − a) sends [0,1] to [a,b].
  This is the key infrastructure for proving EVT on [0,1] ↔ EVT on [a,b].
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Papers.P23

-- ========================================================================
-- Rescaling definition
-- ========================================================================

/-- Affine map sending [0,1] to [a,b]: t ↦ a + t·(b − a). -/
def rescale (a b : ℝ) (t : ℝ) : ℝ := a + t * (b - a)

/-- rescale maps 0 to a. -/
@[simp] theorem rescale_zero (a b : ℝ) : rescale a b 0 = a := by
  unfold rescale; ring

/-- rescale maps 1 to b. -/
@[simp] theorem rescale_one (a b : ℝ) : rescale a b 1 = b := by
  unfold rescale; ring

/-- rescale maps [0,1] into [a,b] when a ≤ b. -/
theorem rescale_maps_Icc (a b : ℝ) (hab : a ≤ b)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    rescale a b t ∈ Set.Icc a b := by
  constructor
  · unfold rescale
    nlinarith [ht.1, ht.2]
  · unfold rescale
    nlinarith [ht.1, ht.2]

/-- rescale is continuous. -/
theorem rescale_continuous (a b : ℝ) : Continuous (rescale a b) := by
  unfold rescale
  exact continuous_const.add (continuous_id.mul continuous_const)

/-- Set.MapsTo version for ContinuousOn.comp. -/
theorem rescale_mapsTo (a b : ℝ) (hab : a ≤ b) :
    Set.MapsTo (rescale a b) (Set.Icc 0 1) (Set.Icc a b) :=
  fun _t ht => rescale_maps_Icc a b hab _t ht

-- ========================================================================
-- Inverse rescaling
-- ========================================================================

noncomputable section

/-- Inverse rescaling: x ↦ (x − a) / (b − a), sending [a,b] to [0,1]. -/
def unscale (a b : ℝ) (x : ℝ) : ℝ := (x - a) / (b - a)

/-- unscale maps [a,b] into [0,1] when a < b. -/
theorem unscale_maps_Icc (a b : ℝ) (hab : a < b)
    (x : ℝ) (hx : x ∈ Set.Icc a b) :
    unscale a b x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold unscale
  have hba : 0 < b - a := sub_pos.mpr hab
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hba)
  · rw [div_le_one hba]
    linarith [hx.2]

/-- rescale ∘ unscale = id on [a,b]. -/
theorem rescale_unscale (a b : ℝ) (hab : a < b)
    (x : ℝ) (_hx : x ∈ Set.Icc a b) :
    rescale a b (unscale a b x) = x := by
  unfold rescale unscale
  have hba : (b - a) ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp; ring

/-- unscale ∘ rescale = id on [0,1]. -/
theorem unscale_rescale (a b : ℝ) (hab : a < b)
    (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1) :
    unscale a b (rescale a b t) = t := by
  unfold unscale rescale
  have hba : (b - a) ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp; ring

end

end Papers.P23
