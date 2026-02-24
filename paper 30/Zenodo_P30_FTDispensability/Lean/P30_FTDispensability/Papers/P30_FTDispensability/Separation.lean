/-
  Paper 30: The Physical Dispensability of the Fan Theorem
  Separation.lean — ExactEVT ↔ FanTheorem (separation result)

  Main theorems:
    - exactEVT_of_ft: FanTheorem → ExactEVT
    - ft_of_exactEVT: ExactEVT → FanTheorem
    - exactEVT_iff_ft: ExactEVT ↔ FanTheorem

  The forward direction uses rescaling from [0,1] to [a,b].
  The backward direction is immediate: ExactEVT on [0,1] gives EVT_max.
-/
import Papers.P30_FTDispensability.Defs

noncomputable section
namespace Papers.P30

open Set

-- ========================================================================
-- Rescaling lemmas
-- ========================================================================

@[simp] theorem rescale_zero (a b : ℝ) : rescale a b 0 = a := by
  unfold rescale; ring

@[simp] theorem rescale_one (a b : ℝ) : rescale a b 1 = b := by
  unfold rescale; ring

theorem rescale_maps_Icc (a b : ℝ) (hab : a ≤ b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    rescale a b t ∈ Icc a b := by
  unfold rescale
  constructor
  · nlinarith [ht.1, ht.2]
  · nlinarith [ht.1, ht.2]

theorem rescale_continuous (a b : ℝ) : Continuous (rescale a b) := by
  unfold rescale
  fun_prop

theorem rescale_mapsTo (a b : ℝ) (hab : a ≤ b) :
    MapsTo (rescale a b) (Icc 0 1) (Icc a b) :=
  fun _t ht => rescale_maps_Icc a b hab _t ht

theorem unscale_maps_Icc (a b : ℝ) (hab : a < b)
    (x : ℝ) (hx : x ∈ Icc a b) :
    unscale a b x ∈ Icc (0 : ℝ) 1 := by
  unfold unscale
  have hba : 0 < b - a := sub_pos.mpr hab
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hba)
  · rw [div_le_one hba]; linarith [hx.2]

theorem rescale_unscale (a b : ℝ) (hab : a < b)
    (x : ℝ) (_hx : x ∈ Icc a b) :
    rescale a b (unscale a b x) = x := by
  unfold rescale unscale
  have hba : (b - a) ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp; ring

theorem unscale_rescale (a b : ℝ) (hab : a < b)
    (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1) :
    unscale a b (rescale a b t) = t := by
  unfold unscale rescale
  have hba : (b - a) ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp; ring

theorem unscale_mapsTo (a b : ℝ) (hab : a < b) :
    MapsTo (unscale a b) (Icc a b) (Icc 0 1) :=
  fun _x hx => unscale_maps_Icc a b hab _x hx

theorem unscale_continuous (a b : ℝ) (hab : a < b) : Continuous (unscale a b) := by
  unfold unscale
  have : (b - a) ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  fun_prop

-- ========================================================================
-- FanTheorem → ExactEVT
-- ========================================================================

/-- Fan Theorem (= EVT_max on [0,1]) implies ExactEVT on any [a,b].
    Uses rescaling: compose f with rescale to get g on [0,1],
    apply FT to g, then unscale the witness. -/
theorem exactEVT_of_ft (hft : FanTheorem) : ExactEVT := by
  intro f a b hab hf
  -- Define g = f ∘ rescale on [0,1]
  set g := f ∘ rescale a b with hg_def
  -- g is continuous on [0,1]
  have hg_cts : ContinuousOn g (Icc 0 1) := by
    apply hf.comp (rescale_continuous a b).continuousOn
    exact rescale_mapsTo a b (le_of_lt hab)
  -- Apply FT: g attains max on [0,1]
  obtain ⟨t, ht_mem, ht_max⟩ := hft g hg_cts
  -- x* = rescale a b t is in [a,b] and maximizes f
  set x := rescale a b t with hx_def
  have hx_mem : x ∈ Icc a b := rescale_maps_Icc a b (le_of_lt hab) t ht_mem
  refine ⟨x, hx_mem, ?_⟩
  intro y hy
  -- f(y) = g(unscale a b y) ≤ g(t) = f(x)
  have huy : unscale a b y ∈ Icc (0 : ℝ) 1 := unscale_maps_Icc a b hab y hy
  have : f y = g (unscale a b y) := by
    simp [hg_def, rescale_unscale a b hab y hy]
  rw [this]
  exact ht_max (unscale a b y) huy

-- ========================================================================
-- ExactEVT → FanTheorem
-- ========================================================================

/-- ExactEVT implies FanTheorem (= EVT_max on [0,1]).
    Immediate: ExactEVT applied to [0,1] gives EVT_max. -/
theorem ft_of_exactEVT (hexact : ExactEVT) : FanTheorem := by
  intro f hf
  exact hexact f 0 1 one_pos hf

-- ========================================================================
-- The equivalence
-- ========================================================================

/-- ExactEVT is equivalent to the Fan Theorem. -/
theorem exactEVT_iff_ft : ExactEVT ↔ FanTheorem :=
  ⟨ft_of_exactEVT, exactEVT_of_ft⟩

end Papers.P30
end
