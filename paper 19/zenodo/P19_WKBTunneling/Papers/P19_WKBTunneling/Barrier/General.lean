/-
Papers/P19_WKBTunneling/Barrier/General.lean
Helper lemmas connecting general barriers to the IVT.

Key result: ExactIVT on [0,1] can be rescaled to any interval [a,b],
and barrier sign conditions give IVT hypotheses.
-/
import Papers.P19_WKBTunneling.Barrier.Definitions

noncomputable section
namespace Papers.P19

-- ========================================================================
-- Rescaled IVT
-- ========================================================================

/-- ExactIVT on [0,1] implies IVT on any interval [a,b] with a < b.
    Proof: given f continuous on [a,b] with f(a) < 0 < f(b),
    define g(t) = f(a + t(b-a)) for t ∈ [0,1]. Then g(0) < 0, g(1) > 0,
    and g is continuous. ExactIVT gives t₀ with g(t₀) = 0, so f(a + t₀(b-a)) = 0. -/
theorem exact_ivt_on_interval (hIVT : ExactIVT)
    (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : Continuous f)
    (hfa : f a < 0) (hfb : f b > 0) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 := by
  -- Define g(t) = f(a + t*(b - a)) on [0,1]
  set g : ℝ → ℝ := fun t => f (a + t * (b - a)) with hg_def
  have hg_cont : Continuous g := hf.comp (continuous_const.add (continuous_id.mul continuous_const))
  have hg0 : g 0 < 0 := by simp [hg_def]  ; exact hfa
  have hg1 : g 1 > 0 := by simp [hg_def]; ring_nf; linarith
  -- Apply ExactIVT to g
  obtain ⟨t₀, ht₀_ge, ht₀_le, ht₀_root⟩ := hIVT g hg_cont hg0 hg1
  -- x = a + t₀*(b - a) is the root
  refine ⟨a + t₀ * (b - a), ?_, ?_, ht₀_root⟩
  · linarith [mul_nonneg ht₀_ge (sub_nonneg.mpr (le_of_lt hab))]
  · have : t₀ * (b - a) ≤ 1 * (b - a) :=
      mul_le_mul_of_nonneg_right ht₀_le (sub_nonneg.mpr (le_of_lt hab))
    linarith

/-- Reversed-sign version: IVT for f(a) > 0, f(b) < 0.
    Apply the standard IVT to -f. -/
theorem exact_ivt_on_interval_neg (hIVT : ExactIVT)
    (a b : ℝ) (hab : a < b) (f : ℝ → ℝ) (hf : Continuous f)
    (hfa : f a > 0) (hfb : f b < 0) :
    ∃ x, a ≤ x ∧ x ≤ b ∧ f x = 0 := by
  obtain ⟨x, hxa, hxb, hfx⟩ := exact_ivt_on_interval hIVT a b hab
    (fun x => -f x) (hf.neg) (by linarith) (by linarith)
  exact ⟨x, hxa, hxb, by linarith⟩

end Papers.P19
end
