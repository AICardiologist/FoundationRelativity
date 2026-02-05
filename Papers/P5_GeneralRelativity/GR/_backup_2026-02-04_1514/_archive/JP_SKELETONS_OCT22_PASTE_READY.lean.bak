-- JP's Ready-to-Paste Skeletons for ricci_identity_on_g_rθ_ext Restoration
-- Date: October 22, 2025
-- Status: READY TO USE - Copy/paste when restoring proof
--
-- IMPORTANT: Keep file in clean state (top-level sorry) until ready to restore.
-- When ready: paste these sections into Riemann.lean near line 5790.

/-! ### Step 6: payload conversion micro-lemmas (skeletons)
  Bounded algebra only. Prefer: `simp only`, `simp_rw`, `sumIdx_*` helpers, `ring`.
  No global simp. No bidirectional lemmas.
-/

private lemma payload_r
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  -- r-branch "first conversion": Γ · (∂θ g) → collected ΓΓ·g + ΓΓ·g
  sumIdx (fun ρ =>
    Γtot M r θ ρ a Idx.r * dCoord Idx.θ (fun r θ => g M ρ b r θ) r θ)
  =
  -- TODO: target shape after expanding ∂θ g via compatibility on θ, then collecting
  -- e.g. sumIdx (fun ρ => Γtot … ρ a r * (sumIdx … + sumIdx …))
  -- and then (optionally) rewrite to the commutator payload layout expected by Step 6
  by
  -- HINTS:
  -- * Use a local, *one-shot* expansion for ∂θ g (compatibility in θ).
  --   Prefer a refold lemma you can `simp_rw` once; avoid any lemma that rewrites both ways.
  -- * Then `simp_rw` distributes products/sums; use `sumIdx_add_distrib`, `sumIdx_mul` or `mul_sumIdx`.
  -- * Normalize with `sumIdx_congr; ring`.
  sorry

private lemma payload_r_flat
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  -- r-branch "flatten/normalize": put the previous result into the linear collector form
  -- (pointwise → collected block)
  _
  := by
  -- HINTS:
  -- * Use `sumIdx_collect4` / `sumIdx_collect6` / `sumIdx_collect_comm_block` helpers.
  -- * `simp_rw` your ASCII `let`-bindings to align shapes before applying the collector lemma.
  -- * Finish with `sumIdx_congr; ring`.
  sorry

private lemma payload_r_second
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  -- r-branch "second transformation": mirror for the other Γ·(∂θ g) occurrence
  _
  := by
  -- HINTS:
  -- * Same pattern as `payload_r`, but for the second term.
  -- * Prefer the same sequence of rewrites so shapes line up without AC search.
  sorry

private lemma payload_th
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  -- θ-branch "first conversion": Γ · (∂r g) → collected ΓΓ·g + ΓΓ·g  (mirror of payload_r)
  sumIdx (fun ρ =>
    Γtot M r θ ρ a Idx.θ * dCoord Idx.r (fun r θ => g M ρ b r θ) r θ)
  = _
  := by
  -- HINTS:
  -- * Swap r↔θ everywhere compared to `payload_r`.
  -- * Use the r‑compatibility refold once; then apply the same collector algebra.
  sorry

private lemma payload_th_flat
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  -- θ-branch "flatten/normalize" (mirror of payload_r_flat)
  _
  := by
  -- HINTS: identical algebra as in the r‑branch flatten lemma.
  sorry

private lemma payload_th_second
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  -- θ-branch "second transformation" (mirror of payload_r_second)
  _
  := by
  sorry

/-! ### Phase 2B: Differentiability stubs (drop-in replacements for lines ~8421, ~8423)

Replace the two sorries around your ∂/Σ interchange with this pattern.
Uses only lemmas already in file: differentiableAt_g_all_r/_θ,
differentiableAt_Γtot_all_r/_θ, and dCoord_sumIdx.
-/

-- For the r-branch (∂_r over Σ_k Γ_{k θ a}·g_{k b})
have hF_r :
  ∀ k, DifferentiableAt_r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ ∨ Idx.r ≠ Idx.r := by
  intro k
  -- μ = r, so we must prove differentiability (left branch of the disjunction)
  left
  -- product rule from your master lemmas
  exact
    (DifferentiableAt.mul
      (differentiableAt_Γtot_all_r M r θ h_ext k Idx.θ a)
      (differentiableAt_g_all_r M r θ h_ext k b))

have hF_θ :
  ∀ k, DifferentiableAt_θ (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ ∨ Idx.r ≠ Idx.θ := by
  intro k
  -- we are in the r-branch, so allowing μ ≠ θ is fine to discharge the disjunction:
  right; decide   -- or `simp` since `Idx.r ≠ Idx.θ`

-- Apply dCoord_sumIdx on the r-branch:
have hr_interchange :
  dCoord Idx.r (fun r θ => sumIdx (fun k => Γtot M r θ k Idx.θ a * g M k b r θ)) r θ
  = sumIdx (fun k => dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ) := by
  simpa using (dCoord_sumIdx Idx.r
    (fun k r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ hF_r hF_θ)

-- Similarly for the θ-branch (∂_θ over Σ_k Γ_{k r a}·g_{k b}):
have hG_θ :
  ∀ k, DifferentiableAt_θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ ∨ Idx.θ ≠ Idx.θ := by
  intro k
  left
  exact
    (DifferentiableAt.mul
      (differentiableAt_Γtot_all_θ M r θ k Idx.r a h_θ)
      (differentiableAt_g_all_θ M r θ k b))

have hG_r :
  ∀ k, DifferentiableAt_r (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ ∨ Idx.θ ≠ Idx.r := by
  intro k
  right; decide

have hθ_interchange :
  dCoord Idx.θ (fun r θ => sumIdx (fun k => Γtot M r θ k Idx.r a * g M k b r θ)) r θ
  = sumIdx (fun k => dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ) := by
  simpa using (dCoord_sumIdx Idx.θ
    (fun k r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ hG_r hG_θ)

/-! ### Step 6 wrapper: suffices pattern (replaces top-level sorry at line 5790)

Paste this to replace the current `sorry` in ricci_identity_on_g_rθ_ext.
-/

-- Inside `ricci_identity_on_g_rθ_ext … := by`
simp only [nabla, nabla_g]
rw [ dCoord_r_push_through_nabla_g_θ_ext M r θ h_ext a b
   , dCoord_θ_push_through_nabla_g_r_ext M r θ h_ext a b ]
-- … other deterministic rewrites …

-- Containment without `refine`:
suffices H :
  nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
  - nabla (fun M r θ a b => nabla_g M r θ Idx.r a b) M r θ Idx.θ a b
  = - Riemann M r θ b a Idx.r Idx.θ - Riemann M r θ a b Idx.r Idx.θ by
  exact H

-- Step 6.A: mixed partials (bounded)
have hmixed :
  dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ
= dCoord Idx.θ (fun r θ => dCoord Idx.r (fun r θ => g M a b r θ) r θ) r θ := by
  simpa using dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ
have hXY0 : _ - _ = 0 := sub_eq_zero.mpr hmixed

-- Step 6.B: define all 12 lets (ASCII) BEFORE collector
let Gb  : Idx → ℝ := fun ρ => g M ρ b r θ
let Ar  : Idx → ℝ := fun ρ => - Γtot M r θ ρ a Idx.r * g M ρ b r θ
-- … Br, Cr, Dr, Pr, Qr, Ath, Bth, Cth, Dth, Pth, Qth …

-- Step 6.C: two-branch collector
have hCollect :=
  sumIdx_collect_two_branches Gb Ar Br Cr Dr Pr Qr Ath Bth Cth Dth Pth Qth
simp_rw [Gb, Ar, Br, Cr, Dr, Pr, Qr, Ath, Bth, Cth, Dth, Pth, Qth] at hCollect
-- Bring the collector into the goal:
rw [hCollect]

-- Step 6.D–E: payload conversions (use the 6 micro-lemmas here)
--   exact payload_r  …, payload_r_flat …, payload_r_second …,
--         payload_th …, payload_th_flat …, payload_th_second …
sorry

/-! ### Filling tips (when restoring)

* Use your compat_refold_* (one direction only) or the axiom‑free
  dCoord_g_via_compat_ext once per occurrence via simp_rw—don't
  put those lemmas in global simp.

* Immediately follow with sumIdx_add_distrib, mul_sumIdx/sumIdx_mul,
  sumIdx_swap, then sumIdx_congr; ring.

* If you need metric symmetry, use your explicit (non‑simp) metric
  symmetry lemma (e.g. g_symm‑style) by simp_rw once at the right place.

* Guardrail: Verify with single-file build after each integration:
  ```
  cd /Users/quantmann/FoundationRelativity
  lake build Papers.P5_GeneralRelativity.GR.Riemann
  ```
-/
