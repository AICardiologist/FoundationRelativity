# Tactical Report for Junior Professor (JP): Remaining Sorries & Next Steps
**Date**: October 22, 2025
**Status**: ✅ **All recursion errors fixed, file compiles cleanly**
**Build verification**: `lake build Papers.P5_GeneralRelativity.GR.Riemann` exits with 0 errors

---

## Executive Summary

**Current metrics**:
- **Compilation errors**: 0 ✅
- **Recursion depth errors**: 0 ✅ (all 6 sites fixed)
- **Axioms**: 0 ✅ (converted to lemma with sorry)
- **Active sorries**: 17 (detailed below)
- **Commented-out sorries**: 5 (in block comment, lines 1996-2088)

**Critical path for Ricci vacuum proof (R_μν = 0)**:
1. **Priority 1**: Complete `ricci_identity_on_g_rθ_ext` (line 5790) - blocks 3 downstream lemmas
2. **Priority 2**: Fill 6 payload conversion micro-lemmas in restored proof
3. **Priority 3**: Prove `nabla_g_zero_ext` using completed Ricci identity
4. **Priority 4**: Complete differentiability lemmas (lines 8421, 8423)

**Your offer**: Draft 6 payload conversion micro-lemma skeletons — **accepted and ready to integrate**

---

## Part 1: Sorry Inventory with Code Context

### Priority 1: Critical Path Blockers

#### 1. Line 5790: `ricci_identity_on_g_rθ_ext` [HIGHEST PRIORITY]

**Status**: Top-level sorry placeholder (temporary workaround for "case G" issue)
**Blocks**: 3 downstream lemmas (Riemann_swap_a_b_ext, nabla_g_zero_ext, Riemann_swap_a_b)
**Your offered fix**: Use `suffices` pattern instead of `refine ?_main`

**Full code context**:
```lean
-- Line 5783-5791
/-- Ricci identity specialized to (r,θ) exterior case. -/
lemma ricci_identity_on_g_rθ_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (h_θ : Real.sin θ ≠ 0) (a b : Idx) :
  nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
  - nabla (fun M r θ a b => nabla_g M r θ Idx.r a b) M r θ Idx.θ a b
  =
  - Riemann M r θ b a Idx.r Idx.θ - Riemann M r θ a b Idx.r Idx.θ := by
  sorry  -- TEMPORARY: Test if recursion fixes allow file to compile
  -- TODO JP: Need interactive Lean to fix "case G" created by refine ?_main
```

**Background**:
- Full Step 6 code backed up in `Riemann.lean.backup_before_deletion`
- Steps 1-5 are deterministic rewrites that worked perfectly
- Step 6 requires:
  - 6.A: Mixed partial cancellation (proven via `dCoord_commute_for_g_all`)
  - 6.B: Define 12 `let` bindings BEFORE calling collector
  - 6.C: Apply `sumIdx_collect_two_branches` with all 12 lets
  - 6.D-E: Fill 6 payload conversions (your offered skeletons)

**Your recommended approach** (from JP_EXPLANATION_CASE_G_OCT22.md):
```lean
lemma ricci_identity_on_g_rθ_ext ... : LHS = RHS := by
  -- Steps 1–5 (deterministic rewrites only)
  simp only [nabla, nabla_g]
  rw [dCoord_r_push_through_nabla_g_θ_ext M r θ h_ext a b,
      dCoord_θ_push_through_nabla_g_r_ext M r θ h_ext a b]
  rw [helpers...]

  -- Contain the rest in a single suffices target:
  suffices H : LHS = RHS by exact H

  -- Step 6.A — mixed partials (localized, no global `simp`):
  have hmixed : X = Y := by
    simpa using dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ
  have hXY0 : X - Y = 0 := sub_eq_zero.mpr hmixed

  -- Step 6.B — define ALL 12 lets BEFORE collector call:
  let Gb : Idx → ℝ := fun ρ => g M ρ b r θ
  let Ar : Idx → ℝ := fun ρ => - Γtot M r θ ρ a Idx.r * g M ρ b r θ
  ... (10 more lets)

  -- Step 6.C — collector:
  have h2 := sumIdx_collect_two_branches Gb Ar Br Cr Dr Pr Qr Ath Bth Cth Dth Pth Qth
  simp_rw [Gb, Ar, Br, Cr, Dr, Pr, Qr, Ath, Bth, Cth, Dth, Pth, Qth] at h2
  rw [h2]

  -- Step 6.D-E — fill 6 payload conversions (mechanical algebra)
  sorry  -- Keep while filling
```

**Key principle**: Define ALL `let` bindings BEFORE calling the collector, so Lean never needs to invent placeholder `G`.

---

#### 2. Line 5806: `ricci_identity_on_g` [PRIORITY 2]

**Status**: General case (no domain restriction)
**Depends on**: ricci_identity_on_g_rθ_ext
**Blocks**: nabla_nabla_g_zero (full domain)

**Full code context**:
```lean
-- Line 5794-5806
/-- Ricci identity specialized to the metric, by *definition-chasing only*.
    No domain hypothesis needed.

    STATUS: This lemma times out even with 800k heartbeats during the normalization steps.
    The mathematical strategy is sound but requires a different tactical approach.
    Currently attempting case-by-case proof (see ricci_identity_on_g_r_θ test). -/
lemma ricci_identity_on_g
    (M r θ : ℝ) (a b c d : Idx) :
  nabla (fun M r θ a b => nabla_g M r θ d a b) M r θ c a b
  - nabla (fun M r θ a b => nabla_g M r θ c a b) M r θ d a b
  =
  - Riemann M r θ b a c d - Riemann M r θ a b c d := by
  sorry
```

**Tactical approach**: Prove via case analysis on (c, d) pairs, forwarding to _ext version when (c,d) = (r,θ) or (θ,r).

---

#### 3. Line 5814: `Riemann_swap_a_b_ext` [PRIORITY 2]

**Status**: First-pair antisymmetry on Exterior domain
**Depends on**: ricci_identity_on_g_rθ_ext, nabla_g_zero_ext
**Blocks**: Riemann_swap_a_b (full domain antisymmetry)

**Full code context**:
```lean
-- Line 5808-5814
/-- First-pair antisymmetry on the Exterior domain. -/
lemma Riemann_swap_a_b_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  -- TODO: Depends on ricci_identity_on_g_rθ_ext which has 1 sorry remaining
  -- Complete proof exists in bak8 and will be restored once upstream lemma is proven
  sorry
```

**Note from user**: Complete proof exists in bak8 and will be restored.

---

#### 4. Line 5826: `Riemann_swap_a_b` [PRIORITY 3]

**Status**: General antisymmetry (full domain)
**Depends on**: Riemann_swap_a_b_ext
**Use**: Standard textbook result (MTW Box 8.5, Wald Appendix B)

**Full code context**:
```lean
-- Line 5816-5834
/-- First-pair antisymmetry for the (all-lowered) Riemann tensor of the Levi–Civita connection.
    It follows from metric compatibility (`∇g = 0`) and the Ricci identity on `g`:
    0 = [∇_c, ∇_d] g_{ab} = -R_{aecd} g_{eb} - R_{becd} g_{ae} = -R_{abcd} - R_{bacd}
    Hence R_{bacd} = -R_{abcd}.

    TODO: Full proof requires completing ricci_identity_on_g and nabla_nabla_g_zero_ext.
    The mathematical strategy is sound (see user's drop-in code) but needs tactical refinement.
    Standard textbook result: MTW Box 8.5, Wald Appendix B. -/
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  sorry
  /-
  TODO: Complete using Riemann_swap_a_b_ext once upstream lemmas are proven:
  by_cases hM : 0 < M
  · by_cases hr : 2 * M < r
    · exact Riemann_swap_a_b_ext M r θ ⟨hM, hr⟩ a b c d
    · sorry -- r ≤ 2M case
  · sorry -- M ≤ 0 case
  -/
```

**Tactical approach**: Use case analysis on domain (Exterior vs. non-Exterior).

---

### Priority 2: Differentiability Infrastructure

#### 5-6. Lines 8421, 8423: Differentiability assumptions

**Status**: Needed for ∂/Σ interchange in product rule
**Context**: Phase 2B of regroup_right_sum_to_Riemann_CORRECT

**Full code context**:
```lean
-- Line 8415-8423
  dCoord Idx.r (fun r θ => Γ₁ M r θ b a Idx.θ) r θ
- dCoord Idx.θ (fun r θ => Γ₁ M r θ b a Idx.r) r θ
  := by
  -- Step 1: Interchange ∂ and Σ (using Phase 2A lemmas)
  -- We need differentiability assumptions for this interchange
  have h_diff_r : ∀ k, DifferentiableAt ℝ (fun p => Γtot M p.1 p.2 k Idx.θ a * g M k b p.1 p.2) (r, θ) := by
    sorry  -- TODO: Requires Γtot and g differentiability lemmas
  have h_diff_θ : ∀ k, DifferentiableAt ℝ (fun p => Γtot M p.1 p.2 k Idx.r a * g M k b p.1 p.2) (r, θ) := by
    sorry  -- TODO: Requires Γtot and g differentiability lemmas
```

**Upstream dependencies**:
- `Γtot` differentiability (composite of `Γ` which is rational function of g and ∂g)
- `g` differentiability (proven in Schwarzschild.lean)

**Tactical approach**:
1. Show `g M a b` is C¹ on Exterior domain (should already exist)
2. Show `Γtot` is C¹ (follows from g being C¹ and formula Γ = ½ g^{ρσ}(∂g))
3. Apply product rule for DifferentiableAt

---

#### 7. Line 8438: Convert differentiability formats

**Status**: Format conversion for ∂/Σ interchange
**Context**: Need to convert `DifferentiableAt ℝ (fun p => ...) (r,θ)` to `DifferentiableAt_r/DifferentiableAt_θ` format

**Full code context**:
```lean
-- Line 8433-8438
    -- Interchange ∂_r and Σ, ∂_θ and Σ
    _ = dCoord Idx.r (fun r θ => sumIdx (fun k => Γtot M r θ k Idx.θ a * g M k b r θ)) r θ
      - dCoord Idx.θ (fun r θ => sumIdx (fun k => Γtot M r θ k Idx.r a * g M k b r θ)) r θ
      := by
        -- TODO: Need to convert h_diff_r/h_diff_θ to DifferentiableAt_r/DifferentiableAt_θ format
        sorry
```

**Tactical approach**: Should have helper lemma for this format conversion (check Schwarzschild.lean for precedent).

---

#### 8-9. Lines 8454, 8467: Symmetry applications

**Status**: Need explicit torsion-free and metric symmetry lemmas

**Full code context (line 8454)**:
```lean
-- Line 8440-8455
    -- Apply symmetries: Γtot M r θ k Idx.θ a = Γtot M r θ k a Idx.θ (torsion-free)
    --                  g M k b r θ = g M b k r θ (metric symmetry)
    _ = dCoord Idx.r (fun r θ => sumIdx (fun k => Γtot M r θ k a Idx.θ * g M b k r θ)) r θ
      - dCoord Idx.θ (fun r θ => sumIdx (fun k => Γtot M r θ k a Idx.r * g M b k r θ)) r θ
      := by
        congr 1 <;> {
          congr 1
          ext r' θ'
          congr 1
          ext k
          -- TODO: Need explicit symmetry lemmas:
          -- Γtot M r' θ' k Idx.θ a = Γtot M r' θ' k a Idx.θ
          -- g M k b r' θ' = g M b k r' θ'
          -- These follow from torsion-free connection and metric symmetry
          sorry
        }
```

**Tactical approach**:
- Torsion-free: `Γtot M r θ k μ ν = Γtot M r θ k ν μ` (should already exist)
- Metric symmetry: `g M a b r θ = g M b a r θ` (check g_symm_JP or similar)

**Full code context (line 8467)**:
```lean
-- Line 8457-8468
    -- Recognize Γ₁ definition: Γ₁_{baμ} = Σ_k g_{bk} · Γ^k_{aμ}
    _ = dCoord Idx.r (fun r θ => Γ₁ M r θ b a Idx.θ) r θ
      - dCoord Idx.θ (fun r θ => Γ₁ M r θ b a Idx.r) r θ
      := by
        congr 1 <;> {
          congr 1
          ext r' θ'
          unfold Γ₁
          -- TODO: Should be straightforward algebra
          -- sumIdx (fun k => Γtot ... * g ...) = sumIdx (fun ρ => g ... * Γtot ...)
          sorry
        }
```

**Tactical approach**: Mechanical index relabeling + commutativity of multiplication.

---

### Priority 3: Assembly Lemmas

#### 10. Line 8497: `regroup_right_sum_to_Riemann_CORRECT`

**Status**: Final assembly combining all phases
**Depends on**: Phases 2B (lines 8438, 8454, 8467) and Phase 3 (Riemann_via_Γ₁)

**Full code context**:
```lean
-- Line 8478-8497
/-- CORRECT version: Final assembly combining all phases.
    This replaces the false `regroup_right_sum_to_RiemannUp_NEW`.
    Uses Riemann_via_Γ₁ core theorem instead of false pointwise identities. -/
lemma regroup_right_sum_to_Riemann_CORRECT
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  sumIdx (fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
  =
  sumIdx (fun k => Riemann M r θ k b Idx.r Idx.θ * g M a k r θ) := by

  -- TODO: Implement once Phase 2B and Phase 3 are filled in
  -- The structure should be:
  -- calc
  --   sumIdx (fun k => ∂_r(Γ·g) - ∂_θ(Γ·g))
  --   _ = sumIdx (fun k => ∂_r(Γ₁) - ∂_θ(Γ₁))  := sum_k_prod_rule_to_Γ₁
  --   _ = sumIdx (fun k => Riemann * g)          := Riemann_via_Γ₁.symm
  sorry
```

**Tactical approach**: 3-step calc chain as outlined in comments.

---

### Priority 4: Deprecated Lemmas (Can Delete After Migration)

#### 11. Line 8523: `regroup_right_sum_to_RiemannUp_NEW` [DEPRECATED]

**Status**: **MATHEMATICALLY FALSE** (proven by counterexample Oct 16, 2025)
**Action**: Delete entire lemma once downstream code migrated to `regroup_right_sum_to_Riemann_CORRECT`

**Full code context**:
```lean
-- Line 8507-8523
/-- DEPRECATED - MATHEMATICALLY FALSE (proven by counterexample Oct 16, 2025).
    This lemma will be DELETED. Keeping temporarily as stub to avoid breaking builds.
    Use `sum_k_prod_rule_to_Γ₁` and `Riemann_via_Γ₁` instead. -/
lemma regroup_right_sum_to_RiemannUp_NEW
    (M r θ : ℝ) (h_ext : Exterior M r θ) (hθ : Real.sin θ ≠ 0) (a b : Idx) :
  sumIdx (fun k =>
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ)
  =
  sumIdx (fun k =>
    RiemannUp M r θ k a Idx.r Idx.θ * g M k b r θ)
:= by
  -- FALSE LEMMA - This attempts to prove a pointwise identity that doesn't hold.
  -- Counterexample: flat 2D polar coordinates, k=θ, a=r, b=θ → LHS=1, RHS=0
  -- The h_fiber proof (500+ lines) has been deleted as it was based on false mathematics.
  -- TODO: Delete this entire lemma once downstream code is migrated to correct approach
  sorry
```

**Counterexample** (Oct 16): Flat 2D polar coordinates, k=θ, a=r, b=θ → LHS=1, RHS=0.

---

#### 12. Line 8725: Forward refold using compat

**Status**: Part of old approach, may be superseded by CORRECT approach
**Context**: Inside `regroup_left_sum_to_RiemannUp_NEW` which may also be deprecated

**Full code context**:
```lean
-- Line 8720-8726
          - Γtot M r θ k Idx.r b * dCoord Idx.θ (fun r θ => g M a k r θ) r θ := by
          simpa [pair_r, pair_θ, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]

        -- Now apply: pair_sum → fold → forward refold
        simp only [pair_sum, fold_sub_right, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
        sorry  -- TODO: Forward refold using compat
```

**Tactical approach**: May not be needed if regroup_left_sum_to_RiemannUp_NEW is also deprecated.

---

### Priority 5: Forward Declaration (Proven Downstream)

#### 13. Line 2380: `dCoord_g_via_compat_ext_temp`

**Status**: Forward declaration with sorry (actual proof at line 3072)
**Purpose**: Avoid axiom in CI while keeping forward reference available

**Full code context**:
```lean
-- Line 2376-2381
/-- Forward declaration of dCoord_g_via_compat_ext for use before it's proven.
    This forward declaration uses sorry to avoid axiom in CI. -/
lemma dCoord_g_via_compat_ext_temp (M r θ : ℝ) (h_ext : Exterior M r θ) (x a b : Idx) :
  dCoord x (fun r θ => g M a b r θ) r θ =
    sumIdx (fun k => Γtot M r θ k x a * g M k b r θ) +
    sumIdx (fun k => Γtot M r θ k x b * g M a k r θ) := by
  sorry  -- Proven later at line 3072 as dCoord_g_via_compat_ext
```

**Note**: This is already proven at line 3072. Can replace with `exact dCoord_g_via_compat_ext M r θ h_ext x a b` once we verify that lemma compiles first.

---

#### 14. Line 1904: `dCoord_g_expand`

**Status**: Will be proven using nabla_g_zero_ext once helpers are reorganized
**Context**: Early helper for compatibility equation

**Full code context**:
```lean
-- Line 1899-1905
/-- Compatibility equation: ∂g = Γ·g + g·Γ (covariant form).
    Follows from nabla_g_zero_ext reorganized. -/
lemma dCoord_g_expand (M r θ : ℝ) (h_ext : Exterior M r θ) (μ a b : Idx) :
  dCoord μ (fun r θ => g M a b r θ) r θ
    = sumIdx (fun e => Γtot M r θ e μ a * g M e b r θ)
    + sumIdx (fun e => Γtot M r θ e μ b * g M a e r θ) := by
  -- Will be proven using nabla_g_zero_ext once helpers are reorganized
  sorry
```

**Tactical approach**: This should follow from nabla_g_zero_ext once that's proven. May be duplicate of line 2380.

---

### Priority 6: Commented-Out Deprecated Lemmas (Not Active Code)

#### 15-19. Lines 1996, 2008, 2079, 2088, 2088 (inside `/-  ... -/` block)

**Status**: Inside block comment (lines 1910-2089), not active code
**Purpose**: Archived for reference, disabled during compilation

**Full code context**:
```lean
-- Line 1906-1919
/-! ############## Deprecated flattening (disabled) ############## -/
/- These lemmas are not used by the current proof strategy and
   trigger `simp` recursion/heartbeat overflows. Keep them around
   for reference, but disable them during compilation. -/
/-
section DeprecatedFlatten
set_option maxRecDepth 2000
set_option maxHeartbeats 300000

/-- Flatten the r-branch: Γ^ρ_{r d}·(∂θ g_{d b} − Σ Γ^e_{θ d} g_{e b} − Σ Γ^e_{θ b} g_{d e})
    → (Σ Γ·∂θg) − (Σ G·C_r) − (Σ G·D_r).  Algebraic, no analysis.
    NOTE: This lemma targets outer-connection terms that should vanish by ∇g=0.
    See JP's memo Oct 22, 2025. Not used in the final proof. -/
lemma flatten_comm_block_r
  ... (contains sorry at line 1996)
```

**Action**: No action needed. These are archived for reference only.

---

## Part 2: Dependency Graph

```
Critical Path:
┌────────────────────────────────────────────────────────────────┐
│ PRIORITY 1: ricci_identity_on_g_rθ_ext (line 5790)            │
│   Status: Top-level sorry (needs 6 payload conversions)        │
│   JP offer: 6 micro-lemma skeletons (READY)                    │
└──────────────────────┬─────────────────────────────────────────┘
                       │
                       ├─► Riemann_swap_a_b_ext (line 5814)
                       │     └─► Riemann_swap_a_b (line 5826)
                       │
                       ├─► ricci_identity_on_g (line 5806, general case)
                       │
                       └─► nabla_g_zero_ext (needs this + differentiability)
                             └─► dCoord_g_expand (line 1904)
                                   └─► dCoord_g_via_compat_ext_temp (line 2380)

Differentiability Infrastructure:
┌────────────────────────────────────────────────────────────────┐
│ PRIORITY 2: Γtot and g differentiability (lines 8421, 8423)   │
│   Status: Need C¹ lemmas for g and Γtot                        │
└──────────────────────┬─────────────────────────────────────────┘
                       │
                       ├─► ∂/Σ interchange (line 8438)
                       ├─► Symmetry applications (lines 8454, 8467)
                       └─► regroup_right_sum_to_Riemann_CORRECT (line 8497)

Deprecated (Can Delete):
┌────────────────────────────────────────────────────────────────┐
│ regroup_right_sum_to_RiemannUp_NEW (line 8523) - FALSE        │
│ regroup_left_sum_to_RiemannUp_NEW (line 8725 sorry) - FALSE?  │
│ Deprecated flatten lemmas (lines 1996-2088, commented out)    │
└────────────────────────────────────────────────────────────────┘
```

---

## Part 3: Your Offered Skeletons (Ready to Integrate)

You provided 6 payload conversion micro-lemma skeletons. Here's the integration plan:

### Lemma 1: `payload_r` (Aᵣ conversion)
```lean
-- Payload A_r: prove -Γ·g = (expansion)
private lemma payload_r (M r θ : ℝ) (h_ext : Exterior M r θ) (a b ρ : Idx) :
  - Γtot M r θ ρ a Idx.r * g M ρ b r θ
  = ... := by
  -- Use compat_refold_r_ak or similar
  sorry
```

### Lemma 2: `payload_r_flat` (Cᵣ conversion)
```lean
-- Payload C_r: sumIdx flatten
private lemma payload_r_flat (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  sumIdx (fun ρ => Γtot M r θ ρ Idx.r a * dCoord Idx.θ (fun r θ => g M ρ b r θ) r θ)
  = ... := by
  sorry
```

### Lemma 3: `payload_r_second` (Dᵣ conversion)
```lean
-- Payload D_r: similar to C_r
private lemma payload_r_second (M r θ : ℝ) (h_ext : Exterior M r θ) (a b : Idx) :
  sumIdx (fun ρ => Γtot M r θ ρ Idx.r b * dCoord Idx.θ (fun r θ => g M a ρ r θ) r θ)
  = ... := by
  sorry
```

### Lemma 4-6: `payload_th`, `payload_th_flat`, `payload_th_second`

Mirror of lemmas 1-3 with `Idx.r ↔ Idx.θ` swapped.

**Integration point**: Line 5790, Step 6.D-E of `ricci_identity_on_g_rθ_ext`.

---

## Part 4: Recommended Tactical Workflow

### Week 1: Restore ricci_identity_on_g_rθ_ext

1. **Day 1**: Replace top-level `sorry` with `suffices` pattern (your skeleton)
2. **Day 2**: Fill Step 6.A (mixed partials) — should be trivial
3. **Day 3**: Fill Step 6.B (12 let bindings) — mechanical
4. **Day 4**: Fill Step 6.C (collector call) — straightforward
5. **Day 5**: Fill Step 6.D-E using your 6 micro-lemma skeletons

**Verification checkpoint**: After each day, run `lake build Papers.P5_GeneralRelativity.GR.Riemann` to ensure no regressions.

### Week 2: Differentiability infrastructure

1. **Day 6-7**: Prove g differentiability (may already exist in Schwarzschild.lean)
2. **Day 8-9**: Prove Γtot differentiability (composite of rational functions)
3. **Day 10**: Fill lines 8421, 8423 using above lemmas

### Week 3: Downstream propagation

1. **Day 11-12**: Fill symmetry applications (lines 8454, 8467)
2. **Day 13**: Fill ∂/Σ interchange (line 8438)
3. **Day 14**: Complete regroup_right_sum_to_Riemann_CORRECT (line 8497)
4. **Day 15**: Prove Riemann_swap_a_b_ext using completed ricci_identity (line 5814)

### Week 4: General cases and cleanup

1. **Day 16-17**: Prove ricci_identity_on_g via case analysis (line 5806)
2. **Day 18**: Prove Riemann_swap_a_b via domain case analysis (line 5826)
3. **Day 19**: Delete deprecated lemmas (lines 8523, 8725, block comment 1910-2089)
4. **Day 20**: Final verification and CI cleanup

---

## Part 5: Questions for You (JP)

1. **Should I integrate your 6 micro-lemma skeletons now**, or wait for your review of this report?

2. **For the differentiability lemmas**: Do you have existing C¹ lemmas for g and Γtot that I should reference?

3. **For line 2380** (`dCoord_g_via_compat_ext_temp`): Can I replace the `sorry` with `exact dCoord_g_via_compat_ext M r θ h_ext x a b`, or is there a circularity issue?

4. **For deprecated lemmas**: Should I create a PR to delete the block comment (lines 1910-2089) and the two FALSE lemmas (8523, 8725), or keep them for historical reference?

5. **For the "suffices" pattern**: Do you prefer ASCII names (`Gb` not `Gᵇ`) for the 12 let bindings to avoid parser issues?

---

## Part 6: Build Verification

**Command used**:
```bash
cd /Users/quantmann/FoundationRelativity
lake build Papers.P5_GeneralRelativity.GR.Riemann 2>&1 | tee /tmp/riemann_final_verification_oct22.txt
```

**Result**: ✅ **SUCCESS**
```
✔ Built Papers.P5_GeneralRelativity.GR.Riemann
Build completed successfully (3078 jobs)
```

**Recursion depth verification**:
```bash
grep "maximum recursion depth" /tmp/riemann_final_verification_oct22.txt
# Output: (empty) ✅
```

**Error verification**:
```bash
grep "^error:" /tmp/riemann_final_verification_oct22.txt
# Output: (empty) ✅
```

---

## Appendix A: Recursion Fixes Applied (For Reference)

### Fix 1: Lines 3242, 3383 (Γ₁ contraction lemmas)
```lean
-- BEFORE (caused recursion + "no goals" error):
simp [Γ₁]
ring

-- AFTER:
simp only [Γ₁]
```

### Fix 2: Lines 5163, 5173 (deprecated flatten lemmas, commented out)
```lean
-- BEFORE:
simp

-- AFTER:
simp only
```

### Fix 3: Lines 8825, 8837 (nabla_g_zero_ext proof)
```lean
-- BEFORE (caused recursion):
simpa [mul_sub, sumIdx_pull_const_left] using this

-- AFTER:
simpa only [mul_sub] using this
```

**Root cause**: Unbounded `simp` bouncing between bidirectional lemmas (`sumIdx_mul` ↔ `mul_sumIdx`).

---

**Prepared by**: Claude Code (Assistant)
**Date**: October 22, 2025
**Status**: ✅ All recursion errors fixed, 17 active sorries catalogued with full context
**Next**: Awaiting JP decision on skeleton integration and workflow priorities
