# Corrected Proof Strategy for Ricci Identity - October 23, 2025
**Based on**: Senior Professor feedback (SP_CRITICAL_FEEDBACK_OCT23.md)
**Status**: Ready for JP's tactical implementation guidance

---

## The Goal (Unchanged)

Prove the **general Ricci identity** WITHOUT assuming ∇g = 0:

```lean
lemma ricci_identity_on_g_rθ_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (h_θ : Real.sin θ ≠ 0) (a b : Idx) :
  nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
  - nabla (fun M r θ a b => nabla_g M r θ Idx.r a b) M r θ Idx.θ a b
  =
  - Riemann M r θ b a Idx.r Idx.θ - Riemann M r θ a b Idx.r Idx.θ
```

Mathematical form: `[∇_r, ∇_θ]g_ab = -R_barθ - R_abrθ`

---

## Corrected Strategy (Per SP's Guidance)

### Step 1: Expand Commutator (Treating g as General Tensor)

Expand `[∇_r, ∇_θ]g_ab` into two parts:

**Part A - Partial derivative terms (P_rθ)**:
```
∂_r(∇_θ g_ab) - ∂_θ(∇_r g_ab)
```

**Part B - Outer connection terms (C_rθ)**:
```
-Γ^d_ra (∇_θ g_db) + Γ^d_θa (∇_r g_db)
-Γ^d_rb (∇_θ g_ad) + Γ^d_θb (∇_r g_ad)
```

**Note**: Terms acting on derivative index vanish (torsion-free):
```
(Γ^d_θr - Γ^d_rθ)(∇_d g_ab) = 0
```

**In Lean notation** (our current definitions):
```lean
LHS = nabla (fun M r θ a b => nabla_g M r θ Idx.θ a b) M r θ Idx.r a b
    - nabla (fun M r θ a b => nabla_g M r θ Idx.r a b) M r θ Idx.θ a b
```

**Expands to**:
```lean
= dCoord Idx.r (fun r θ => nabla_g M r θ Idx.θ a b) r θ
  - sumIdx (fun d => Γtot M r θ d a Idx.r * nabla_g M r θ Idx.θ d b) r θ
  - sumIdx (fun d => Γtot M r θ d b Idx.r * nabla_g M r θ Idx.θ a d) r θ
  - (dCoord Idx.θ (fun r θ => nabla_g M r θ Idx.r a b) r θ
     - sumIdx (fun d => Γtot M r θ d a Idx.θ * nabla_g M r θ Idx.r d b) r θ
     - sumIdx (fun d => Γtot M r θ d b Idx.θ * nabla_g M r θ Idx.r a d) r θ)
```

---

### Step 2: Expand ∇g Within P_rθ and C_rθ (WITHOUT Simplifying to 0)

**Key principle**: Do NOT apply ∇g = 0. Instead, expand using definition:

```
∇_θ g_ab = ∂_θ g_ab - Γ^k_θa g_kb - Γ^k_θb g_ak
∇_r g_ab = ∂_r g_ab - Γ^k_ra g_kb - Γ^k_rb g_ak
```

**Substitute into Part A**:
```
P_rθ = ∂_r(∂_θ g_ab - Γ^k_θa g_kb - Γ^k_θb g_ak)
     - ∂_θ(∂_r g_ab - Γ^k_ra g_kb - Γ^k_rb g_ak)
```

**Substitute into Part B**:
```
C_rθ = -Γ^d_ra (∂_θ g_db - Γ^k_θd g_kb - Γ^k_θb g_dk)
     + Γ^d_θa (∂_r g_db - Γ^k_rd g_kb - Γ^k_rb g_dk)
     - Γ^d_rb (∂_θ g_ad - Γ^k_θa g_dk - Γ^k_θd g_ak)
     + Γ^d_θb (∂_r g_ad - Γ^k_ra g_dk - Γ^k_rd g_ak)
```

**In Lean**: This corresponds to expanding `nabla_g` using its definition, then applying product rules to `dCoord` and distributing sums.

---

### Step 3: Commute Mixed Partials (Clairaut's Theorem)

Since Schwarzschild metric is C^∞ on exterior domain:

```
∂_r ∂_θ g_ab = ∂_θ ∂_r g_ab
```

These terms cancel when computing `P_rθ + C_rθ`.

**In Lean**:
```lean
have hmixed :
  dCoord Idx.r (fun r θ => dCoord Idx.θ (fun r θ => g M a b r θ) r θ) r θ
  = dCoord Idx.θ (fun r θ => dCoord Idx.r (fun r θ => g M a b r θ) r θ) r θ := by
  simpa using dCoord_commute_for_g_all M r θ a b Idx.r Idx.θ
```

---

### Step 4: Distribute Product Rules and Interchange ∂/Σ

**For terms like**: `∂_r(Γ^k_θa g_kb)`

Apply product rule:
```
∂_r(Γ^k_θa g_kb) = (∂_r Γ^k_θa) g_kb + Γ^k_θa (∂_r g_kb)
```

**For sums**: Use differentiability to interchange `∂` and `Σ`:
```
∂_r(Σ_k Γ^k_θa g_kb) = Σ_k ∂_r(Γ^k_θa g_kb)
```

**In Lean**: Use existing lemmas:
- `dCoord_sumIdx` (interchange ∂/Σ, requires differentiability)
- Product rule expansion (may need helper lemmas)

**Differentiability**: Use existing lemmas (SP verified ✅):
```lean
differentiableAt_g_all_r / differentiableAt_g_all_θ
differentiableAt_Γtot_all_r / differentiableAt_Γtot_all_θ
```

---

### Step 5: Algebraic Regrouping to Match Riemann Tensor Definition

After expanding, the full expression `P_rθ + C_rθ` will contain terms like:

1. **Christoffel derivative terms**:
   ```
   ∂_r Γ^k_θa g_kb - ∂_θ Γ^k_ra g_kb
   ```

2. **Christoffel product terms** (ΓΓ·g):
   ```
   Γ^d_ra Γ^k_θd g_kb - Γ^d_θa Γ^k_rd g_kb
   Γ^d_ra Γ^k_θb g_dk - Γ^d_θa Γ^k_rb g_dk
   (... and permutations with b-index)
   ```

3. **Mixed partial terms** (cancel via Clairaut):
   ```
   ∂_r ∂_θ g_ab - ∂_θ ∂_r g_ab = 0
   ```

**Goal**: Show these regroup to match RHS definition:
```
-R_barθ - R_abrθ
```

Where Riemann tensor (fully covariant) is defined as:
```
R_abμν = ∂_ν Γ₁_abμ - ∂_μ Γ₁_abν + (ΓΓ terms)
```

Or via the Riemann curvature tensor definition with lowered indices.

**In Lean**: This requires careful term collection, likely using:
- `sumIdx_add_distrib` (distribute sums over addition)
- `sumIdx_mul` / `mul_sumIdx` (factor constants in/out of sums)
- `sumIdx_congr` + `ring` (normalize each summand)
- Collector lemmas (organize terms into blocks matching RHS structure)

---

## Key Difference from Flawed Strategy

### OLD (Flawed) Approach ❌

**Step 2**: Apply ∇g = 0 to simplify
```
∇_θ g_ab = 0, ∇_r g_ab = 0
```

**Result**:
```
LHS = ∂_r(0) - ∂_θ(0) = 0
```

**Problem**: This proves `0 = RHS`, which is the Riemann symmetry, NOT the general identity.

### NEW (Correct) Approach ✅

**Step 2**: Expand ∇g using definition WITHOUT assuming it equals 0
```
∇_θ g_ab = ∂_θ g_ab - Γ^k_θa g_kb - Γ^k_θb g_ak
```

**Result**: After full expansion and regrouping, demonstrate `LHS = RHS` algebraically.

**Validity**: Proves the general Ricci identity as a geometric fact (independent of ∇g = 0).

---

## Technical Challenges and Questions for JP

### Challenge 1: Term Explosion Management

**Issue**: Expanding `[∇_r, ∇_θ]g_ab` fully (without ∇g = 0) creates many terms.

**Questions for JP**:

a) **Should we prove intermediate lemmas** for each expansion step?
   - `expand_nabla_g_r`, `expand_nabla_g_θ` (explicit ∂ - Γ·g - Γ·g)
   - `expand_P_rθ` (partial derivative terms)
   - `expand_C_rθ` (outer connection terms)
   - Then combine: `P_rθ + C_rθ = RHS`

b) **Or work directly** with the full expansion in one proof?
   - More monolithic but potentially clearer

c) **Recommended proof structure**?
   - Still use `suffices` pattern?
   - Or different skeleton?

### Challenge 2: Christoffel Symbol Expansion

**Issue**: Expanding ∂(Γ·g) requires product rule, which creates more terms.

**Questions for JP**:

a) **Should we expand Γ in terms of metric**?
   ```
   Γ^k_μν = (1/2) g^kρ (∂_μ g_ρν + ∂_ν g_ρμ - ∂_ρ g_μν)
   ```

b) **Or work symbolically with Γ**?
   - Keep Γ as atomic symbol
   - Rely on its transformation properties

c) **Which is more tractable in Lean**?

### Challenge 3: Riemann Tensor Definition Match

**Issue**: Need to show final expression matches Riemann tensor definition.

**Questions for JP**:

a) **Which Riemann definition should we match**?
   - Option 1: `R^ρ_σμν` (mixed tensor) then lower with g
   - Option 2: `R_ρσμν` (fully covariant) via Γ₁
   - Option 3: Direct definition in terms of ∂Γ - ∂Γ + ΓΓ - ΓΓ

b) **Is there a lemma** relating our collected terms to the chosen definition?
   - Or do we need to prove this as part of the regrouping?

c) **Pattern for the final `rw` step**?

### Challenge 4: Avoiding Circular Dependencies

**Issue**: Must not use ANY lemma that depends on ∇g = 0 or Riemann symmetries.

**Questions for JP**:

a) **Audit of safe lemmas**: Which of our existing helpers are safe?
   - `dCoord_commute_for_g_all` - assumes only C² (safe ✅)
   - `dCoord_sumIdx` - requires differentiability (safe ✅)
   - `sumIdx_add_distrib`, `sumIdx_mul`, etc. - algebraic (safe ✅)
   - Metric symmetry `g_ab = g_ba` - definitional (safe ✅)
   - Torsion-free `Γ^k_μν = Γ^k_νμ` - definitional (safe ✅)

b) **Forbidden lemmas** to avoid:
   - Anything using `nabla_g_zero` or derivatives
   - Riemann symmetry lemmas
   - `regroup_*_to_Riemann*` (these may assume ∇g = 0)

c) **Should we create a separate section** of "bootstrap lemmas" that are proven WITHOUT ∇g = 0?

---

## What Work Can Safely Continue (SP Verified ✅)

While awaiting revised ricci_identity strategy, these can proceed:

### 1. Differentiability Infrastructure (Lines 8421, 8423, 8438)

**SP's verdict**: ✅ Verified correct

These don't depend on ricci_identity and can be filled:
- Use existing `differentiableAt_g_all_r/_θ`
- Use existing `differentiableAt_Γtot_all_r/_θ`
- JP provided drop-in stubs (in `JP_SKELETONS_OCT22_PASTE_READY.lean` lines 86-130)

**Safe to implement now**.

### 2. Γ₁ Approach Work (Lines 8454, 8467, 8497)

**SP's verdict**: ✅ Verified valid

SP confirmed:
- Q9: Γ₁ identity is valid (doesn't depend on ∇g = 0)
- Q10: Riemann-Γ₁ relation is standard (Wald Eq. 3.4.5)

**BUT**: Check if these depend on ricci_identity before filling.

### 3. Helper Lemmas (JP's Paste-Ready Helpers)

**From JP's message** (Oct 23):
- `g_symm_pointwise` (metric symmetry) - definitional, safe ✅
- `Γtot_lower_symm` (torsion-free wrapper) - definitional, safe ✅

**Safe to add and use via `simp_rw`**.

### 4. Downstream Symmetry Proofs (Lines 5814, 5826)

**SP's verdict**: ✅ Strategy verified correct

But these DEPEND on ricci_identity, so must wait until it's proven.

---

## Proposed Revised Workflow

### Phase 0: Add Safe Helpers (Can Do Now)

1. Add `g_symm_pointwise` (JP's helper)
2. Add `Γtot_lower_symm` (JP's helper)
3. Verify build still clean

**Estimated time**: 15 minutes

### Phase 1: Fill Differentiability Lemmas (Can Do Now)

1. Fill sorries at lines 8421, 8423 using JP's drop-in stubs
2. Fill sorry at line 8438 (format conversion)
3. Verify build still clean

**Estimated time**: 1-2 hours

### Phase 2: Ricci Identity (Awaiting Revised Strategy)

1. Request JP's guidance on Challenges 1-4 above
2. Get revised proof skeleton from JP
3. Implement corrected ricci_identity_on_g_rθ_ext
4. Verify with single-file build

**Estimated time**: TBD (depends on term explosion complexity)

### Phase 3: Downstream Propagation

1. Fill Riemann_swap_a_b_ext (line 5814) - uses ricci_identity + ∇g = 0
2. Fill Riemann_swap_a_b (line 5826) - general case
3. Fill ricci_identity_on_g (line 5806) - general domain case

**Estimated time**: 2-4 weeks (per original tactical plan)

---

## Summary for JP

**Request**: Tactical guidance for implementing corrected ricci_identity strategy

**Specific questions**:
1. Should we break proof into intermediate lemmas or work directly? (Challenge 1)
2. How to handle Christoffel expansion - symbolic or in terms of metric? (Challenge 2)
3. Which Riemann definition to match? (Challenge 3)
4. Audit of safe vs. forbidden lemmas? (Challenge 4)

**What we can do while awaiting answer**:
- Add safe helper lemmas (metric symmetry, torsion-free)
- Fill differentiability lemmas (lines 8421, 8423, 8438)
- Keep file in clean, compilable state

**What we'll hold on**:
- Filling ricci_identity_on_g_rθ_ext (line 5790)
- Any work that depends on it (lines 5806, 5814, 5826)

---

**Date**: October 23, 2025
**Status**: Awaiting JP's tactical guidance on corrected strategy
**Build status**: ✅ (0 errors, 16 sorries, no changes made)
