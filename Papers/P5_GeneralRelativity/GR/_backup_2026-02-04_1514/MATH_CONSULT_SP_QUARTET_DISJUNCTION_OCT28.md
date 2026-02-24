# Mathematical Consultation Request: ΓΓ Quartet Splitter Disjunction

**To**: Senior Professor (SP) - Mathematical Physics
**From**: Implementation Team (Claude Code + JP)
**Date**: October 28, 2025
**Status**: 🔴 **BLOCKING** Phase 1 implementation
**Priority**: HIGH - blocks error reduction from 34 → baseline

---

## Executive Summary

We are implementing JP's surgical fixes for Phase 1 (scalar packaging corrections + ΓΓ adapter restoration). The `ΓΓ_quartet_split_b` lemma returns a **disjunction** rather than a plain equality:

```lean
(equality) ∨ g M b b r θ = 0
```

**Question for SP**: In the Schwarzschild exterior region (r > 2M, sin θ ≠ 0), can the diagonal metric component `g M b b r θ` ever be zero? If not, what is the correct way to discharge this disjunction in our proof context?

---

## Context: What We're Doing

### Phase 1 Fixes Applied
1. ✅ Fixed `scalar_finish_bb/aa` - corrected mathematically wrong targets
2. ✅ Added `sumIdx_reduce_by_diagonality_right_comm` with calc chain
3. ✅ Added scalar repack lemmas (`scalar_pack4`, `scalar_pack4_alt`)
4. ✅ Restored ΓΓ adapter swaps (pointwise factor commutations)

### Current Blocker
The `ΓΓ_block` proofs (b-branch line 7919, a-branch line 8084) fail with:

```
error: Type mismatch: After simplification, term
  ΓΓ_quartet_split_b M r θ μ ν a b
 has type
  (((sumIdx fun i => Γtot M r θ b ν i * Γtot M r θ i μ a)
    - sumIdx fun i => Γtot M r θ b μ i * Γtot M r θ i ν a)
   = (sumIdx fun i => Γtot M r θ b μ i * Γtot M r θ i ν a)
    - sumIdx fun i => Γtot M r θ b ν i * Γtot M r θ i μ a))
  ∨ g M b b r θ = 0
but is expected to have type
  [equality of the LHS to bb_core + rho_core_b]
```

---

## Mathematical Question

### The Quartet Splitter Signature

```lean
lemma ΓΓ_quartet_split_b
    (M r θ : ℝ) (μ ν a b : Idx) :
  ( sumIdx (fun ρ => sumIdx (fun e =>
        ((Γtot M r θ ρ μ a * Γtot M r θ e ν ρ)
       - (Γtot M r θ ρ ν a * Γtot M r θ e μ ρ)) * g M e b r θ))
  + sumIdx (fun ρ => sumIdx (fun e =>
        ((Γtot M r θ ρ μ a * Γtot M r θ e ν b)
       - (Γtot M r θ ρ ν a * Γtot M r θ e μ b)) * g M ρ e r θ)) )
  =
    -- bb-core
    ( g M b b r θ
        * (  sumIdx (fun e => Γtot M r θ b μ e * Γtot M r θ e ν a)
           -  sumIdx (fun e => Γtot M r θ b ν e * Γtot M r θ e μ a) ) )
  +
    -- ρρ-core (to be cancelled by the a-branch later)
    ( sumIdx (fun ρ =>
        g M ρ ρ r θ
        * (   Γtot M r θ ρ μ a * Γtot M r θ ρ ν b
            - Γtot M r θ ρ ν a * Γtot M r θ ρ μ b )) )
```

**However**, the actual Lean type shows this is wrapped in an `Or`:

```lean
(equality_shown_above) ∨ g M b b r θ = 0
```

### Why This Disjunction?

Our hypothesis: The proof of `ΓΓ_quartet_split_b` likely uses metric diagonality, and the case split produces:
- **Left disjunct**: The equality holds (assuming g_bb ≠ 0)
- **Right disjunct**: Degenerate case where g_bb = 0

### Physical Context: Schwarzschild Exterior

In Schwarzschild coordinates (r > 2M, sin θ ≠ 0):

```lean
structure Exterior (M r θ : ℝ) : Prop where
  hM : 0 < M
  hr_ex : 2 * M < r
```

The Schwarzschild metric is:
- `g_tt = -(1 - 2M/r)` → negative, non-zero for r > 2M
- `g_rr = 1/(1 - 2M/r)` → positive, non-zero for r > 2M
- `g_θθ = r²` → positive, non-zero for r > 0
- `g_φφ = r² sin² θ` → positive, non-zero for sin θ ≠ 0

**Question 1**: Can any diagonal component `g M b b r θ` (where `b ∈ {t, r, θ, φ}`) ever be zero in the exterior region?

**Question 2**: If the answer is "no, all diagonal components are non-zero", what is the correct approach:
- **Option A**: Add an explicit lemma `g_diag_ne_zero : Exterior M r θ → g M b b r θ ≠ 0` and use `.resolve_right`?
- **Option B**: The splitter should not return an Or at all - is the lemma statement incorrect?
- **Option C**: Something else?

---

## Current Usage Context

### Where We Use This

**File**: `Riemann.lean` lines 7879-7909 (b-branch)

```lean
have ΓΓ_block :
    ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν ρ * g M e b r θ))
    - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ ρ * g M e b r θ)) )
  + ( sumIdx (fun ρ => (Γtot M r θ ρ μ a) * sumIdx (fun e => Γtot M r θ e ν b * g M ρ e r θ))
    - sumIdx (fun ρ => (Γtot M r θ ρ ν a) * sumIdx (fun e => Γtot M r θ e μ b * g M ρ e r θ)) )
  =
    bb_core + rho_core_b := by
  classical
  -- [adapters: swap_rho_mu, swap_rho_nu, swap_rho_mu_b, swap_rho_nu_b]
  simpa [swap_rho_mu, swap_rho_nu, swap_rho_mu_b, swap_rho_nu_b, h_bb_core, h_rho_core_b]
    using ΓΓ_quartet_split_b M r θ μ ν a b
```

### What We Need

We need this to resolve to a **plain equality** so `simpa` can unify types. Currently blocked by the `∨` wrapper.

---

## Proposed Solutions (Pending SP Verification)

### Option A: Add Non-Vanishing Lemma

```lean
/-- In exterior region, all diagonal metric components are non-zero -/
lemma g_diag_ne_zero (M r θ : ℝ) (h_ext : Exterior M r θ) (b : Idx) :
  g M b b r θ ≠ 0 := by
  cases b
  case t => -- g_tt = -(1 - 2M/r) ≠ 0
    simp [g, f]
    -- use h_ext.hr_ex : 2*M < r to show 1 - 2M/r ≠ 0
    sorry
  case r => -- g_rr = 1/(1 - 2M/r) ≠ 0
    simp [g]
    -- use Exterior.f_ne_zero
    exact Exterior.f_ne_zero h_ext
  case θ => -- g_θθ = r² ≠ 0
    simp [g]
    -- use Exterior.r_ne_zero
    exact pow_ne_zero 2 (Exterior.r_ne_zero h_ext)
  case φ => -- g_φφ = r² sin² θ ≠ 0
    simp [g]
    -- need: sin θ ≠ 0 (implicit assumption)
    sorry
```

Then use:

```lean
have h_g_ne_zero : g M b b r θ ≠ 0 := g_diag_ne_zero M r θ h_ext b
have ΓΓ_equality := (ΓΓ_quartet_split_b M r θ μ ν a b).resolve_right h_g_ne_zero
simpa [swap_rho_mu, swap_rho_nu, swap_rho_mu_b, swap_rho_nu_b, h_bb_core, h_rho_core_b]
  using ΓΓ_equality
```

### Option B: Fix Splitter Statement

If the Or is unnecessary, we could strengthen `ΓΓ_quartet_split_b` to assume `g M b b r θ ≠ 0` as a hypothesis:

```lean
lemma ΓΓ_quartet_split_b
    (M r θ : ℝ) (μ ν a b : Idx)
    (h_g_ne_zero : g M b b r θ ≠ 0) :  -- ADD THIS
  [LHS] = [bb_core + rho_core]        -- PLAIN EQUALITY
```

**Question for SP**: Which approach is mathematically correct?

---

## Mathematical Verification Needed

1. **Verify**: In Schwarzschild exterior (r > 2M, sin θ ≠ 0), do we have `g M b b r θ ≠ 0` for all diagonal indices `b`?

2. **Verify**: The φφ component `g_φφ = r² sin² θ` requires `sin θ ≠ 0`. Is this already implicit in our `Exterior` definition, or do we need to add it?

3. **Recommend**: Best approach to handle the Or disjunction:
   - Add non-vanishing lemma + `.resolve_right`?
   - Strengthen splitter statement?
   - Something else?

4. **Verify**: Are there edge cases where a diagonal metric component could vanish that we're missing?

---

## Impact Assessment

**Blocking**: 34 errors currently (vs baseline 32)
**Affected proofs**:
- `ΓΓ_block` b-branch (line 7919)
- `ΓΓ_block` a-branch (line 8084)
- Cascading failures in scalar packaging

**Once resolved**: Expect error count to drop to ~26 errors (below baseline), enabling Phase 2 (collector lemmas).

---

## References

- **Metric definition**: `Riemann.lean` lines ~400-450
- **Exterior definition**: `Riemann.lean` lines ~25-35
- **Splitter proof**: `Riemann.lean` lines 7132-7300 (ΓΓ_quartet_split_b)
- **Previous successful SP consultations**:
  - `MATH_CONSULT_SP_CHRISTOFFEL_EQUALITY_OCT27.md`
  - `MATH_CONSULT_SP_FOUR_BLOCK_VERIFICATION_OCT27.md`

---

## Request Summary

**Specific questions for SP**:
1. Can `g M b b r θ` ever be zero in exterior region?
2. Do we need explicit `sin θ ≠ 0` hypothesis, or is it implicit?
3. Which approach (A or B) is mathematically correct?
4. Any edge cases we're missing?

**Urgency**: High - blocks Phase 1 completion
**Estimated SP time**: 15-20 minutes (review metric properties + recommend approach)

---

**Prepared by**: Claude Code + JP
**Session**: October 28, 2025
**Status**: Awaiting SP mathematical verification

---

**END OF CONSULTATION REQUEST**
