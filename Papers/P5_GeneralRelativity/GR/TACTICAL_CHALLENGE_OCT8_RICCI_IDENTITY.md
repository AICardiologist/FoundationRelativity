# Tactical Challenge: ricci_identity_on_g Proof

**Date:** October 8, 2025 (Late Night Session, Part 2)
**Status:** ⚠️ **BLOCKED - Computational Timeout**
**Impact:** Blocks completion of Riemann_swap_a_b (last remaining sorry)

---

## Executive Summary

We have successfully implemented all the infrastructure for proving `Riemann_swap_a_b` (first-pair antisymmetry) as specified by the user's drop-in code. However, the central lemma `ricci_identity_on_g` hits a **deterministic timeout** even with 800,000 heartbeats during the normalization phase.

**Current State:**
- ✅ All definitions and lemmas structurally correct
- ✅ Both Riemann.lean and Invariants.lean build successfully (3078/3079 jobs)
- ⚠️ `ricci_identity_on_g` has sorry due to timeout
- ⚠️ Downstream lemmas have sorries pending completion of `ricci_identity_on_g`

**The Issue:** This is not a mathematical problem - it's a **tactical/computational problem**. The proof strategy is sound, but Lean's simplifier cannot handle the term complexity within reasonable resource limits.

---

## What We Implemented

### 1. General `nabla` Function (Riemann.lean:1294-1300)

```lean
/-- Covariant derivative of a (0,2) tensor field T.
    ∇_c T_{ab} = ∂_c T_{ab} - Γ^d_{ca} T_{db} - Γ^d_{cb} T_{ad} -/
noncomputable def nabla (T : ℝ → ℝ → ℝ → Idx → Idx → ℝ)
    (M r θ : ℝ) (c a b : Idx) : ℝ :=
  dCoord c (fun r θ => T M r θ a b) r θ
  - sumIdx (fun d => Γtot M r θ d a c * T M r θ d b)
  - sumIdx (fun d => Γtot M r θ d b c * T M r θ a d)
```

**Status:** ✅ Compiles successfully

### 2. `nabla_nabla_g_zero_ext` (Riemann.lean:1645-1659)

```lean
/-- On the Exterior domain, the second covariant derivative of the metric vanishes. -/
lemma nabla_nabla_g_zero_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ)
    (c d a b : Idx) :
  nabla (fun M' r' θ' a' b' => nabla_g M' r' θ' d a' b') M r θ c a b = 0 := by
  sorry
```

**Status:** ⚠️ Has sorry (pending `ricci_identity_on_g`)
**Mathematical Content:** This should follow easily from `nabla_g_zero` (metric compatibility already proven at lines 1317-1337)

### 3. `dCoord_commute_for_g_all` (Riemann.lean:1764-1779)

```lean
/-- Mixed coordinate derivatives commute for `g` in *all* index directions. -/
lemma dCoord_commute_for_g_all
    (M r θ : ℝ) (a b c d : Idx) :
  dCoord c (fun r θ => dCoord d (fun r θ => g M a b r θ) r θ) r θ
  =
  dCoord d (fun r θ => dCoord c (fun r θ => g M a b r θ) r θ) r θ := by
  cases c <;> cases d
  all_goals
    first
    | exact dCoord_r_θ_commute_for_g M r θ a b
    | exact (dCoord_r_θ_commute_for_g M r θ a b).symm
    | simp [g, dCoord_r, dCoord_θ, dCoord_t, dCoord_φ, deriv_const]
```

**Status:** ✅ Compiles successfully - **no sorry**!

### 4. `ricci_identity_on_g` (Riemann.lean:1791-1807)

```lean
lemma ricci_identity_on_g
    (M r θ : ℝ) (a b c d : Idx) :
  nabla (fun M r θ a b => nabla_g M r θ d a b) M r θ c a b
  - nabla (fun M r θ a b => nabla_g M r θ c a b) M r θ d a b
  =
  - Riemann M r θ b a c d - Riemann M r θ a b c d := by
  sorry
```

**Status:** ⚠️ **TIMEOUT - This is the blocker**

### 5. `Riemann_swap_a_b_ext` (Riemann.lean:1813-1820)

```lean
/-- First-pair antisymmetry on the Exterior domain. -/
lemma Riemann_swap_a_b_ext
    (M r θ : ℝ) (h_ext : Exterior M r θ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  sorry
```

**Status:** ⚠️ Has sorry (blocked by `ricci_identity_on_g`)
**Proof Strategy (once dependencies resolved):**
```lean
by
  have h_ricci := ricci_identity_on_g M r θ a b c d
  have h_zero := nabla_nabla_g_zero_ext M r θ h_ext c d a b
  linarith [h_ricci, h_zero]
```

### 6. `Riemann_swap_a_b` (Riemann.lean:1830-1844)

```lean
/-- First-pair antisymmetry for the Riemann tensor. -/
lemma Riemann_swap_a_b (M r θ : ℝ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  sorry
```

**Status:** ⚠️ Has sorry (blocked by `Riemann_swap_a_b_ext`)

---

## The Timeout Problem

### User's Provided Proof Strategy

```lean
lemma ricci_identity_on_g ... := by
  classical
  -- Step 1: unfold the outer `nabla` and rewrite inner `nabla_g`.
  simp [nabla, nabla_g_eq_dCoord_sub_C, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc, mul_comm, mul_left_comm, mul_assoc, sumIdx_add, sumIdx_sub]
  -- Step 2: Apply commutation
  have Hcomm := dCoord_commute_for_g_all M r θ a b c d
  simp [Hcomm]
  -- Step 3: Simplify ContractionC terms
  all_goals
    first
    | { simp [ContractionC, sumIdx_add, dCoord_sumIdx, sub_eq_add_neg] }
    | { simp [ContractionC, dCoord_mul_of_diff] <;> discharge_diff }
  -- Step 4: Expand Riemann definitions
  simp [RiemannUp, Riemann, sumIdx_add, sumIdx_sub, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
```

### What Happens

**Error at Step 4:**
```
error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (800000) has been reached
```

**Why:**
- The proof involves nested `nabla` applications on the metric
- Each `nabla` unfolds to: derivative - 2 sumIdx terms with Christoffel symbols
- With 4 free indices (a, b, c, d), the term tree explodes combinatorially
- Normalizing with commutative/associative lemmas (`add_comm`, `mul_comm`, etc.) creates a massive search space
- Lean's `simp` tactic tries to find a normal form but exhausts computational resources

**Heartbeat Limits Attempted:**
- Default: 200,000 → Timeout
- Increased: 800,000 → Still timeout
- This suggests we need a fundamentally different approach, not just more resources

---

## Attempted Solutions

### Attempt 1: Increase Heartbeat Limit ❌

```lean
set_option maxHeartbeats 800000 in
lemma ricci_identity_on_g ...
```

**Result:** Still times out at Step 4

### Attempt 2: Break Into Smaller Steps ❌

```lean
simp only [nabla, nabla_g_eq_dCoord_sub_C, sub_eq_add_neg, sumIdx_add, sumIdx_sub]
simp only [Hcomm, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
simp only [ContractionC, sumIdx_add, dCoord_sumIdx, sub_eq_add_neg]
simp only [RiemannUp, Riemann, sumIdx_add, sumIdx_sub, ...]
```

**Result:** Still times out (separating steps doesn't reduce total work)

### Attempt 3: Case-by-Case Analysis (In Progress)

**Idea:** Prove for specific index pairs (c, d) separately, then combine:
```lean
private lemma ricci_identity_on_g_r_θ (M r θ : ℝ) (a b : Idx) : ...
private lemma ricci_identity_on_g_r_r (M r θ : ℝ) (a b : Idx) : ...
...
lemma ricci_identity_on_g (M r θ : ℝ) (a b c d : Idx) : ... := by
  cases c <;> cases d
  all_goals { apply appropriate helper }
```

**Status:** Test case `ricci_identity_on_g_r_θ` added but not yet completed

---

## Proposed Solutions

### Option A: Complete Case-by-Case Proof (Most Viable)

**Strategy:**
1. Prove `ricci_identity_on_g` for all 16 combinations of (c, d) indices
2. Many cases will be trivial (when c or d is t or φ, derivatives vanish)
3. Only (r,r), (r,θ), (θ,r), (θ,θ) are non-trivial
4. Main lemma dispatches by cases

**Estimated Effort:** 4-8 hours
**Probability of Success:** High (80%)
**Advantage:** Reduces term complexity by fixing concrete indices

### Option B: Intermediate Helper Lemmas

**Strategy:**
1. Create lemmas for partial expansions:
   - `nabla_g_expanded`: Explicit form of ∇_c g_{ab}
   - `nabla_nabla_g_expanded`: Explicit form of ∇_c ∇_d g_{ab}
2. Build up to full Ricci identity incrementally
3. Avoid large `simp` calls with many normalizing lemmas

**Estimated Effort:** 6-12 hours
**Probability of Success:** Medium (60%)
**Advantage:** More modular, reusable lemmas

### Option C: Computational Proof via Explicit Components

**Strategy:**
1. Since we have all 6 independent Riemann components (Riemann.lean:4897-5037), prove antisymmetry for each explicitly
2. Use these to prove `Riemann_swap_a_b` directly without the Ricci identity route
3. Bypass the definitional proof entirely

**Estimated Effort:** 3-6 hours
**Probability of Success:** Very High (90%)
**Advantage:** Uses existing proven components, avoids symbolic manipulation
**Disadvantage:** Doesn't establish the general Ricci identity (loses mathematical generality)

### Option D: Custom Tactic or Metaprogramming

**Strategy:**
1. Write a custom tactic in Lean 4 metaprogramming to handle the specific term patterns
2. Control normalization more precisely than `simp` allows
3. Use `conv` mode strategically

**Estimated Effort:** 8-16 hours (requires deep Lean 4 expertise)
**Probability of Success:** Medium (50%)
**Advantage:** Most elegant solution if it works
**Disadvantage:** High complexity, steep learning curve

---

## Recommendation

**Immediate Action:** Pursue **Option A (Case-by-Case)** or **Option C (Computational)**

### Why Option A:
- Most direct adaptation of user's strategy
- Breaks the computational bottleneck by reducing index generality
- Still proves the general result, just by exhaustive cases

### Why Option C:
- Fastest path to eliminating the sorry
- Leverages already-proven component lemmas
- Pragmatic over idealistic

**If both fail:** Consider Option B (intermediate lemmas) or consulting with Lean 4 experts about Option D.

---

## Current File Status

### Riemann.lean (4,065 lines)

**Sorries:**
- Line 1651: `nabla_nabla_g_zero_ext`
- Line 1793: `ricci_identity_on_g_r_θ` (test case)
- Line 1807: `ricci_identity_on_g` ⚠️ **PRIMARY BLOCKER**
- Line 1820: `Riemann_swap_a_b_ext`
- Line 1838: `Riemann_swap_a_b`

**Build Status:** ✅ Compiles successfully (3078 jobs, 0 errors)

### Invariants.lean (308 lines)

**Sorries:**
- Line 201: `Kretschmann_block_sq` (blocked by `Riemann_swap_a_b`)
- Line 250: `Kretschmann_six_blocks` Step 3 (blocked by `Kretschmann_block_sq`)

**Build Status:** ✅ Compiles successfully (3079 jobs, 0 errors)

**Note:** The Kretschmann lemmas had been completed with zero sorries yesterday, but must be reverted to sorry because they depend on `Riemann_sq_swap_a_b` which uses `Riemann_swap_a_b`.

---

## Mathematical Correctness

**Important:** All the mathematics is **100% sound**. The issue is purely tactical:

✅ **Metric compatibility holds:** `nabla_g_zero` proven (lines 1317-1337)
✅ **Mixed derivatives commute:** `dCoord_commute_for_g_all` proven (lines 1764-1779)
✅ **Ricci identity is standard:** MTW §8.6, Wald Appendix B.2
✅ **All Christoffel symbols computed:** Schwarzschild.lean:570-656
✅ **All metric derivatives computed:** Schwarzschild.lean (g_deriv_r, g_deriv_theta)

The proof *should* work by definition-chasing. We're not missing any mathematical ingredients. We just need a tactical approach that Lean can execute within resource constraints.

---

## Dependency Chain

```
ricci_identity_on_g (BLOCKER - timeout)
  ↓
nabla_nabla_g_zero_ext (blocked)
  ↓
Riemann_swap_a_b_ext (blocked)
  ↓
Riemann_swap_a_b (blocked)
  ↓
Riemann_sq_swap_a_b (blocked)
  ↓
Kretschmann_block_sq (blocked)
  ↓
Kretschmann_six_blocks (blocked)
  ↓
Zero sorries project-wide (GOAL)
```

**Bottleneck:** The single lemma `ricci_identity_on_g` at line 1807 is blocking the entire chain.

---

## Session Timeline

**10:00 PM:** Received user's drop-in code with complete proof strategy
**10:15 PM:** Added general `nabla` definition
**10:30 PM:** Added `dCoord_commute_for_g_all` (success!)
**10:45 PM:** Added `ricci_identity_on_g` with user's proof
**11:00 PM:** First timeout at 200k heartbeats
**11:15 PM:** Increased to 800k heartbeats - still timeout
**11:30 PM:** Tried breaking into smaller steps - still timeout
**11:45 PM:** Began investigating case-by-case approach
**12:00 AM:** Created this status report

**Total time spent:** ~2 hours on tactical refinement

---

## Next Steps

1. **Choose approach:** Decide between Option A (case-by-case) vs Option C (computational)
2. **Implement chosen strategy:** Allocate 4-8 hours for focused tactical work
3. **Test on one case:** Verify approach works for at least one specific (c,d) pair
4. **Complete remaining cases:** Systematically work through all required cases
5. **Verify build:** Confirm zero sorries after completion

---

## Questions for User

1. **Preference on approach?** Should we pursue:
   - (A) Case-by-case proof of Ricci identity (more general, longer)
   - (C) Direct computational proof using components (faster, less general)

2. **Acceptable to lose generality?** If we use Option C, we won't have proven the general `ricci_identity_on_g` lemma, only the specific `Riemann_swap_a_b` result. Is this acceptable for publication?

3. **Time constraints?** Is there a deadline that would favor the faster Option C over the more elegant Option A?

4. **Alternative infrastructure?** Do you have any other Lean 4 tactics or lemmas in your broader codebase that might help with large commutative/associative normalizations?

---

**Prepared by:** Claude Code (AI Agent)
**Session timestamp:** October 8, 2025, 12:00 AM
**Status:** ⚠️ **BLOCKED AT TACTICAL LEVEL** - Mathematically sound, computationally intractable
**Recommendation:** Pursue Option A or Option C to unblock

**Build verification:** Both files compile successfully with documented sorries ✅
