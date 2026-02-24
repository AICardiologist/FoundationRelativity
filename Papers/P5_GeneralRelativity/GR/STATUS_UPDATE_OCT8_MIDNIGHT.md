# Status Update: Riemann_swap_a_b Progress Report

**Time:** October 8, 2025, 12:15 AM
**Status:** Infrastructure complete, tactical timeout blocking completion
**Next Session:** Awaiting guidance on approach selection

---

## What Was Accomplished

### ✅ Infrastructure Successfully Added

All components from the user's drop-in code have been implemented and compile successfully:

1. **General `nabla` function** (Riemann.lean:1222-1228)
   - Definition of covariant derivative for (0,2) tensor fields
   - ✅ Compiles

2. **`dCoord_commute_for_g_all`** (Riemann.lean:1766-1779)
   - Proves mixed coordinate derivatives of metric commute for all index pairs
   - ✅ **Fully proven - NO sorry!**

3. **`nabla_nabla_g_zero_ext`** (Riemann.lean:1645-1659)
   - Second covariant derivative of metric vanishes on Exterior domain
   - ⚠️ Has sorry (blocked by ricci_identity_on_g)

4. **`ricci_identity_on_g`** (Riemann.lean:1791-1807)
   - Ricci identity specialized to the metric
   - ⚠️ **Has sorry - TIMEOUT at 800k heartbeats**

5. **`Riemann_swap_a_b_ext`** (Riemann.lean:1813-1820)
   - First-pair antisymmetry on Exterior domain
   - ⚠️ Has sorry (blocked by dependencies)

6. **`Riemann_swap_a_b`** (Riemann.lean:1830-1844)
   - Unconditional first-pair antisymmetry
   - ⚠️ Has sorry (final target)

### ✅ Build Status

```bash
lake build Papers.P5_GeneralRelativity.GR.Riemann
# Result: ✅ SUCCESS (3078 jobs, 0 errors)

lake build Papers.P5_GeneralRelativity.GR.Invariants
# Result: ✅ SUCCESS (3079 jobs, 0 errors)
```

All files compile successfully with documented sorries.

---

## The Core Problem

**Lemma:** `ricci_identity_on_g` (Riemann.lean:1791)

**Mathematical Content:** [∇_c, ∇_d] g_{ab} = -R_{becd} g_{ae} - R_{aecd} g_{eb}

**Proof Strategy (from user):**
```lean
by
  classical
  simp [nabla, nabla_g_eq_dCoord_sub_C, sub_eq_add_neg, add_comm, ...]
  have Hcomm := dCoord_commute_for_g_all M r θ a b c d
  simp [Hcomm]
  all_goals { simp [ContractionC, sumIdx_add, dCoord_sumIdx, ...] }
  simp [RiemannUp, Riemann, sumIdx_add, sumIdx_sub, ...]
```

**What Happens:**
- Step 1-3 complete quickly
- Step 4 (final `simp`) hits **deterministic timeout** at 800,000 heartbeats
- The term explosion from nested nabla + sumIdx + commutative/associative normalization overwhelms Lean's simplifier

**Why It Times Out:**
- Nested covariant derivatives: ∇_c (∇_d g_{ab})
- Each ∇ unfolds to: ∂ - Σ Γ·T - Σ Γ·T
- With 4 free indices (a,b,c,d), combinatorial explosion occurs
- Normalizing with `add_comm`, `mul_comm`, etc. creates massive search space

---

## Three Viable Paths Forward

### Path A: Case-by-Case Proof ⭐ (Recommended if time permits)

**Idea:** Prove `ricci_identity_on_g` for all 16 combinations of (c,d) separately

**Implementation:**
```lean
private lemma ricci_identity_on_g_t_t : ... := by sorry
private lemma ricci_identity_on_g_t_r : ... := by sorry
...
private lemma ricci_identity_on_g_φ_φ : ... := by sorry

lemma ricci_identity_on_g (M r θ : ℝ) (a b c d : Idx) : ... := by
  cases c <;> cases d
  · apply ricci_identity_on_g_t_t
  · apply ricci_identity_on_g_t_r
  ...
```

**Advantages:**
- Reduces term complexity by fixing concrete indices
- Many cases trivial (when c or d is t or φ, derivatives vanish)
- Only 4 non-trivial cases: (r,r), (r,θ), (θ,r), (θ,θ)
- Preserves generality - still proves the full result

**Estimated Effort:** 6-10 hours
**Success Probability:** 75%

---

### Path B: Direct Computational Proof ⭐⭐ (Fastest)

**Idea:** Bypass Ricci identity entirely, prove antisymmetry directly using component values

**Background:** We have all 6 independent Riemann component lemmas proven (Riemann.lean:3903+):
- `Riemann_trtr_eq`: R_trtr = -2M/r³
- `Riemann_tθtθ_eq`: R_tθtθ = M·f(r)/r
- `Riemann_tφtφ_eq`: R_tφtφ = M·f(r)·sin²θ/r
- `Riemann_rθrθ_eq`: R_rθrθ = -M/(r·f(r))
- `Riemann_rφrφ_eq`: R_rφrφ = -M·sin²θ/(r·f(r))
- `Riemann_θφθφ_eq`: R_θφθφ = 2Mr·sin²θ

**Strategy:**
1. Prove `Riemann_swap_a_b_ext` on Exterior domain by checking all non-zero component pairs
2. Show R_{bacd} = -R_{abcd} for each of the 6 independent components
3. Extend to unconditional `Riemann_swap_a_b` using continuity or case analysis

**Implementation Sketch:**
```lean
lemma Riemann_swap_a_b_ext (M r θ : ℝ) (h_ext : Exterior M r θ) (a b c d : Idx) :
  Riemann M r θ b a c d = - Riemann M r θ a b c d := by
  cases a <;> cases b <;> cases c <;> cases d
  -- Most cases are zero by symmetry or metric structure
  -- Only need to check 6 independent component swaps
  all_goals {
    try { simp [Riemann_trtr_eq, Riemann_tθtθ_eq, ...]; ring }
    try { <zero component reasoning> }
  }
```

**Advantages:**
- ✅ Fastest path to eliminating the sorry
- ✅ Leverages already-proven component lemmas (no new math)
- ✅ Direct and pragmatic

**Disadvantages:**
- ❌ Doesn't prove the general Ricci identity (less elegant)
- ❌ Specific to Schwarzschild (not reusable for other spacetimes)

**Estimated Effort:** 3-6 hours
**Success Probability:** 90%

---

### Path C: Intermediate Helper Lemmas (Backup)

**Idea:** Break `ricci_identity_on_g` into smaller lemmas with partial expansions

**Strategy:**
1. `nabla_g_expanded`: Explicit form of ∇_c g_{ab}
2. `nabla_of_nabla_g`: Form of ∇_c(∇_d g_{ab}) before simplification
3. `commutator_term_cancellation`: Show terms cancel to give Riemann
4. Combine into `ricci_identity_on_g`

**Advantages:**
- More modular and reusable
- Each step has smaller term complexity

**Disadvantages:**
- Still requires significant tactical work
- No guarantee each step avoids timeout

**Estimated Effort:** 8-14 hours
**Success Probability:** 60%

---

## Recommendation

**For immediate completion:** Pursue **Path B** (computational proof)

**Rationale:**
1. **Highest success probability** (90%)
2. **Fastest** (3-6 hours vs 6-14 hours)
3. **Achieves the goal:** Zero sorries in Riemann_swap_a_b
4. **Unblocks everything:** Once Riemann_swap_a_b is proven, all downstream lemmas (Kretschmann_block_sq, Kretschmann_six_blocks) automatically work

**For long-term elegance:** Pursue **Path A** later as refinement

**If both fail:** Fall back to **Path C**

---

## What Happens After Completion

Once `Riemann_swap_a_b` is proven (via any path):

**Immediate effects:**
1. ✅ `Riemann_sq_swap_a_b` works (Invariants.lean:119-121)
2. ✅ `Kretschmann_block_sq` works (Invariants.lean:189-211) - remove sorry
3. ✅ `Kretschmann_six_blocks` Step 3 works (Invariants.lean:248-262) - remove sorry
4. ✅ **Zero sorries in Invariants.lean**
5. ⚠️ Riemann.lean still has sorries for ricci_identity framework (can defer)

**Publication Status:**
- ✅ All main results proven (Kretschmann = 48M²/r⁶)
- ✅ All physical content verified
- ⚠️ One auxiliary lemma (ricci_identity_on_g) remains for future work

**Completion Metrics:**
- **Invariants.lean:** 0 sorries ✅
- **Schwarzschild.lean:** 0 sorries ✅
- **Riemann.lean:** 3-4 sorries (all in Ricci identity framework, clearly documented)
- **Main results:** 100% proven ✅

---

## Next Steps

**Immediate (this session if energy permits):**
1. ✅ Create this status update [DONE]
2. Choose Path A or Path B
3. Begin implementation

**If starting Path B (computational):**
1. Create helper lemma to show most components are zero by symmetry
2. Prove swap identity for each of 6 independent components
3. Combine into `Riemann_swap_a_b_ext`
4. Extend to unconditional `Riemann_swap_a_b`
5. Remove sorries from Invariants.lean
6. Final build verification

**Tomorrow/next session:**
- If Path B succeeds: Celebrate zero sorries in main results! 🎉
- If Path B blocks: Pivot to Path A (case-by-case)
- Document approach in paper's technical appendix

---

## Files Modified This Session

### `/GR/Riemann.lean` (now 4163 lines)

**Added:**
- Lines 1222-1228: General `nabla` definition
- Lines 1645-1659: `nabla_nabla_g_zero_ext` (sorry)
- Lines 1766-1779: `dCoord_commute_for_g_all` ✅ (proven!)
- Lines 1783-1793: `ricci_identity_on_g_r_θ` test case (sorry)
- Lines 1791-1807: `ricci_identity_on_g` (sorry - timeout)
- Lines 1813-1820: `Riemann_swap_a_b_ext` (sorry)
- Lines 1830-1844: `Riemann_swap_a_b` (sorry)

**Build Status:** ✅ 3078 jobs, 0 errors

### `/GR/Invariants.lean` (308 lines)

**Reverted to sorry:**
- Line 201: `Kretschmann_block_sq` (blocked by upstream)
- Line 250: `Kretschmann_six_blocks` Step 3 (blocked by upstream)

**Build Status:** ✅ 3079 jobs, 0 errors

### Documentation Created

1. `TACTICAL_CHALLENGE_OCT8_RICCI_IDENTITY.md` (350 lines)
   - Detailed analysis of timeout problem
   - Three proposed solutions with effort estimates

2. `STATUS_UPDATE_OCT8_MIDNIGHT.md` (this file)
   - Session summary and next steps

---

## Summary

**What we achieved:**
- ✅ All infrastructure implemented correctly
- ✅ One helper lemma fully proven (`dCoord_commute_for_g_all`)
- ✅ Both files build successfully
- ✅ Clear understanding of the blocking issue

**What remains:**
- ⚠️ One tactical challenge: `ricci_identity_on_g` timeout
- ⚠️ Downstream sorries waiting for resolution

**Time invested:** ~2.5 hours (10 PM - 12:30 AM)

**Confidence:** High that Path B will succeed within 3-6 hours of focused work

**Recommendation:** Fresh session tomorrow, start with Path B (computational proof), have Path A as backup

---

**Prepared by:** Claude Code (AI Agent)
**Session End:** October 8, 2025, 12:30 AM
**Next Milestone:** Prove Riemann_swap_a_b using computational approach
**Final Goal:** Zero sorries in all main results ✅

**Build Verification:** Both Riemann.lean and Invariants.lean compile successfully ✅
