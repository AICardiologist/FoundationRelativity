# STATUS: Pointwise Pattern Implementation Blocked

**Date**: November 7, 2025
**Status**: 🔴 **Blocked - pattern mismatch at RHS folding step**

---

## Summary

Attempted to implement Paul's pointwise reduction pattern for `hb_plus` and `ha_plus` helpers. The basic structure compiles but we hit an error at step 2 (folding the RHS into a single sumIdx).

**Current error count**: 19 errors (baseline was 18)

---

## Implementation Attempted

### Pattern Used (Both Helpers)

```lean
have hb_plus :
    (sumIdx B_b) - sumIdx (...) + sumIdx (...)
  = - sumIdx (fun ρ => RiemannUp...) + rho_core_b := by
  classical

  -- 1) Repack LHS to pointwise form
  rw [hb_pack]

  -- 2) Unfold rho_core_b and fold RHS into single sumIdx
  simp only [h_rho_core_b]
  rw [sumIdx_neg, ← sumIdx_add_distrib]  -- ← FAILS HERE

  -- 3) Reduce to pointwise equality
  apply sumIdx_congr
  intro ρ

  -- 4) Pointwise algebra
  simp only [B_b, nabla_g, RiemannUp, sub_eq_add_neg, neg_mul, mul_neg]

  -- Split on ρ = b for Kronecker delta
  split_ifs with h_rho_eq_b <;> sorry
```

---

## The Blocker

### Error at Line 8762 (hb_plus) and 9004 (ha_plus)

```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sumIdx fun i => -?f i
in the target expression
  (sumIdx fun ρ => B_b ρ - Γtot... + Γtot...) =
    (-sumIdx fun ρ => RiemannUp...) + sumIdx fun ρ => g M ρ ρ r θ * (...)
```

### The Problem

After `simp only [h_rho_core_b]`, the RHS is:
```
(-sumIdx fun ρ => RiemannUp...) + sumIdx fun ρ => g M ρ ρ r θ * (...)
```

We're trying to use `sumIdx_neg` to convert the negation from outside the sumIdx to inside:
- Have: `- sumIdx f`
- Want: `sumIdx (fun i => - f i)`

But `sumIdx_neg` has signature:
```lean
lemma sumIdx_neg (f : Idx → ℝ) :
  sumIdx (fun i => - f i) = - sumIdx f
```

Using it with `←` should rewrite `- sumIdx f` to `sumIdx (fun i => - f i)`, but Lean can't find the pattern.

### Possible Causes

1. **Pattern matching issue**: The negation might be parenthesized or have implicit arguments that prevent pattern matching
2. **Wrong direction**: Maybe we need to use the lemma in the forward direction?
3. **Wrong lemma**: Maybe we need a different lemma for this transformation?
4. **Wrong assumption about h_rho_core_b**: Maybe after unfolding `h_rho_core_b`, the RHS doesn't have the form we expect?

---

## Questions for Paul/JP

1. **Is the `sumIdx_neg` + `sumIdx_add_distrib` approach correct?**
   - Should we be folding the RHS into a single sumIdx before reducing to pointwise?

2. **Alternative folding approach?**
   - Could we use `simp only [← sumIdx_neg, ← sumIdx_add_distrib]` instead?
   - Or maybe `conv` to target specific parts?

3. **Different strategy?**
   - Should we skip step 2 entirely and work with the two separate sumIdx terms on the RHS?
   - Would that make the pointwise proof more complex?

4. **What does the goal state look like after `simp only [h_rho_core_b]`?**
   - Can you verify what form `h_rho_core_b` unfolds to?
   - Is it already in a form that's ready for `sumIdx_congr`?

---

## Full Error List (19 errors)

**In `hb_plus` (lines 8748-8773)**: 6 errors
- 8762: Tactic `rewrite` failed (sumIdx_neg)
- 8779: unsolved goals
- 8929: failed to synthesize
- 8944: unsolved goals
- 8961: Type mismatch
- 8965: Tactic `rewrite` failed

**In `ha_plus` (lines 8990-9015)**: 6 errors
- 9004: Tactic `rewrite` failed (sumIdx_neg)
- 9022: unsolved goals
- 9170: failed to synthesize
- 9185: unsolved goals
- 9203: Type mismatch
- 9207: Tactic `rewrite` failed

**Outside helpers (baseline + shifted)**: 7 errors
- 9247, 9252: calc errors
- 9493, 9694, 9708: Type mismatch / rewrite failures
- 9777, 9888: unsolved goals

---

## Files

**Modified**: `Riemann.lean`
- `hb_plus` helper: lines 8748-8773
- `ha_plus` helper: lines 8990-9015

**Build log**: `/Users/quantmann/FoundationRelativity/Papers/P5_GeneralRelativity/GR/build_step9_fixes_verified_nov7.txt`

---

## Next Steps

Awaiting guidance on:
1. Whether the `sumIdx_neg` + `sumIdx_add_distrib` folding approach is correct
2. How to fix the pattern matching issue if the approach is correct
3. Whether to try an alternative approach (e.g., skip step 2, different lemmas, etc.)

---

**Status**: Blocked - need clarification on correct folding pattern for RHS.
