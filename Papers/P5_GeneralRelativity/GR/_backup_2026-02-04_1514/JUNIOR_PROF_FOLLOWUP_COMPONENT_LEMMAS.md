# Follow-up Question: Component Lemma Implementation Strategy

**Date:** October 5, 2025
**Context:** Phase 2 Component Lemmas Implementation
**Previous Guidance:** [JUNIOR_PROF_REQUEST_COMPONENT_LEMMAS.md](./JUNIOR_PROF_REQUEST_COMPONENT_LEMMAS.md)

---

## Summary of Progress

Following your guidance from October 5, I attempted to implement the component lemmas:

### ✅ Successfully Implemented (Phase 1 - Helper Lemmas)
```lean
lemma r_mul_f (M r : ℝ) (hr_nz : r ≠ 0) : r * f M r = r - 2 * M
lemma one_minus_f (M r : ℝ) : 1 - f M r = 2 * M / r
```

### ❌ Implementation Blocked (Phase 2 - Component Lemmas)

Attempted to implement:
```lean
lemma Riemann_tθtθ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ = M * f M r / r

lemma Riemann_tφtφ_eq (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ = M * f M r * sin θ ^ 2 / r

-- (similar for rθrθ, rφrφ, θφθφ)
```

---

## Technical Issue Encountered

Your recommended proof strategy was:
```lean
1. Contract first index using Riemann_contract_first
2. Expand RiemannUp only for concrete indices
3. Insert closed-form pieces (derivatives, Christoffel symbols)
4. Close with field_simp + ring
```

### What Happens in Practice

After steps 1-3, the goal before `field_simp` looks like:
```lean
⊢ -(f M r * r ^ 2) + (M * 2 - r) * (-M + -(f M r * r)) = -(f M r * M * r)
```

After `field_simp [hr_nz, hf_nz, pow_two, sq, g, one_minus_f M r]`, the goal becomes:
```lean
⊢ -(f M r * r ^ 2) + (M * 2 - r) * (-M + -(f M r * r)) = -(f M r * M * r)
```

**Problem:** The pattern `r - 2*M` (which would match `rmf : r - 2*M = r * f M r`) doesn't appear anywhere in this normalized form. The `ring` tactic alone cannot recognize that `(M * 2 - r) = -(r - 2*M)`.

### Approaches Tried

1. **Include `rmf` in `field_simp`:**
   ```lean
   field_simp [hr_nz, hf_nz, pow_two, sq, g, rmf, one_minus_f M r]
   ring
   ```
   Result: Creates different normalization issues

2. **Use `rw [rmf]` after `field_simp`:**
   ```lean
   field_simp [hr_nz, hf_nz, pow_two, sq, g, one_minus_f M r]
   rw [←rmf]  -- Fails: pattern r - 2*M not found
   ring
   ```
   Result: Tactic `rewrite` failed: Did not find an occurrence of the pattern

3. **Multi-step `calc` block:**
   ```lean
   field_simp [...]
   calc -(f M r * r ^ 2) + (M * 2 - r) * (-M + -(f M r * r))
       = ... := by ring
     _ = ... := by rw [←rmf]; ring  -- Fails with unsolved goals
   ```
   Result: `ring` inside `calc` creates unsolved subgoals

---

## Specific Questions for Junior Professor

### Question 1: Normalization Strategy
When you said "Close with field_simp + ring", did you mean:

**Option A:** A single combined `field_simp [...]; ring` where `field_simp` does all substitutions?

**Option B:** A multi-step approach like `field_simp; show <expected>; calc ...`?

**Option C:** Something else entirely?

### Question 2: Handling the `r - 2*M = r·f(r)` Identity
The identity `rmf : r - 2*M = r * f M r` is algebraically equivalent to what appears in the goal `(M * 2 - r) = -(r - 2*M)`, but Lean's `field_simp` doesn't recognize this.

**How should this be handled?** Should I:
- Use `conv` tactics to manually rearrange terms before rewriting?
- Create additional helper lemmas for the negated form?
- Use `simp` with custom lemmas to normalize `(M * 2 - r)` to `-(r - 2*M)` first?

### Question 3: Alternative Proof Structure
Is there a fundamentally different proof structure that would avoid these normalization issues? For example:

**Alternative Approach:** Instead of component lemmas, directly prove properties like:
```lean
lemma Riemann_diagonal_cases_alt (M r θ : ℝ) (hM : 0 < M) (hr_ex : 2 * M < r) :
  Riemann M r θ Idx.t Idx.θ Idx.t Idx.θ +
  Riemann M r θ Idx.t Idx.φ Idx.t Idx.φ + ... = [some tractable form]
```

Would this be more amenable to the `field_simp + ring` strategy?

---

## Current Status

**Baseline (c173658):** 9 errors with `lake build`
- 3 infrastructure errors (lines 1939, 2188, 2323)
- 4 diagonal Ricci case errors (lines 5082, 5132, 5171, 5203)
- 2 additional errors

**After component lemma attempts:** 14-18 errors (regression)

**Action taken:** Reverted to baseline c173658 to maintain stability

---

## Request

Could you provide either:

1. **A concrete working example** of one component lemma (e.g., `Riemann_tθtθ_eq`) showing exactly how to handle the `field_simp + ring` step when `r - 2*M = r·f(r)` is involved?

2. **Clarification on the tactical approach** - specifically how to bridge the gap between the `field_simp` normalized form and the desired closed form?

3. **An alternative proof strategy** if the component lemma approach has fundamental issues with the current infrastructure?

---

## Additional Context

**Build validation note:** All testing done with `lake build` (authoritative), not `lake env lean` (can give false positives/negatives per [LAKE_BUILD_VS_LAKE_ENV_LEAN_FINDINGS.md](../../LAKE_BUILD_VS_LAKE_ENV_LEAN_FINDINGS.md)).

**Files:**
- Source: `Papers/P5_GeneralRelativity/GR/Riemann.lean` (5252 lines)
- Baseline commit: c173658
- Stashed work: Contains failed component lemma attempts

Thank you for your guidance!

---

**Generated:** October 5, 2025
**Author:** Claude Code
**Purpose:** Technical consultation on proof tactics for component lemma implementation
