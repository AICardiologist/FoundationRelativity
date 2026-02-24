# Algebra Challenge: Line 3786 - Detailed Analysis
**Date:** October 11, 2025
**Status:** Multiple approaches attempted, unsolved goal persists

---

## The Goal

After expanding Christoffel symbols and applying field_simp:
```
M r θ : ℝ
h_ext : Exterior M r θ
hr : r ≠ 0
hf : f M r ≠ 0
hD : r - 2 * M ≠ 0

⊢ r * M * (r - M * 2)⁻¹ + (-(M * 2) - M ^ 2 * (r - M * 2)⁻¹ * 2) = -M
```

**Key Issue:** The denominator appears as `(r - M * 2)⁻¹` but our hypothesis is `r - 2 * M ≠ 0`.
These are equal (`M * 2 = 2 * M` by commutativity), but Lean's pattern matching doesn't unify them automatically.

---

## Approaches Attempted

### Attempt 1: Direct field_simp with hD
```lean
have hD : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]
field_simp [hr, hD]
ring
```
**Result:** field_simp doesn't recognize `(r - M * 2)⁻¹` as matchable with `hD`.

### Attempt 2: Normalize with simp [two_mul]
```lean
have hD : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]
simp [two_mul]  -- Try to normalize 2*M expressions
field_simp [hD]
ring
```
**Result:** `simp [two_mul]` creates different normalization issues.

### Attempt 3: Normalize M*2 → 2*M in simp_only
```lean
simp only [Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, div_eq_mul_inv, f, pow_two, mul_comm M 2]
have hD : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]
field_simp [hr, hD]
ring
```
**Result:** Still doesn't clear the denominators.

### Attempt 4: Expand f early
```lean
simp only [Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, div_eq_mul_inv, f, pow_two]
have hD : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]
field_simp [hr, hD]
ring
```
**Result:** Slightly different goal shape, still unsolved.

---

## Why This Is Hard

1. **Commut ativity Mismatch:** `r - M * 2` vs `r - 2 * M` are definitionally equal but field_simp's pattern matcher doesn't automatically try commutativity.

2. **Multiple Denominators:** Even after attempting normalization, we have:
   - `(r - M * 2)⁻¹` appears twice in the goal
   - But in different contexts (once multiplied by `r * M`, once by `M ^ 2 * 2`)

3. **f Expansion:** When `f` is expanded, it introduces `1 - 2*M/r` which becomes `(r - 2*M)/r`, adding more structure.

---

## What Should Work (Pencil Proof)

Let D = r - 2M. The goal is:
```
(r * M) / D  - 2M - (2 * M²) / D = -M
```

Multiply through by D:
```
r * M - 2M * D - 2 * M² = -M * D
```

Expand D:
```
r * M - 2M * (r - 2M) - 2 * M² = -M * (r - 2M)
r * M - 2M*r + 4M² - 2M² = -M*r + 2M²
r * M - 2M*r + 2M² = -M*r + 2M²
-M*r + 2M² = -M*r + 2M²  ✓
```

So the identity IS true. Lean should be able to verify this with field_simp + ring.

---

## Hypothesis

The issue might be that after the FIRST field_simp (line 3814), some simplification happened that changed the goal shape in a way that makes the SECOND field_simp (line 3816) not recognize the denominators properly.

**Possible Solution:** Don't do the first field_simp at all. Instead:
1. simp_only to expand definitions
2. Immediately do ONE field_simp with all hypotheses
3. ring

OR: Need to prove `r - M * 2 ≠ 0` explicitly (which is just `r - 2 * M ≠ 0` by commutativity).

---

## Request for JP

Could you provide the EXACT sequence starting from after:
```lean
rw [shape, hderθθ]
```

What should the next lines be to:
1. Expand the Christoffel symbols
2. Clear all denominators
3. Close with ring

Specifically:
- Should I include `f` in the initial simp_only or not?
- Should there be ONE field_simp or TWO?
- What exact hypotheses should field_simp receive?
- Is there a lemma that relates `r - M * 2` to `r - 2 * M`?

---

## Current Code

```lean
lemma RiemannUp_r_θrθ_ext
  (M r θ : ℝ) (h_ext : Exterior M r θ) :
  RiemannUp M r θ Idx.r Idx.θ Idx.r Idx.θ = -M / r := by
  classical
  have hr : r ≠ 0 := Exterior.r_ne_zero h_ext
  have hf : f M r ≠ 0 := Exterior.f_ne_zero h_ext

  have shape :
      RiemannUp M r θ Idx.r Idx.θ Idx.r Idx.θ
        = deriv (fun s => Γ_r_θθ M s) r
            + Γ_r_rr M r * Γ_r_θθ M r
            - Γ_r_θθ M r * Γ_θ_rθ r := by
    unfold RiemannUp
    simp only [dCoord_r, dCoord_θ, sumIdx_expand, Γtot,
      Γtot_r_θθ, Γtot_r_rr, Γtot_θ_rθ, deriv_const]
    ring

  have hderθθ : deriv (fun s => Γ_r_θθ M s) r = -1 := by
    have : (fun s => Γ_r_θθ M s) = (fun s => -(s - 2*M)) := by
      funext s; simp [Γ_r_θθ]
    simpa [this, deriv_neg, deriv_sub, deriv_const] using (deriv_id (x := r))

  rw [shape, hderθθ]
  simp only [Γ_r_rr, Γ_r_θθ, Γ_θ_rθ, div_eq_mul_inv, f, pow_two, mul_comm M 2]
  have hD : r - 2 * M ≠ 0 := by linarith [h_ext.hr_ex]
  field_simp [hr, hD]
  ring  -- ← FAILS HERE with unsolved goal
```

---

**Bottom Line:** The algebra is correct (pencil proof works), but the tactical sequence to get Lean to verify it eludes me. Need JP's expert guidance on the exact incantation.
