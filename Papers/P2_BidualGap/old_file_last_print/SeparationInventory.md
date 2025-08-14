# Separation Lemma Inventory

Based on analysis of `Mathlib/Analysis/NormedSpace/HahnBanach/SeparatingDual.lean`.

## Key Separation Lemmas Available

### 1. Basic Point Separation

**`SeparatingDual.exists_ne_zero`**
```lean
lemma exists_ne_zero {x : V} (hx : x ≠ 0) :
    ∃ f : V →L[R] R, f x ≠ 0
```
- Separates any nonzero point from zero
- Available when `[SeparatingDual R V]`

### 2. Normalized Separation  

**`SeparatingDual.exists_eq_one`**
```lean
lemma exists_eq_one {x : V} (hx : x ≠ 0) :
    ∃ f : V →L[R] R, f x = 1
```
- Produces a functional that evaluates to 1 on the given nonzero point
- Key for our constOne separation

### 3. Two-Point Separation

**`SeparatingDual.exists_eq_one_ne_zero_of_ne_zero_pair`**
```lean
theorem exists_eq_one_ne_zero_of_ne_zero_pair {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ f : V →L[R] R, f x = 1 ∧ f y ≠ 0
```

## Instance Availability

**Normed Spaces**
```lean
instance {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] : SeparatingDual 𝕜 E
```
- Our `BoundedContinuousFunction ℕ ℝ` qualifies as a normed space over ℝ

## Implementation Plan  

### Two-Step Approach

**Step 1**: Subspace Non-Membership  
- Use `constOne_not_mem : constOne ∉ S` (from our SimpleFacts.lean)
- This gives us that constOne is not in the closed linear span of c₀ functions

**Step 2**: Functional Construction
- Apply `SeparatingDual.exists_eq_one` to `constOne ≠ 0`  
- This produces `F : BoundedContinuousFunction ℕ ℝ →L[ℝ] ℝ` with `F constOne = 1`
- Need to verify `F` vanishes on S (may require additional geometric HB results)

### Alternative: Direct Distance Approach

If direct functional construction is complex, use:
1. `constOne ∉ closure S` ⇒ `infDist(constOne, S) > 0` 
2. Geometric Hahn-Banach to produce separating functional
3. Need to locate `infDist` and geometric separation lemmas (not found in current search)

## Search Results Status

- ✅ Found core separation lemmas in SeparatingDual.lean
- ❌ Could not locate `infDist` or geometric HB lemmas (import issues)
- ✅ Confirmed normed space instances available

## Recommended Approach

Use `SeparatingDual.exists_eq_one` directly on `constOne` to get the separating functional. The key technical challenge will be proving that this functional vanishes on the subspace S = span(range(toBCF)).