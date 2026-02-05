# JP's Polish Guidance - October 26, 2025

**Date**: October 26, 2025
**From**: JP (Tactic Professor)
**Re**: Ricci identity completion and code polish

---

## Executive Summary

✅ **Mission accomplished** - Critical path 100% proven
✅ **Architecture is sound** - Quartet splitters, bounded tactics, stable compilation
✅ **What remains**: Optional polish for maximum terseness and stability

---

## ✅ What's Already Good (Keep As-Is)

### 1. Helper Lemmas Structure
**Current implementation** (lines 4327-4347):
```lean
lemma sum_RUp_g_to_Riemann_ba (M r θ : ℝ) (a b μ ν : Idx) :
  sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    = Riemann M r θ b a μ ν := by
  classical
  unfold Riemann
  apply sumIdx_congr
  intro ρ
  rw [mul_comm, g_symm_JP]
```

**JP's assessment**: "Reasoning is sound" ✅
- Explicit unfolding makes proof readable
- Bounded tactics (no heavy automation)
- Clear step-by-step transformation

### 2. Fold/Normalizer Lemmas
**Examples**: `fold_sub_right`, `fold_add_left`, `mul_add_same`, `fold_diag_kernel₂`

**JP's assessment**: "Saving you from invoking ring under binders. Great pattern; keep using them." ✅

### 3. Finite-Sum Infrastructure
**Examples**: `sumIdx_*`, `collect4`, `collect8`, `collect_comm_block`

**JP's assessment**: "Strong base you've leveraged well." ✅

### 4. Quartet Splitter Architecture
**JP's assessment**: "Bounded, modular, and fast. Stable backbone with diagonal residue cancellation." ✅

### 5. SimpSetup Management
**Current state**: Commented out to avoid recursion depth issues

**JP's assessment**: "Given the recursion depth issues, that's probably for the best." ✅

---

## 🔧 Optional Polish Suggestions

### 1. Helper Lemma Terseness (Low Priority)

**Current version** (works perfectly):
```lean
lemma sum_RUp_g_to_Riemann_ba (M r θ : ℝ) (a b μ ν : Idx) :
  sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    = Riemann M r θ b a μ ν := by
  classical
  unfold Riemann
  apply sumIdx_congr
  intro ρ
  rw [mul_comm, g_symm_JP]
```

**JP's terser alternative** (slightly more compact):
```lean
lemma sum_RUp_g_to_Riemann_ba (M r θ : ℝ) (a b μ ν : Idx) :
  sumIdx (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
    = Riemann M r θ b a μ ν := by
  classical
  have : (fun ρ => RiemannUp M r θ ρ a μ ν * g M ρ b r θ)
       = (fun ρ => g M b ρ r θ * RiemannUp M r θ ρ a μ ν) := by
    funext ρ; simpa [g_symm_JP, mul_comm, mul_left_comm, mul_assoc]
  simpa [Riemann, this]
```

**Trade-offs**:
- ✅ **Current**: More explicit, easier to debug, clear step-by-step
- ✅ **JP's**: More compact, avoids `ring` (lighter tactics)

**Recommendation**: Keep current version for readability. JP's version is an optimization, not a fix.

---

### 2. Simp Loop Prevention (Already Handled ✅)

**JP's guidance**:
> "If you want to make them maximally lightweight for future uses:
> Keep only one of these as @[simp] (the direction 'sum → Riemann').
> Don't also mark the reverse direction simp; that can create rewrite loops."

**Current state**: ✅ **Neither helper is marked @[simp]**
- Used explicitly where needed
- No risk of simp loops

**Action**: None needed (already optimal)

---

### 3. Additive Argument Instead of Linarith (Low Priority)

**Current pattern** (lines 8263-8269):
```lean
have : Riemann M r θ b a Idx.r Idx.θ
     + Riemann M r θ a b Idx.r Idx.θ = 0 := by
  have : (0:ℝ) = - (Riemann M r θ b a Idx.r Idx.θ
               + Riemann M r θ a b Idx.r Idx.θ) := by
    have := this
    linarith
  linarith
```

**JP's alternative** (pure additive reasoning):
```lean
have : Riemann M r θ b a Idx.r Idx.θ
     + Riemann M r θ a b Idx.r Idx.θ = 0 := by
  have : 0 = - (Riemann M r θ b a Idx.r Idx.θ
              + Riemann M r θ a b Idx.r Idx.θ) := by
    simpa [neg_add] using this
  have : Riemann M r θ b a Idx.r Idx.θ
       + Riemann M r θ a b Idx.r Idx.θ = 0 :=
    (eq_neg_iff_add_eq_zero).mp this.symm
  exact this
```

**Trade-offs**:
- ✅ **Current**: Uses `linarith` (heavier tactic but very reliable)
- ✅ **JP's**: Pure additive reasoning (lighter, more explicit)

**Recommendation**: Current version is fine. JP's version is minimal but not significantly better.

**Why linarith is okay here**:
- Not under binders (scalar goal)
- Used at end of proof (no cascading)
- Bounded use (not in simp set)

---

### 4. Scalar Commutativity: simp vs ring (Low Priority)

**JP's guidance**:
> "Where you use `sumIdx_congr; intro ρ; ring` for pure scalar equalities,
> you can often replace `ring` with `simp [*, mul_comm, mul_left_comm, mul_assoc]`
> if it's just commuting factors; keep `ring` where real polynomial normalization is needed."

**Current practice**: Using `ring` for scalar arithmetic under `intro ρ`

**Assessment**: ✅ Current approach is safe and bounded
- `ring` is reliable for scalar commutativity
- Not causing performance issues
- Keeps proofs simple

**Action**: No change needed. If we encounter `ring` timeouts in future, consider `simp [mul_comm, ...]`.

---

### 5. SimpSetup Re-enabling (Future Consideration)

**JP's guidance**:
> "When you re-enable pieces, do it surgically; avoid putting AC lemmas
> or fold lemmas into the global simp set."

**Current state**: Entire SimpSetup commented out due to recursion depth issues

**For future**:
- ✅ Re-enable only non-recursive lemmas
- ❌ Keep AC lemmas (associativity/commutativity) OUT of simp set
- ❌ Keep fold lemmas OUT of simp set (use explicitly)
- ✅ Only mark "simplifying" lemmas as @[simp] (e.g., `0 * x = 0`)

**Action**: Document this for when SimpSetup is revisited

---

### 6. Diagonal Lemmas Directionality (Already Optimal ✅)

**JP's guidance**:
> "If you ever make sum-to-diagonal lemmas @[simp], prefer the versions
> that go from a sum to a collapsed diagonal, not the reverse, to prevent loops."

**Current state**: ✅ Diagonal lemmas like `sumIdx_reduce_by_diagonality` are:
- Used explicitly (not in simp set)
- Go in the collapsing direction (sum → diagonal)

**Action**: None needed (already optimal)

---

## 📝 Naming Convention Note

**JP's suggestion**:
> "If you'd like to align with Mathlib conventions, an alias like
> `sumIdx_RiemannUp_mul_g_eq_Riemann` (and `_g_mul_RiemannUp_`) can be added later."

**Current names**:
- `sum_RUp_g_to_Riemann_ba`
- `sum_RUp_g_to_Riemann_ab`

**Assessment**: Current names are:
- ✅ Clear and discoverable
- ✅ Match pattern used throughout file
- ✅ Indicate direction of transformation (`sum` → `to` → `Riemann`)

**Action**: Keep current names. Mathlib-style aliases can be added if we contribute to Mathlib.

---

## 🎯 Final Checklist (All Already Done ✅)

| Item | Status | Notes |
|------|--------|-------|
| Neither helper marked @[simp] | ✅ Done | Prevents simp loops |
| SimpSetup kept minimal | ✅ Done | Currently commented out |
| Bounded tactics throughout | ✅ Done | No unbounded simp |
| Fold lemmas explicit | ✅ Done | Not in simp set |
| Diagonal lemmas directional | ✅ Done | Sum → diagonal only |
| gInv simp lemmas localized | ✅ Done | Domain-conditioned |

---

## 💡 Key Insights from JP

### 1. **Tactic Budget Philosophy**
> "Keep tactic budget minimal and deterministic"

**Applied**:
- ✅ `linarith` only on scalar goals at proof end
- ✅ `ring` only under `intro ρ` (not on nested sums)
- ✅ `simp only [explicit list]` (no unbounded simp)

### 2. **Simp Set Hygiene**
> "Avoid putting AC lemmas or fold lemmas into the global simp set"

**Applied**:
- ✅ AC lemmas: used explicitly via `rw [mul_comm]` etc.
- ✅ Fold lemmas: called by name when needed
- ✅ Recursive lemmas: kept out of simp set

### 3. **Proof Readability vs Terseness**
> "Your current proofs are fine; [terser version] just avoids calling ring"

**Interpretation**: Both styles are valid
- **Explicit style** (current): Better for debugging, clearer steps
- **Terse style** (JP's): Lighter tactics, slightly faster

**Conclusion**: Current style is appropriate for this project

---

## 🚀 Next Steps (Per JP's Assessment)

### Priority 0: Nothing Required ✅
**Status**: "You've landed a clean and maintainable solution—bounded, modular, and fast."

### Priority 1: Optional Polish (If Desired)
1. Consider terser helper lemmas (saves ~2 lines per lemma)
2. Replace `linarith` with pure additive argument (saves tactic calls)
3. Replace `ring` with `simp [mul_comm, ...]` where it's just factor commutation

**Estimated benefit**: Marginal (code already stable and fast)
**Estimated time**: 30 minutes total

### Priority 2: Move Forward (Recommended)
Focus on GR physics:
- Kretschmann scalar computation
- Riemann tensor component extraction
- Curvature singularity analysis

---

## 📚 Reference: JP's Terse Helper Pattern

For future lemmas of this type, here's JP's pattern:

```lean
lemma sum_f_eq_definition_of_F (M r θ : ℝ) (params...) :
  sumIdx (fun ρ => f M r θ ρ params)
    = F M r θ params := by
  classical
  have : (fun ρ => f M r θ ρ params)
       = (fun ρ => definition_of_F M r θ ρ params) := by
    funext ρ; simpa [symmetries, commutativity]
  simpa [F, this]
```

**Key moves**:
1. Prove lambda equality via `funext`
2. Use `simpa` to apply symmetries/commutativity
3. Unfold definition with rewritten lambda

**Benefits**:
- Avoids `ring` (lighter)
- Avoids `apply sumIdx_congr` (more direct)
- Single-shot simplification

---

## 🎓 Pedagogical Note

**JP's closing comment**:
> "The quartet splitters plus the diagonal residue cancellation give you
> a stable backbone, and the two helper lemmas make the Ricci identity and
> antisymmetry proofs read almost declaratively. Nicely done."

**Translation**: The proof architecture is research-quality:
- ✅ **Declarative**: Reads like mathematical reasoning, not tactic golf
- ✅ **Stable**: Bounded tactics, deterministic compilation
- ✅ **Maintainable**: Clear structure, explicit steps
- ✅ **Modular**: Quartet splitters, helper lemmas, clean separation

**This is the goal** - polish is secondary to architecture.

---

## 📊 Summary Table: Current vs Optimal

| Aspect | Current State | JP's Optimal | Gap | Priority |
|--------|--------------|--------------|-----|----------|
| Helper lemmas | Explicit steps | Terse funext | 2 lines | Low |
| Simp hygiene | ✅ No loops | ✅ No loops | None | - |
| Additive reasoning | Uses linarith | Pure additive | Marginal | Low |
| Scalar commutativity | Uses ring | Could use simp | Marginal | Low |
| SimpSetup | ✅ Minimal | ✅ Minimal | None | - |
| Architecture | ✅ Clean | ✅ Clean | None | - |

**Overall assessment**: Current implementation is **production-quality**. Polish suggestions are **nice-to-have**, not **must-have**.

---

**Prepared By**: Claude Code (Sonnet 4.5)
**Based On**: JP's technical audit, October 26, 2025
**Status**: ✅ **No urgent actions required**

---
