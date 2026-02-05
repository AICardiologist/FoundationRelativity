# JP's Tactical Implementation Guidance - October 23, 2025
**Status**: ✅ READY TO IMPLEMENT - Concrete recipe provided

---

## JP's Verdict on SP's Revised Strategy

✅ **Mathematically sound**: Avoids circularity, matches standard tensorial identity
✅ **Good modularization**: commutator_structure + algebraic_identity is the right split
✅ **Feasible in our codebase**: All machinery already exists

**JP's quote**: "Everything above uses the infrastructure that's already in your file."

---

## Minor Corrections Needed

### 1. Use Correct Lemma Name

❌ **Don't use**: `Γtot_symm` (SP's notation)
✅ **Use**: `Γtot_symmetry` (our actual lemma name)

**Pattern**:
```lean
-- Inside commutator_structure:
simpa using (Γtot_symmetry M r θ lam μ ν)
```

**Location**: Our lemma is exposed around "differentiableAt_Γtot_θ_θr_r" usage sites

---

### 2. Domain Hypotheses (h_ext, h_θ)

**JP's guidance**:

**commutator_structure**:
- Does NOT need h_θ
- Purely algebra/definitions + torsion-free
- Remove h_ext if not needed

**algebraic_identity**:
- DOES need differentiability hypotheses
- When μ=Idx.θ or ν=Idx.θ: need h_θ : Real.sin θ ≠ 0
- Keep exterior/axis hypotheses scoped to dCoord_sumIdx / dCoord_mul_of_diff calls

**Specialized (r,θ) wrapper**:
- Keep h_θ on ricci_identity_on_g_rθ_ext (safe)

---

## Implementation Recipe

### A. `commutator_structure` (SHORT - ~15-20 lines)

**Goal**: Prove `[∇²g]_μνab - [∇²g]_νμab = P_μν + C_aμν + C_bμν`

**Steps**:

1. **Unfold definitions**
   ```lean
   unfold nabla2_g P_terms C_terms_a C_terms_b
   ```

2. **Rearrange with ring**
   - Rewrite subs as `+ (-_)` to line up summands

3. **Torsion cancellation** (THE KEY STEP)
   ```lean
   have torsion_cancel :
       sumIdx (fun lam => Γtot M r θ lam ν μ * nabla_g M r θ lam a b)
     - sumIdx (fun lam => Γtot M r θ lam μ ν * nabla_g M r θ lam a b) = 0 := by
     rw [sub_eq_zero]
     apply sumIdx_congr
     intro lam
     simpa using (Γtot_symmetry M r θ lam μ ν)
   ```

4. **Assemble**
   - Use `ring` or small `calc` chain with `group_sub_add`
   - Result: exactly `P_terms + C_terms_a + C_terms_b`

**Estimated**: 15-20 lines, no differentiability hypotheses needed

---

### B. `algebraic_identity` (HEAVY but MECHANICAL)

**Goal**: Prove `P_μν + C_aμν + C_bμν = -R_baμν - R_abμν`

**JP's recommendation**: "Don't do it monolithically. Stub the four sub-lemmas (B1-B4)."

---

#### B1. Expansion Sub-Lemma

**Name**: `expand_PCaCb_to_main_plus_payload`

**Purpose**: Unfold nabla_g, push dCoord through sums/products

**Steps**:
1. Unfold `nabla_g` inside `P_terms`
2. Push `dCoord` through `sumIdx` via `dCoord_sumIdx`
3. Push `dCoord` through products via `dCoord_mul_of_diff`
4. Use `discharge_diff` tactic for DifferentiableAt_* side conditions

**Shape obtained** (for a-branch):
```
∑_ρ (∂_μ Γ^ρ_νa) g_ρb     [(∂Γ)g term]
+ ∑_ρ Γ^ρ_νa (∂_μ g_ρb)   [Γ∂g payload]
- (swap μ ↔ ν)
```

Plus analogous for b-branch, plus C_a, C_b blocks.

**Result**: Sum of four "commutator blocks", each with:
- Main part: (∂Γ)g + ΓΓg
- Payload part: Γ∂g

---

#### B2. KEY Payload Cancellation

**Names**:
- `payload_cancel_a` (a-branch Γ∂g cancellation)
- `payload_cancel_b` (b-branch Γ∂g cancellation)

**Purpose**: Cancel ALL Γ∂g terms using collector lemmas

**JP's key insight**: "Your collector with extras shines here."

**Pattern for a-branch** (using `sumIdx_collect_comm_block_with_extras`):

Define:
```lean
let G  : Idx → ℝ := fun ρ => g M ρ b r θ
let A  : Idx → ℝ := fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
let B  : Idx → ℝ := fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
let C  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ μ lam * Γtot M r θ lam ν a)
let D  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ ν lam * Γtot M r θ lam μ a)
let P  : Idx → ℝ := fun ρ => Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ
let Q  : Idx → ℝ := fun ρ => Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ
```

**Collector transforms**:
```
(∑ (A*G + P)) - (∑ (B*G + Q)) + (∑ (G*C)) - (∑ (G*D))
= ∑ G*((A-B)+(C-D)) + ∑ (P-Q)
```

**The point** (JP's emphasis):
> "∑ (P-Q) equals (and cancels with) the Γ∂g coming from C_a:
> -∑_λ Γ^λ_μa (∂_ν g_λb) + ∑_λ Γ^λ_νa (∂_μ g_λb)"

**Cancellation**: "Just renaming the dummy index (sumIdx_congr) plus one line of ring."

**Repeat** for b-branch payload against C_b.

**Result**: NO Γ∂g terms left anywhere ✅

---

#### B3. Mixed Partials Cancellation

**Name**: `mixed_partials_cancel_in_P`

**Purpose**: Use Clairaut's theorem to cancel ∂∂g terms

**Pattern**:
```lean
have hmixed := dCoord_commute_for_g_all M r θ a b μ ν
-- Kills the ∂∂g remnants from expanding P before collecting
```

**Location**: These appear if you expand P before applying the collector

---

#### B4. Regroup to Riemann

**Name**: `regroup_main_to_Riemann`

**Purpose**: Recognize remaining terms as Riemann tensor definition

**What remains** (after B2, B3):
```
∑_ρ g_ρb ( ∂_μ Γ^ρ_νa - ∂_ν Γ^ρ_μa
         + ∑_λ (Γ^ρ_μλ Γ^λ_νa - Γ^ρ_νλ Γ^λ_μa) )
```
Plus mirror with a ↔ b.

**This is BY DEFINITION**: `-R_baμν - R_abμν`

**Tools**:
- `simp_rw` to RiemannUp shape
- `sumIdx_collect6` (two ∂Γ and four ΓΓ)
- `Riemann_contract_first` to re-express contraction
- Metric symmetry: `g M a ρ = g M ρ a` where needed

---

## Safe vs. Unsafe Lemmas (Circularity Audit)

### ✅ SAFE to use (inside Ricci identity proof)

**Symmetries**:
- `Γtot_symmetry` (torsion-free)
- `g_symm` / `g_symm_JP` (metric symmetry)

**Differentiability**:
- `differentiableAt_g_all_r` / `differentiableAt_g_all_θ`
- `differentiableAt_Γtot_all_r` / `differentiableAt_Γtot_all_θ`

**Derivative rules**:
- `dCoord_sumIdx`
- `dCoord_mul_of_diff`
- All `dCoord_*_of_diff` rules
- `dCoord_commute_for_g_all` (Clairaut)

**Algebra**:
- All `sumIdx_*` lemmas (add, mul, collect, swap, congr, etc.)
- `group_sub_add`, `peel_mixed`, etc.

### ❌ AVOID (would create circularity)

- Anything using `∇g = 0` (nabla_g_zero, nabla_nabla_g_zero)
- Any Riemann symmetry (R_bacd = -R_abcd) - these are downstream corollaries
- `regroup_*_to_Riemann*` lemmas if they assume ∇g = 0

---

## Recommended Implementation Order

**JP's recommendation**:

### 1. Implement `commutator_structure` first ✅
- Short (~15-20 lines)
- De-risks the shape for the big lemma
- No differentiability hypotheses

### 2. Stub the four sub-lemmas for `algebraic_identity` ✅
```lean
private lemma expand_PCaCb_to_main_plus_payload ... := by sorry
private lemma payload_cancel_a ... := by sorry
private lemma payload_cancel_b ... := by sorry
private lemma mixed_partials_cancel_in_P ... := by sorry
private lemma regroup_main_to_Riemann ... := by sorry
```

**Then** fill them incrementally (keeps surface lemma small and readable)

### 3. Assemble `algebraic_identity` using sub-lemmas ✅
```lean
lemma algebraic_identity ... := by
  calc P_terms + C_terms_a + C_terms_b
    _ = [expanded with payloads] := expand_PCaCb_to_main_plus_payload ...
    _ = [a-payload cancelled]    := payload_cancel_a ...
    _ = [b-payload cancelled]    := payload_cancel_b ...
    _ = [mixed partials gone]    := mixed_partials_cancel_in_P ...
    _ = -R_baμν - R_abμν         := regroup_main_to_Riemann ...
```

### 4. Specialize `ricci_identity_on_g_rθ_ext` ✅
- One-line call to general theorem
- Keep h_θ for θ-derivative paths

---

## Pitfalls & Tactical Tips

### 1. Bound Your Rewrites
✅ **Prefer**: `simp only [nabla_g, ...]`
✅ **Use**: Flatten helpers (flatten₄₁, flatten₄₂, group_*)
❌ **Avoid**: Global `simp` with bidirectional pairs (mul_sumIdx ↔ sumIdx_mul)

**Reason**: Prevents infinite loops from bidirectional lemmas

---

### 2. Variable Hygiene
When cancelling payloads against C_a/C_b:
```lean
-- Use sumIdx_congr to rename dummy index
apply sumIdx_congr
intro ρ
-- Then one ring line finishes it
ring
```

---

### 3. Collector Choice
**Two-branch collector**: Can replace a lot of hand reshaping for μ↔ν commutator
**Single-branch with_extras**: Also fine if you prefer to do a and b separately

**Pattern**: `sumIdx_collect_comm_block_with_extras` + explicit subtraction

---

### 4. Discharge Differentiability
Use existing `discharge_diff` tactic for DifferentiableAt_* side conditions

**Pattern**:
```lean
have hF_r : ∀ k, DifferentiableAt_r (...) ∨ μ ≠ μ := by
  intro k; left
  exact (DifferentiableAt.mul
    (differentiableAt_Γtot_all_r M r θ h_ext k ν a)
    (differentiableAt_g_all_r M r θ h_ext k b))
```

---

## Exact G/A/B/C/D/P/Q Mapping (for B2 - Payload Cancellation)

### For a-branch:

```lean
let G  : Idx → ℝ := fun ρ => g M ρ b r θ
let A  : Idx → ℝ := fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν a) r θ
let B  : Idx → ℝ := fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ a) r θ
let C  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ μ lam * Γtot M r θ lam ν a)
let D  : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ ν lam * Γtot M r θ lam μ a)
let P  : Idx → ℝ := fun ρ => Γtot M r θ ρ ν a * dCoord μ (fun r θ => g M ρ b r θ) r θ
let Q  : Idx → ℝ := fun ρ => Γtot M r θ ρ μ a * dCoord ν (fun r θ => g M ρ b r θ) r θ
```

### For b-branch (swap a ↔ b):

```lean
let Gb : Idx → ℝ := fun ρ => g M a ρ r θ
let Ab : Idx → ℝ := fun ρ => dCoord μ (fun r θ => Γtot M r θ ρ ν b) r θ
let Bb : Idx → ℝ := fun ρ => dCoord ν (fun r θ => Γtot M r θ ρ μ b) r θ
let Cb : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ μ lam * Γtot M r θ lam ν b)
let Db : Idx → ℝ := fun ρ => sumIdx (fun lam => Γtot M r θ ρ ν lam * Γtot M r θ lam μ b)
let Pb : Idx → ℝ := fun ρ => Γtot M r θ ρ ν b * dCoord μ (fun r θ => g M a ρ r θ) r θ
let Qb : Idx → ℝ := fun ρ => Γtot M r θ ρ μ b * dCoord ν (fun r θ => g M a ρ r θ) r θ
```

**Apply**: `sumIdx_collect_comm_block_with_extras G A B C D P Q`

**Result**: Payload ∑(P-Q) cancels with C_a contribution (and similarly for b-branch vs C_b)

---

## JP's Offer

> "If you want, I can draft the four sub-lemma statements (B1–B4) in Lean-style prose you can paste as stubs next to algebraic_identity so everything drops neatly into place when you start filling them."

**Status**: ✅ ACCEPTED - Proceeding with creating sub-lemma stubs

---

## Summary

**What we have**:
- ✅ Mathematically sound strategy (SP verified)
- ✅ All required infrastructure in codebase
- ✅ Concrete implementation recipe (JP provided)
- ✅ Exact collector mappings for key cancellation
- ✅ Safety audit (safe vs. unsafe lemmas)

**What to do**:
1. Fix lemma name: `Γtot_symm` → `Γtot_symmetry`
2. Adjust domain hypotheses (remove h_ext from commutator_structure if not needed)
3. Implement commutator_structure (~15-20 lines)
4. Create 4 sub-lemma stubs for algebraic_identity
5. Fill sub-lemmas incrementally
6. Assemble via calc chain

**Estimated total effort**:
- commutator_structure: 1-2 hours
- Sub-lemma stubs: 30 minutes
- B1 (expansion): 2-3 hours
- B2 (payload cancellation): 3-4 hours (the key step)
- B3 (mixed partials): 1 hour
- B4 (regroup to Riemann): 2-3 hours
- **Total**: 10-15 hours of focused work

---

**Date**: October 23, 2025
**Status**: Ready to implement - All guidance received
**Next**: Create sub-lemma stubs and start with commutator_structure
