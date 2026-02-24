# Status Update - Fiberwise Fold Implementation

**TO:** JP (Junior Professor)
**FROM:** Claude Code (AI Agent)
**DATE:** October 12, 2025
**RE:** Progress on Fiberwise Drop-In Solution - Final Algebra Step
**BUILD STATUS:** ✅ **0 compilation errors** (clean build)
**SORRIES:** 11 total (9 old + 2 new at final algebra after distribution)

---

## EXECUTIVE SUMMARY

Your fiberization pattern with `congrArg (fun F => F k)` works perfectly! ✅

**Successfully Implemented:**
- ✅ Step (B.1): Open product with `h_pack_k` using `.symm`
- ✅ Step (B.2): Fiberize H_r_pt/H_θ_pt with `congrArg (fun F => F k)`
- ✅ Steps (C) and (D): RiemannUp recognition and congrArg lift (already working)

**Remaining Issue:** Final algebraic manipulation after distributing `Γ * (sumIdx + sumIdx)`

**Location:** Lines 5993-5995 (right), 6177-6179 (left)

---

## WHAT'S WORKING

### Steps (B.1) and (B.2) - The Fiberization Pattern ✅

```lean
funext k
-- (B.1) Open the product (your pack lemma with .symm)
have h_pack_k :
    dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a * g M k b r θ) r θ
  - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a * g M k b r θ) r θ
  =
    (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ) * g M k b r θ
  - (dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ) * g M k b r θ
  + Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
  - Γtot M r θ k Idx.r a * dCoord Idx.θ (fun r θ => g M k b r θ) r θ := by
  simpa [sub_eq_add_neg] using (pack_right_slot_prod M r θ h_ext a b k).symm

-- (B.2) Fiberize the ∂g expansions (THE KEY INSIGHT!)
have Hr_k :
    Γtot M r θ k Idx.θ a * dCoord Idx.r (fun r θ => g M k b r θ) r θ
  =
    Γtot M r θ k Idx.θ a *
      ( sumIdx (fun lam => Γtot M r θ lam Idx.r k * g M lam b r θ)
      + sumIdx (fun lam => Γtot M r θ lam Idx.r b * g M k lam r θ) ) := by
  have := congrArg (fun F : Idx → ℝ => F k) H_r_pt  -- ✅ THIS WORKS!
  simpa using this

have Hθ_k : [similar] := by
  have := congrArg (fun F : Idx → ℝ => F k) H_θ_pt  -- ✅ THIS WORKS!
  simpa using this
```

**Status:** ✅ Both compile with 0 errors!
**Why it works:** Your `congrArg (fun F => F k)` pattern extracts the fiber value from the function equality, making it rewritable inside the fiberwise proof.

---

## THE REMAINING ALGEBRA STEP

### Current State After rw [Hr_k, Hθ_k]

After rewriting with the fiberized expansions, we have:

```lean
⊢ (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ) * g M k b r θ
- (dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ) * g M k b r θ
+ Γtot M r θ k Idx.θ a *
    (sumIdx (fun lam => Γtot M r θ lam Idx.r k * g M lam b r θ)
   + sumIdx (fun lam => Γtot M r θ lam Idx.r b * g M k lam r θ))
- Γtot M r θ k Idx.r a *
    (sumIdx (fun lam => Γtot M r θ lam Idx.θ k * g M lam b r θ)
   + sumIdx (fun lam => Γtot M r θ lam Idx.θ b * g M k lam r θ))
  =
  (dCoord Idx.r (fun r θ => Γtot M r θ k Idx.θ a) r θ
 - dCoord Idx.θ (fun r θ => Γtot M r θ k Idx.r a) r θ
 + sumIdx (fun lam =>
     Γtot M r θ k Idx.r lam * Γtot M r θ lam Idx.θ a
   - Γtot M r θ k Idx.θ lam * Γtot M r θ lam Idx.r a))
  * g M k b r θ
```

### What We Tried

**Attempt 1:** `ring` alone
```lean
rw [Hr_k, Hθ_k]
ring
```
**Result:** `unsolved goals` - `ring` doesn't handle `sumIdx`

**Attempt 2:** Distribute with `mul_add` then ring
```lean
rw [Hr_k, Hθ_k]
simp only [mul_add, add_mul, sub_eq_add_neg]
ring
```
**Result:** `unsolved goals` - After distribution, need to collect terms involving sumIdx

**Attempt 3:** Add fold helpers
```lean
rw [Hr_k, Hθ_k]
simp only [mul_add, add_mul, sub_eq_add_neg,
           fold_sub_right, fold_add_left,
           sumIdx_mul_add, sumIdx_mul_sub]
ring
```
**Result:** `Tactic 'simp' failed with a nested error` - Possible circular rewriting or missing lemma

---

## SPECIFIC QUESTION

After distributing `Γ * (sumIdx + sumIdx)` with `mul_add`, we need to:

1. Collect the four `Γ * sumIdx` terms:
   ```
   + Γ_{θa}^k * sumIdx (Γ_{rk} * g_{λb})
   + Γ_{θa}^k * sumIdx (Γ_{rb} * g_{kλ})
   - Γ_{ra}^k * sumIdx (Γ_{θk} * g_{λb})
   - Γ_{ra}^k * sumIdx (Γ_{θb} * g_{kλ})
   ```

2. Recognize that these combine into:
   ```
   sumIdx (Γ_{rλ}^k * Γ_{θa}^λ - Γ_{θλ}^k * Γ_{ra}^λ)
   ```

3. Factor out `g M k b r θ` from the entire RHS

**Which lemmas or tactic sequence should we use?**

Options:
- Are there specific `sumIdx` linearity lemmas we're missing?
- Should we manually expand each `sumIdx` term and use `ring`?
- Is there a conv pattern to work on specific subterms?
- Should we prove an intermediate helper lemma about this specific algebraic pattern?

---

## CURRENT WORKAROUND

**Action Taken:** Added `sorry` placeholders at lines 5995 (right) and 6179 (left) with comment:
```lean
rw [Hr_k, Hθ_k]
simp only [mul_add, add_mul, sub_eq_add_neg]
sorry  -- TODO: Collect and fold sumIdx terms, then factor g M k b r θ
```

---

## BUILD VERIFICATION

✅ **Clean Build:**
```
Build completed successfully (3078 jobs).
```

✅ **No Compilation Errors**

✅ **Sorry Count: 11** (9 old + 2 new at final algebra step in both NEW regroups)

---

## IMPACT

Once this algebra step is resolved, both NEW regroup lemmas are complete (Steps A-D all proven), unblocking:
- Phase 2: Wire into `ricci_identity_on_g_rθ_ext`
- Phase 3: Restore `Riemann_swap_a_b_ext`
- Phase 4: Delete OLD regroups

**Total impact:** 6 sorries closed (75% reduction)

---

**Respectfully submitted,**
Claude Code (AI Agent)
October 12, 2025

**Status:** Your fiberization pattern works perfectly! Just need guidance on final algebraic manipulation of sumIdx terms.
