# Consultation Request: Mathematical Verification of Corrected Riemann Computation
## To: Senior Professor (Mathematics)
## From: quantmann (via Claude Code)
## Date: October 19, 2025
## Subject: Verify corrected metric compatibility expansion in Schwarzschild coordinates

---

## BACKGROUND

We are formally verifying the computation of the Riemann curvature tensor in Schwarzschild coordinates using the Lean 4 proof assistant.

**Context**: This is part of Paper 5 in the FoundationRelativity project, which formalizes General Relativity in a constructive type theory framework.

**Previous issue**: We discovered a mathematical error in our metric compatibility expansion where extra terms were being incorrectly omitted.

**Current status**: We have corrected the mathematics and implemented the fix, but need verification that our corrected formulas are mathematically sound.

---

## THE MATHEMATICAL QUESTION

We are computing the Riemann tensor component R^a_{brθ} via the standard formula involving derivatives of Christoffel symbols and their products.

### Setting

**Spacetime**: Schwarzschild metric in (t, r, θ, φ) coordinates
**Restriction**: We work only in the (r, θ) 2-dimensional submanifold
**Metric**:
```
g_rr = (1 - 2M/r)^(-1)
g_θθ = r²
g_rθ = 0  (off-diagonal)
```

**Christoffel symbols**: Γ^a_{bc} computed from the metric in the standard way

**Lowered Christoffel**: Γ_abc := Σ_ρ g_aρ Γ^ρ_{bc} (we call this Γ₁)

### The Computation

We compute:
```
∂_r(Γ_a,θb) - ∂_θ(Γ_a,rb) + [Γ·Γ product terms]
```

where Γ_a,θb = Σ_ρ g_aρ Γ^ρ_{θb} is the lowered Christoffel symbol.

### The Key Expansion

When we expand ∂_r(Σ_ρ g_aρ Γ^ρ_{θb}) using the product rule:

```
∂_r(Σ_ρ g_aρ Γ^ρ_{θb}) = Σ_ρ g_aρ (∂_r Γ^ρ_{θb}) + Σ_ρ (∂_r g_aρ) Γ^ρ_{θb}
```

The second term Σ_ρ (∂_r g_aρ) Γ^ρ_{θb} can be expanded using **metric compatibility** ∇g = 0.

---

## METRIC COMPATIBILITY FORMULA

From ∇_μ g_ab = 0 (covariant derivative of metric vanishes), we have:

```
∂_μ g_ab = Σ_ρ Γ^ρ_{μa} g_ρb + Σ_ρ Γ^ρ_{μb} g_aρ
```

In our case (μ = r, a = a, b = ρ):

```
∂_r g_aρ = Σ_σ Γ^σ_{ra} g_σρ + Σ_σ Γ^σ_{rρ} g_aσ
```

---

## THE CORRECTION

### What We Had (WRONG)

**Old formula** for Σ_ρ (∂_r g_aρ) Γ^ρ_{θb}:
```
Σ_ρ (∂_r g_aρ) Γ^ρ_{θb} = Σ_{ρ,σ} g_aσ Γ^σ_{rρ} Γ^ρ_{θb}
```

This only includes ONE of the two terms from metric compatibility!

### What We Have Now (CORRECT)

**New formula** for Σ_ρ (∂_r g_aρ) Γ^ρ_{θb}:
```
Σ_ρ (∂_r g_aρ) Γ^ρ_{θb}
  = Σ_{ρ,σ} g_aσ Γ^σ_{rρ} Γ^ρ_{θb}     [this is M_r, the "main" term]
  + Σ_σ Γ^σ_{ra} Γ_σ,θb                 [this is Extra_r, the "extra" term]
```

where Γ_σ,θb = Σ_ρ g_σρ Γ^ρ_{θb} is the lowered Christoffel.

Similarly for the θ-derivative:
```
Σ_ρ (∂_θ g_aρ) Γ^ρ_{rb}
  = Σ_{ρ,σ} g_aσ Γ^σ_{θρ} Γ^ρ_{rb}     [M_θ]
  + Σ_σ Γ^σ_{θa} Γ_σ,rb                 [Extra_θ]
```

---

## MATHEMATICAL VERIFICATION NEEDED

### Question 1: Correct Expansion?

Is the following algebraic expansion correct?

**Starting from**:
```
Σ_ρ (∂_r g_aρ) Γ^ρ_{θb}
```

**Using** ∂_r g_aρ = Σ_σ Γ^σ_{ra} g_σρ + Σ_σ Γ^σ_{rρ} g_aσ:
```
Σ_ρ (∂_r g_aρ) Γ^ρ_{θb}
  = Σ_ρ [(Σ_σ Γ^σ_{ra} g_σρ) + (Σ_σ Γ^σ_{rρ} g_aσ)] Γ^ρ_{θb}
  = Σ_{ρ,σ} Γ^σ_{ra} g_σρ Γ^ρ_{θb} + Σ_{ρ,σ} Γ^σ_{rρ} g_aσ Γ^ρ_{θb}
  = Σ_σ Γ^σ_{ra} (Σ_ρ g_σρ Γ^ρ_{θb}) + Σ_σ g_aσ (Σ_ρ Γ^σ_{rρ} Γ^ρ_{θb})
  = Σ_σ Γ^σ_{ra} Γ_σ,θb + Σ_{ρ,σ} g_aσ Γ^σ_{rρ} Γ^ρ_{θb}
```

**This gives**:
- Extra_r = Σ_σ Γ^σ_{ra} Γ_σ,θb
- M_r = Σ_{ρ,σ} g_aσ Γ^σ_{rρ} Γ^ρ_{θb}

**Question**: Is this algebraically correct?

### Question 2: Final Riemann Formula

After all cancellations and regroupings, we get:

```
[LHS of Ricci identity] = g_aa R^a_{brθ} + (Extra_r - Extra_θ)
```

where:
```
Extra_r - Extra_θ = Σ_σ Γ^σ_{ra} Γ_σ,θb - Σ_σ Γ^σ_{θa} Γ_σ,rb
```

**Question**: Does this formula make geometric sense?

**Intuition**: The extra terms involve Γ^σ_{μa} where μ is the derivative direction and a is the "slot" index. These terms should vanish in coordinate systems where g_ab is constant, but in Schwarzschild coordinates the metric components vary with r and θ.

### Question 3: Why Did We Miss This?

The standard textbook formula for Riemann tensor is usually written in a form where these extra terms are already incorporated or simplified away.

**Question**: In what coordinate systems or under what assumptions do these extra terms vanish?

**Our hypothesis**: They vanish when:
1. Diagonal metric (g_ab = 0 for a ≠ b), AND
2. The metric components don't vary in the orthogonal directions

But in Schwarzschild, g_rr varies with r and g_θθ varies with r, so the extra terms don't vanish.

---

## FORMAL PROOF STATUS

### What's Working

1. **Corrected Cancel Lemmas**: We have formally proven:
   ```lean
   lemma Cancel_r_expanded :
     Σ_ρ (∂_r g_aρ) Γ^ρ_{θb} = M_r + Extra_r

   lemma Cancel_θ_expanded :
     Σ_ρ (∂_θ g_aρ) Γ^ρ_{rb} = M_θ + Extra_θ
   ```
   These compile cleanly in Lean 4.

2. **Main Lemma Goal**: Corrected to:
   ```lean
   lemma regroup_left_sum_to_RiemannUp :
     [LHS] = g_aa · R^a_{brθ} + (Extra_r - Extra_θ)
   ```

3. **Product Rule Expansion**: The step that expands ∂_r(Σ g·Γ) is proven using:
   ```lean
   prod_rule_backwards_sum : Σ_ρ g·∂Γ = ∂(Σ g·Γ) - Σ (∂g)·Γ
   ```

### What's Blocked

The final calc chain that composes all steps isn't closing the goal due to a tactical issue (not a mathematical one). We're consulting JP (Junior Professor) on the Lean tactics separately.

---

## SPECIFIC VERIFICATION REQUEST

Could you please verify:

1. **Algebraic correctness**: Is our expansion of Σ_ρ (∂_μ g_aρ) Γ^ρ_{νb} using metric compatibility correct? (See Question 1)

2. **Geometric interpretation**: Do the "extra terms" (Extra_r - Extra_θ) make geometric sense in the context of the Riemann tensor computation?

3. **Coordinate-dependent behavior**: Under what conditions (if any) should these extra terms vanish?

4. **Textbook comparison**: Standard GR textbooks don't show these terms explicitly. Why not? Are they:
   a) Always zero in the coordinate systems textbooks use?
   b) Absorbed into other terms in the standard derivation?
   c) Present but written in a different form?

---

## ATTACHED DERIVATIONS

### Detailed Expansion (r-branch)

**Start**: ∂_r(Γ_a,θb) where Γ_a,θb = Σ_ρ g_aρ Γ^ρ_{θb}

**Step 1** - Product rule:
```
∂_r(Σ_ρ g_aρ Γ^ρ_{θb}) = Σ_ρ g_aρ (∂_r Γ^ρ_{θb}) + Σ_ρ (∂_r g_aρ) Γ^ρ_{θb}
```

**Step 2** - Expand ∂_r g_aρ using metric compatibility:
```
∂_r g_aρ = Σ_σ Γ^σ_{ra} g_σρ + Σ_σ Γ^σ_{rρ} g_aσ
```

**Step 3** - Substitute:
```
Σ_ρ (∂_r g_aρ) Γ^ρ_{θb}
  = Σ_ρ [Σ_σ Γ^σ_{ra} g_σρ + Σ_σ Γ^σ_{rρ} g_aσ] Γ^ρ_{θb}
```

**Step 4** - Distribute Γ^ρ_{θb}:
```
  = Σ_{ρ,σ} Γ^σ_{ra} g_σρ Γ^ρ_{θb} + Σ_{ρ,σ} Γ^σ_{rρ} g_aσ Γ^ρ_{θb}
```

**Step 5** - Factor (Fubini for finite sums):
```
  = Σ_σ Γ^σ_{ra} [Σ_ρ g_σρ Γ^ρ_{θb}] + Σ_σ g_aσ [Σ_ρ Γ^σ_{rρ} Γ^ρ_{θb}]
     └─────────────────────┬─────────────────────┘   └──────────────┬──────────────┘
              = Γ_σ,θb                                      = (Σ Γ·Γ term)
```

**Step 6** - Recognize lowered Christoffel:
```
  = Σ_σ Γ^σ_{ra} Γ_σ,θb + Σ_{ρ,σ} g_aσ Γ^σ_{rρ} Γ^ρ_{θb}
    └──────┬──────┘       └──────────┬─────────────┘
    Extra_r              M_r
```

---

## SUMMARY

We believe we have corrected a mathematical error in our formalization where extra terms from metric compatibility were being omitted.

The corrected formulas now include these "Extra" terms explicitly in the final Riemann tensor computation.

We need verification that:
1. Our algebra is correct
2. The extra terms make geometric sense
3. Our understanding of when they vanish is correct

This is urgent because we have a formal proof that is 99% complete but blocked on tactical issues. Once we confirm the mathematics is sound, we can focus purely on the Lean tactics to finish the proof.

---

**Thank you for your time and expertise!**

**Files available**:
- Main proof file: `Papers/P5_GeneralRelativity/GR/Riemann.lean`
- Cancel lemma proofs: Lines 2634-2917
- Main lemma: Lines 4320-4804
- Status reports: `STATUS_*.md` files in same directory

**Contact**: quantmann via GitHub issues at https://github.com/AICardiologist/FoundationRelativity

---

**Prepared by**: Claude Code on behalf of quantmann
**Date**: October 19, 2025
**Priority**: High - proof completion blocked pending verification
