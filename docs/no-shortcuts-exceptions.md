# No-Shortcuts Exceptions Guide

## Overview

The no-shortcuts linters are intentionally conservative and may occasionally flag legitimate very short proofs. This document explains how to handle such cases.

## When Exceptions Are Allowed

Exceptions are ONLY allowed for:
1. **Definitional equalities** that genuinely reduce to `rfl`
2. **Trivial propositions** that are actually trivial by design
3. **Elementary lemmas** in core mathematical libraries

## How to Request an Exception

### Method 1: Lint Comment (Preferred)
Add a comment directly above the declaration:
```lean
-- lint: allow_short_proof - This is definitionally equal
theorem my_def_eq : foo = bar := rfl
```

### Method 2: Exception List
For systematic exceptions, add to `scripts/lean/cheap_proofs_exceptions.json`:
```json
{
  "allowed_short_proofs": [
    {
      "name": "CategoryTheory.id_comp",
      "reason": "Category axiom - definitionally true"
    }
  ]
}
```

## Review Process

All exception requests must:
1. Be reviewed by a senior maintainer
2. Include clear justification
3. Be documented in PR description
4. Pass manual code review

## Examples

### ✅ Legitimate Short Proof
```lean
-- lint: allow_short_proof - Definitional equality from category axioms
theorem id_comp (f : X ⟶ Y) : 𝟙 X ≫ f = f := rfl
```

### ❌ Fake Short Proof (Not Allowed)
```lean
-- This would be rejected even with lint comment
structure BidualGap where dummy : Unit
theorem gap_exists : BidualGap := ⟨()⟩  -- Using Unit trick!
```

## Updating the Linter

To implement lint comment support, update `CheapProofs.lean`:
```lean
def hasAllowShortProofComment (env : Environment) (decl : Name) : IO Bool := do
  -- Implementation to check source comments
  -- This requires source location tracking
  sorry
```

## Important Notes

- Exceptions are rare and closely monitored
- The default stance remains "short == suspicious"
- When in doubt, write a fuller proof
- Never use exceptions to bypass real formalization