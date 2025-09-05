/-
Paper 6 — Axiom ledger.
Collects all axioms used in P6 in one place with short docstrings.
-/
import Papers.P6_Heisenberg.Axioms.Complex
import Papers.P6_Heisenberg.HUP.DComega

/-! # Axioms used in Paper 6: Heisenberg Uncertainty Principle AxCal Analysis

This file centralizes all axiomatized content used in Paper 6 for verification transparency.

## Complex & Real number signatures (Prop-only)
From `Papers.P6_Heisenberg.Axioms.Complex`:

* `ℝ, ℂ : Type` - Real and complex number types
* `real_add, real_mul, complex_add, complex_mul` - Basic arithmetic operations (signature only)
* `complex_conj, complex_norm_sq` - Conjugation and squared norm
* `real_to_complex` - Real embedding into complex numbers
* `complex_i` - Imaginary unit
* Algebraic properties: associativity, commutativity, distributivity (all Prop-only)
* Conjugation properties: `complex_conj_add, complex_conj_mul, complex_conj_conj`
* Norm properties: non-negativity and conjugation relation
* Imaginary unit: `complex_i_sq : i² = -1`
* Real embedding preservation: addition and multiplication

## Dependent Choice (DCω) eliminator
From `Papers.P6_Heisenberg.HUP.DComega`:

* `Foundation : Type` - Foundation type for AxCal framework compatibility
* `HasDCω F : Prop` - DCω capability token for foundation F
* `SerialRel α` - Serial relation structure (every node has successor)
* `dcω_stream` - **KEY AXIOM**: DCω builds infinite sequences along serial relations
  ```lean
  axiom dcω_stream {F : Foundation} [HasDCω F] {α : Type} 
    (S : SerialRel α) (a0 : α) : 
    ∃ f : Nat → α, f 0 = a0 ∧ ∀ n, S.R (f n) (f (n+1))
  ```

## Hilbert space signatures (Prop-only)
From `Papers.P6_Heisenberg.HUP.HilbertSig`:

* `HilbertSig` - Vector space operations, inner product, norm (signatures only)
* `OperatorSig` - Observable operators with expectation and variance
* Properties: inner product linearity, conjugate symmetry, positive definiteness
* Observable expectation and variance definitions
* Canonical commutation relation (signature only)

## Future axioms (to be added)

* `rs_comm_im` - Commutator expectation is purely imaginary for self-adjoint operators
* `absC_im_domination` - Complex absolute value dominates imaginary part: |z| ≥ |Im z|
* Cauchy-Schwarz inequality over the Hilbert signature

## Verification Status

* ✅ All axioms are Prop-only (no instances to avoid code generation)
* ✅ Library target only (no executables)  
* ✅ Mathlib-free implementation
* ✅ Sorry-free verification passes
* 📋 Full AxCal height analysis: HUP-RS at Height 0, HUP-M ≤ DCω

-/