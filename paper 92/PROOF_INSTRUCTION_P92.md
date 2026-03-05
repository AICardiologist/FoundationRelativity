# System Directive: CRMLint Project "Higher Hodge" (Paper 92)

## 1. Context and Mission Objective

**The Mathematical Frontier:** Markman (2025) resolved the Hodge Conjecture for abelian fourfolds of Weil type using secant sheaves and hyper-Kahler geometry. However, his geometric machinery is dimensionally locked. The classical school is currently trapped trying to extend these sheaves to dimensions 6, 8, 10, and 12 because the analytic obstruction to sheaf deformation (the Atiyah class) is computationally impenetrable.

**The CRM Objective:** We will act as the "Computational Scout." By the Atiyah-Gauss-Manin correspondence, the infinitesimal topological obstruction to deforming an algebraic cycle vanishes globally if the trace of the Gauss-Manin connection vanishes (tau_+ = 0). We will use Asymmetric Offloading (Python CAS to Lean 4) to explicitly compute the Gauss-Manin connection and prove tau_+ = 0 universally for the hyperelliptic Weil families in Genera 5, 6, 7, and 8.

**Goal:** Generate a highly optimized Python/SymPy script that executes Griffiths pole reduction for g in {5, 6, 7, 8}, followed by the deterministic emission of a zero-sorry Lean 4 verification file proving global cohomological flatness.

---

## 2. Phase 1: The Python CAS Blueprint (higher_gauss_manin.py)

Write a SymPy script that performs the following symbolic pipeline. Loop over g in {5, 6, 7, 8}:

### A. Initialization and Universal Families

1. For a given genus g, initialize g-1 free symbolic parameters: a_1, a_2, ..., a_{g-1}.
2. Define the universal odd hyperelliptic polynomial of degree 2g+1:

       f_g(x) = x^{2g+1} + a_1 x^{2g-1} + a_2 x^{2g-3} + ... + a_{g-1} x^3 + x

3. Define the curve C_g: y^2 = f_g(x). Because f_g(x) is strictly odd, the curve admits the Q(i)-action sigma(x,y) = (-x, iy).

### B. Cohomology Basis and V_+ Projection

1. The algebraic de Rham cohomology H^1_dR(C_g) has a standard basis. The eigenspace V_+ (eigenvalue +i under sigma*) has dimension g.
2. Construct the V_+ basis forms: omega_k = x^{2k} dx / y for k = 0, ..., g-1.

### C. Griffiths Pole Reduction (The Differential Engine)

*Computational Constraint: To prevent memory exhaustion on Genus 8 (degree 17 polynomials over 7 variables), DO NOT compute the full 2g x 2g matrix. Project strictly onto V_+ and only track the trace components.*

1. For each parameter a_j (which corresponds to the term a_j x^{2g - 2j + 1}), compute the naive derivative of the basis forms omega_k in V_+ with respect to a_j. This introduces double poles at y=0:

       nabla_{d/da_j}(omega_k) = -(1/2) * (x^{2k} * x^{2g - 2j + 1}) / y^3 dx

2. Implement the Griffiths pole reduction algorithm: Repeatedly add exact differentials d(x^p / y) = (2p x^{p-1} f_g - x^p f'_g) / (2 y^3) dx to reduce the numerator degree until the pole order drops from y^3 back to y^1.

3. Express the reduced forms as linear combinations of the V_+ basis to find the diagonal entries of the g x g connection matrix M^{(j)}_+.

### D. Trace Extraction and Code Emission

1. Compute the trace for each parameter direction: tau^{(j)}_+ = Tr(M^{(j)}_+).
2. Extract the exact polynomial numerator of tau^{(j)}_+. The Python script must structurally assert that this numerator collapses algebraically to 0.
3. **Emit Lean 4 Code:** Auto-generate a file HigherHodge_Trace.lean containing the exact unsimplified polynomial trace expansions, exact-form coboundary witnesses, and the `by ring` proofs that the traces equal zero.

---

## 3. Phase 2: The Lean 4 Verification Blueprint (HigherHodge_Trace.lean)

The emitted Lean file must structure the formal verification as follows, strictly complying with Mathlib 4 conventions.

### A. Setup and Imports

```lean
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Basic

/-!
# CRM Paper 92: Universal Flatness for Higher-Dimensional Weil Classes

This file formally verifies that the Gauss-Manin connection trace tau_+
vanishes identically for universal hyperelliptic Weil families of
genus 5, 6, 7, and 8.

By the Atiyah-Gauss-Manin bridge, this computationally guarantees
unobstructed geometric deformation for secant sheaves in
dimensions 10, 12, 14, and 16.
-/
```

### B. The Higher Fermat Anchors

For each genus g, evaluate the family at the origin a_1 = ... = a_{g-1} = 0, yielding C_g(0): y^2 = x^{2g+1} + x. Generate a theorem verifying the explicit rational substitution pi(u,v) = (u^2/v^2, u/v^{2g+1}) that dominates C_g(0) by the Fermat curve F_{4g}: u^{4g} + v^{4g} = 1.

Example format (g=6):

```lean
theorem anchor_domination_g6 (u v : Z) (h : u^24 + v^24 = 1) :
    let x := u^2 * v^22  -- (clearing denominators)
    -- [CAS WILL INSERT SCALED POLYNOMIAL PULLBACK IDENTITY HERE]
    -- proving y^2 = x^13 + x under the Fermat constraint.
    True := trivial -- Replace with actual identity and `by ring`
```

### C. The Universal Trace Vanishing Theorems

For each genus g and each parameter a_j, the CAS must emit the exact expanded numerator of the connection matrix trace and prove it equals zero.

Example format (g=6, parameter a_1):

```lean
theorem trace_vanishing_g6_a1 (a1 a2 a3 a4 a5 x : Z) :
    -- [CAS WILL INSERT MASSIVE EXPANDED POLYNOMIAL COBOUNDARY RELATION HERE]
    0 = 0 := by ring
```

### D. The CRM Axiomatic Anatomy

At the bottom of the Lean file, define the irreducible classical boundary that isolates the BISH computational scout work from the CLASS abstract siege engine work.

```lean
/-- The CRM Squeeze Classification for Higher Dimensions -/
inductive CRMLevel | BISH | MP | LLPO | WLPO | LPO | CLASS
  deriving Repr, DecidableEq

-- 1. Shioda Anchor Axiom (CLASS)
axiom shioda_fermat_anchor (g : Nat) : CRMLevel
axiom shioda_is_class : shioda_fermat_anchor g = CRMLevel.CLASS

-- 2. The Atiyah-Gauss-Manin Bridge (CLASS)
-- "Global trace vanishing (BISH) computationally guarantees that the
--  topological obstruction to analytic sheaf deformation vanishes."
axiom atiyah_deformation_bridge (g : Nat) : CRMLevel
axiom atiyah_is_class : atiyah_deformation_bridge g = CRMLevel.CLASS

-- 3. Higher Secant Sheaf Existence (CLASS)
-- "Markman's abstract sheaf construction must be extended to higher
--  dimensions to complete the cycle."
axiom higher_secant_sheaf_existence (g : Nat) : CRMLevel
axiom secant_is_class : higher_secant_sheaf_existence g = CRMLevel.CLASS
```

---

## 4. Execution Constraints

1. **Zero Trust / Zero Sorry:** The Python CAS must not be trusted by Lean. The Python script must expand the polynomial arithmetic completely so that Lean's `ring` tactic is only doing canonical normalization. No `sorry` is permitted in the Lean proofs.

2. **Computational Scaling:** Genus 8 involves reducing polynomials of degree 17. The SymPy script must use efficient polynomial arithmetic (e.g., Poly domains over QQ) and factor out common denominators before stringifying to Lean to prevent tactic timeouts.

3. **Purity of Scope:** Do not attempt to construct the secant sheaves or algebraic cycles in the Lean code. The mathematical thesis of Paper 92 is that CRM provides the differential-algebraic mechanism (flatness), while classical geometry provides the abstract existence.

---

## 5. Execution Order

1. Write the Python SymPy script (higher_gauss_manin.py).
2. Test on g=5 and g=6 first to validate the Griffiths division algorithm.
3. Scale to g=7 and g=8.
4. Emit Lean 4 code.
5. `lake build` with zero sorry.
6. Write paper92.tex following CRM Series format guide.
