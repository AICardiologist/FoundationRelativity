# Paper 86 — Proof Instruction

## Title
**The Hodge Conjecture for Exotic Weil Classes via Kani-Rosen Splitting**
Paper 86 of the Constructive Reverse Mathematics Series

## One-Sentence Summary
The exotic Weil class on J(C_t)^2 for C_t: y^2 = x^9 - tx^5 + x is algebraic because a hidden reciprocal involution forces the Jacobian to split into a product of abelian surfaces, reducing the Hodge conjecture to the invariant theory of GSp_4.

---

## Theorem Statements

**Theorem A (Kani-Rosen Splitting).**
The genus-4 hyperelliptic curve C_t: y^2 = x^9 - tx^5 + x admits an involution mu(x,y) = (1/x, y/x^5) satisfying sigma*mu = mu*sigma^3, generating a D_8 action. The Jacobian splits up to isogeny:

    J(C_t) ~ J(Q_1) x J(Q_2)

where Q_1: w^2 = (u+2)(u^4 - 4u^2 + 2 - t) and Q_2: v^2 = (u-2)(u^4 - 4u^2 + 2 - t) are genus-2 curves with u = x + 1/x.

**Theorem B (Quotient Isomorphism).**
Over C, the map (u, v) -> (-u, iv) gives Q_1 ~ Q_2. Therefore J(C_t) ~ A^2 where A = J(Q_1) is an abelian surface.

**Theorem C (Hodge Conjecture).**
For generic t, the exotic Weil class omega in wedge^4(V_+) on J(C_t)^2 is algebraic.

**CRM Audit.** The Kani-Rosen splitting, the quotient curve computation, and the D_8 group verification are all BISH. The Hodge conclusion appeals to three classical theorems (Kani-Rosen, Moonen-Zarhin, Zarhin MT group), making the overall logical cost CLASS. But the *obstruction* to algebraicity is removed by a BISH computation. Ninth CRMLint Squeeze.

---

## Proof Architecture

### Layer 1: The Reciprocal Involution (CAS + Lean, fully formal)

**Claim 1.1.** mu(x,y) = (1/x, y/x^5) is an automorphism of C_t.
- *Proof:* (y/x^5)^2 = y^2/x^10 = (x^9 - tx^5 + x)/x^10 = 1/x - t/x^5 + 1/x^9 = f(1/x, t). Polynomial identity, verified by `ring`.
- *Lean:* Define f(x,t) = x^9 - t*x^5 + x, prove f(1/x, t) = f(x, t)/x^10.

**Claim 1.2.** mu^2 = id.
- *Proof:* mu(mu(x,y)) = mu(1/x, y/x^5) = (x, (y/x^5)*x^5) = (x, y).

**Claim 1.3.** sigma*mu = mu*sigma^3, establishing D_8 = <sigma, mu>.
- *Proof:* Direct computation on coordinates. Verified by CAS, formalize by `ring`.

### Layer 2: Quotient Curve Equations (CAS + Lean)

**Claim 2.1.** The mu-invariant coordinate is u = x + 1/x.

**Claim 2.2.** The key factorizations:
- u^5 - 5u^3 + 5u + 2 = (u + 2)(u^2 - u - 1)^2
- u^5 - 5u^3 + 5u - 2 = (u - 2)(u^2 + u - 1)^2
- *Lean:* Polynomial identities, verified by `ring`.

**Claim 2.3.** Quotient curves:
- C_t/<mu>: w^2 = (u + 2)(u^4 - 4u^2 + 2 - t), genus 2.
- C_t/<mu*sigma^2>: v^2 = (u - 2)(u^4 - 4u^2 + 2 - t), genus 2.
- *Derivation:* w = y(x^5+1)/x^5 is mu-invariant, w^2 = (T_4 - t)(T_5 + 2) where T_k = x^k + 1/x^k. Absorb perfect square (u^2 - u - 1)^2.

**Claim 2.4.** The map (u, v) -> (-u, iv) sends Q_2 to Q_1 over C.
- Q_2 at -u: v^2 = (-u-2)(u^4 - 4u^2 + 2 - t) = -(u+2)(u^4 - 4u^2 + 2 - t).
- Absorb sign: (iv)^2 = -v^2 = (u+2)(u^4 - 4u^2 + 2 - t) = Q_1.
- Therefore J(Q_1) ~ J(Q_2) over C, and J(C_t) ~ A^2 where A = J(Q_1).

### Layer 3: Differential Decomposition (CAS + Lean)

**Claim 3.1.** On H^0(Omega^1) with basis omega_k = x^k dx/(2y), k = 0,...,3:
- mu* acts by omega_k -> -omega_{3-k}
- sigma* acts by omega_k -> i*(-1)^k * omega_k

**Claim 3.2.** Eigenspace decomposition:
- V_+ (eigenvalue i of sigma*): span{omega_0, omega_2}
- V_- (eigenvalue -i of sigma*): span{omega_1, omega_3}

**Claim 3.3.** Kani-Rosen decomposition:
- mu*-invariant (from A_1 = J(Q_1)): span{omega_0 - omega_3, omega_1 - omega_2}
- mu*-anti-invariant (from A_2 = J(Q_2)): span{omega_0 + omega_3, omega_1 + omega_2}

**Claim 3.4.** V_+ cuts diagonally:
- omega_0 = (1/2)(omega_0 - omega_3) + (1/2)(omega_0 + omega_3)
- omega_2 = -(1/2)(omega_1 - omega_2) + (1/2)(omega_1 + omega_2)
- Each basis element of V_+ has one component from H^1(A_1) and one from H^1(A_2).
- *Lean:* Matrix computation, verified by `simp` / `decide`.

### Layer 4: Hodge Conjecture (Literature citations, not formalized)

**Step 4.1.** Kani-Rosen Theorem (1989): For a curve C with a group G acting, the Jacobian decomposes up to isogeny according to the rational representations of G. For D_8 on a genus-4 curve with the splitting verified in Layer 3, J(C_t) ~ J(Q_1) x J(Q_2).
- *Reference:* E. Kani and M. Rosen, "Idempotent relations and factors of Jacobians," Math. Ann. 284 (1989), 307-327.

**Step 4.2.** Generic endomorphism ring: For generic t (transcendental), End(J(Q_1)) = Z. This follows from the fact that the locus of genus-2 curves with extra endomorphisms has codimension >= 1 in the moduli space M_2, so a 1-parameter family generically avoids it.
- *Verification option:* Compute the Picard-Fuchs equation of Q_1 and show its differential Galois group is Sp_4 (the maximal possible). This would confirm MT(J(Q_1)) = GSp_4.
- *Alternative:* Specialize to a numeric t (e.g., t = 1) and compute End(J(Q_1)) numerically, verifying it's Z.

**Step 4.3.** Mumford-Tate group: If End(A) = Z for abelian surface A, then MT(A) = GSp_4.
- *Reference:* Yu. G. Zarhin, "Hodge groups of K3 surfaces," J. Reine Angew. Math. 341 (1983), 193-220.
- More directly: B. Moonen and Yu. G. Zarhin, "Hodge classes on abelian varieties of low dimension," Math. Ann. 315 (1999), 711-733.

**Step 4.4.** Invariant theory: All Hodge classes on A^n (for A abelian surface with End = Z, any n) are generated by the symplectic pairing (= divisor classes). This follows from the first fundamental theorem of invariant theory for the symplectic group Sp_{2g}: the invariants of Sp_{2g} acting on tensor powers of the standard representation are generated by the symplectic form.
- *Reference:* H. Weyl, "The Classical Groups," Princeton, 1939.
- *Consequence:* All Hodge classes on J(C_t)^2 ~ A^4 are algebraic.

**Step 4.5.** The exotic Weil class omega in wedge^4(V_+) is a Hodge class on J(C_t)^2 (established in Paper 84). By Step 4.4, it is algebraic.

---

## What Is New vs. What Is Cited

| Component | Status | Method |
|-----------|--------|--------|
| Reciprocal involution mu | NEW (this paper) | CAS + Lean |
| D_8 group relation | NEW (this paper) | CAS + Lean |
| Quotient curve equations | NEW (this paper) | CAS + Lean |
| Q_1 ~ Q_2 over C | NEW (this paper) | Algebraic |
| Differential decomposition | NEW (this paper) | CAS + Lean |
| Kani-Rosen splitting | CITED | Kani-Rosen 1989 |
| End(A) = Z generically | CITED/VERIFIED | Moduli theory / optional CAS |
| MT(A) = GSp_4 | CITED | Zarhin 1983 / Moonen-Zarhin 1999 |
| Invariant theory of Sp | CITED | Weyl 1939 |
| omega is algebraic | CONCLUDED | Combining above |

---

## Lean 4 Formalization Plan

### File: Paper86_KaniRosen.lean (~300-400 lines target)

```
-- 1. Define the curve and involutions
def p86_f (x t : Z[X]) := x^9 - t*x^5 + x   -- or over Z/Q(t)

-- 2. Verify mu is an automorphism
theorem p86_mu_auto : f(1/x, t) * x^10 = f(x, t)  -- polynomial identity

-- 3. Verify D_8 relation: encode sigma*mu = mu*sigma^3 on coordinates

-- 4. Key factorizations
theorem p86_factor_plus : u^5 - 5*u^3 + 5*u + 2 = (u + 2) * (u^2 - u - 1)^2
theorem p86_factor_minus : u^5 - 5*u^3 + 5*u - 2 = (u - 2) * (u^2 + u - 1)^2

-- 5. Genus computation: degree 5 polynomial -> genus 2
def p86_quotient1_degree : Nat := 5
def p86_quotient2_degree : Nat := 5
def p86_quotient1_genus : Nat := 2
def p86_quotient2_genus : Nat := 2

-- 6. Differential action matrices (4x4)
-- mu* matrix, sigma* eigenvalues, eigenspace dimensions

-- 7. The squeeze theorem
theorem p86_hodge_squeeze :
    p86_curve_genus = 4
    /\ p86_quotient1_genus = 2
    /\ p86_quotient2_genus = 2
    /\ p86_eigenspace_dim = 4   -- dim V_+
    /\ (factorization identities)
    /\ (D_8 relation)
```

### File: QuotientData.lean (CAS-emitted, ~150 lines)
- Chebyshev polynomial identities
- Factorization verifications
- Differential action matrix entries

---

## CRM Squeeze Structure

**Classical Boundary Node (CLASS):**
The Hodge conjecture for J(C_t)^2 — asserting that exotic Weil classes are algebraic — requires the Kani-Rosen theorem (topological/algebraic decomposition of Jacobians), Mumford-Tate group theory (transcendental methods), and invariant theory of the symplectic group. All CLASS infrastructure.

**Constructive Content (BISH):**
The *obstruction analysis* is entirely BISH:
- The involution mu and D_8 relation: polynomial identities (ring)
- Quotient curve equations: polynomial factorization (ring)
- Differential decomposition: matrix computation (decide)
- Genus computation: arithmetic (decide)

**Squeeze:** CLASS says "Hodge classes on abelian surfaces are algebraic." BISH says "this specific Jacobian is a product of abelian surfaces." The constructive content identifies the geometric structure; the classical content provides the Hodge-theoretic conclusion. CRM descent: not full BISH (the conclusion is CLASS), but the *discovery* and *verification* of the splitting is BISH.

---

## Dependency on Earlier Papers

- **Paper 84:** Established the exotic Weil class omega in wedge^4(V_+), proved it is a global flat section (tau_+ = 0) for y^2 = x^9 - tx^5 + x. Paper 86 proves this class is algebraic.
- **Paper 85:** Universal flatness across genera. Paper 86 resolves algebraicity for the specific Paper 84 family.
- **Paper 80:** Griffiths pole reduction over Q(t). Same CAS methodology.
- **Paper 83:** Generic Picard number via Kovacic. Same pattern: use differential Galois theory to certify genericity.

---

## Open Questions / Risks

1. **End(J(Q_1)) = Z generically.** High confidence but needs explicit verification. Options:
   (a) Compute Picard-Fuchs of Q_1 over Q(t), show G_gal = Sp_4 via Kovacic-style analysis.
   (b) Specialize to numeric t, compute endomorphism ring numerically.
   (c) Cite general position argument from moduli theory.
   Option (a) is strongest and fits the pipeline. Option (c) is quickest but weakest.

2. **Kani-Rosen theorem: precise statement needed.** The splitting J(C) ~ J(C/H_1) x J(C/H_2) holds up to isogeny when the group G acts and the idempotent decomposition of Q[G] matches the action on differentials. Our Layer 3 computation confirms this decomposition at the level of differentials. Need to cite the exact theorem from Kani-Rosen 1989.

3. **Weyl invariant theory: precise statement.** The first fundamental theorem for Sp_{2g} says the ring of polynomial invariants on V^{tensor n} is generated by contractions with the symplectic form. For the Hodge-theoretic application, we need: all Hodge classes on A^n (A with MT = GSp_{2g}) are linear combinations of products of polarization classes and graph classes of endomorphisms. For End(A) = Z, endomorphisms are trivial, so only polarization classes remain.

4. **The paper does NOT prove the Hodge conjecture for the Paper 85 family** (y^2 = x^9 + tx^7 + x). That family has no reciprocal involution and the Jacobian is generically simple. A separate strategy (CM specialization at t=0, Fermat domination) is needed — see the Math AI roadmap for Strategy 2. This could be Paper 87.

---

## Estimated Scope
- LaTeX: 15-18 pages
- Lean: 300-400 lines (0 sorry target)
- References: 20-25 (Kani-Rosen, Moonen-Zarhin, Zarhin, Weyl, Deligne, + series papers)
- Axiom inventory: ring, decide (BISH core); Classical.choice for any Mathlib abelian variety imports
- Timeline: 1-2 sessions for CAS + Lean, 1 session for LaTeX + pipeline
