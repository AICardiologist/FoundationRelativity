# Paper 80 — Proof Instruction

## Working Title

**The Parameterized CRMLint Squeeze: Algebraic Gauss-Manin Connections over Function Fields**

---

## The Millennium Gap: From Points to Moduli Spaces

The CRMLint Squeeze Trilogy (Papers 77--79) operates on isolated, rigid objects over Q:

- **Paper 77:** Exact integers refuting the E^4 hallucination.
- **Paper 78:** Exact cyclotomic traces for a single local Galois representation.
- **Paper 79:** Exact integer Gram matrix (8I_2) for a fixed Weil fourfold.

The engine is currently a 0-dimensional point solver. Everything reduces to static numbers; Lean 4 verifies via compiled `native_decide`.

The Millennium Prizes are universal structural theorems about **moduli spaces**:

- **BSD Rank >= 2 cycle:** Higher Heegner cycles are parameterized over the continuous function field of X_0(N). Cannot look at one isolated curve.
- **Hodge Conjecture falsification:** Cannot test one isolated variety. A classical mathematician replies: "Your polynomial search bound D was too low; the cycle exists at degree D+1." Must construct the cycle class matrix across a parameterized family, compute the algebraic Gauss-Manin connection, calculate the monodromy group, and prove that the continuous Hodge deformation diverges from the algebraic cycle lattice at all degrees.

**Mandatory upgrade:** CRMLint Squeeze from exact arithmetic (Q) to function field algebra (Q(t)).

---

## Part 1: The Metamathematical Pivot (From `native_decide` to `ring`)

**The Cliff (CLASS):** When a variety deforms along parameter t, its cohomology deforms. Human mathematicians use Ehresmann's fibration theorem, the topological Gauss-Manin connection, and analytic continuation of period integrals over C. CRMLint flags this as heavily CLASS: uncountable limits, non-algebraic transcendental functions, continuous topology.

**The Forest (BISH):** Grothendieck and Dwork proved the differential equation governing cohomology is fundamentally algebraic. Computable entirely via the **Griffiths Pole Reduction Algorithm** in algebraic de Rham cohomology over Q[t].

**The Lean Upgrade:** Cannot use `native_decide` — Lean's compiled kernel cannot natively evaluate a symbolic variable t. Python emits formal polynomial identities; Lean 4 verifies them using `ring` and `linear_combination` tactics.

---

## Part 2: Lean/Python Engineering Specification

### Task 1: `solve_gauss_manin.py` (SymPy Polynomial Offloading)

1. **Setup:** Define t and x as `sympy.Symbols`. Work over Q(t).
2. **Target Family:** Legendre family of elliptic curves y^2 = x(x-1)(x-t).
3. **Algebraic de Rham Cohomology:** Basis of H^1_dR(X_t) spanned by:
   - omega = dx/y
   - eta = x dx/y
4. **Gauss-Manin Connection:** Differentiate forms w.r.t. t. Use algebraic pole reduction (adding exact forms df) to express nabla_{d/dt} omega and nabla_{d/dt} eta as Q(t)-linear combinations of omega and eta.
5. **Picard-Fuchs Equation:** Extract the 2nd-order linear differential operator L that annihilates omega. Expected result: L = t(1-t) d^2/dt^2 + (1-2t) d/dt - 1/4.
6. **Emitter (`P80_GaussManin/GMData.lean`):** Emit coefficients as formal Lean 4 `Polynomial Q` or `RatFunc Q` definitions. Emit the exact polynomial identities proving the reduction.

### Task 2: Lean Verification Architecture (`Paper80_Moduli.lean`)

1. **Classical Boundary Node (CLASS):** Analytic period isomorphism and flat continuation over C.
2. **Constructive Target (BISH):** Purely algebraic statement: L omega ≡ 0 (mod df).
3. **Proof method:** `ring` tactic to computationally verify the formal polynomial expansion emitted by Python. No `native_decide`, no `sorry`, no axiom in the constructive path.

---

## Part 3: Writing Specification

### Narrative Arc

Frame Paper 80 as the mandatory prerequisite for resolving universal moduli problems. Papers 77--79 de-omniscientized specific algebraic varieties (points in moduli space) using compiled rational arithmetic (`native_decide`).

To tackle Millennium conjectures regarding families of varieties, the Squeeze must operate over Q(t). Paper 80 physically bypasses transcendental analytic continuation by calculating the exact algebraic Gauss-Manin connection over Q(t), pushing verification into Lean 4 via purely syntactic polynomial equality (`ring`).

**Conclusion:** The CRM pipeline is now capable of performing automated, exact algebraic geometry over varying moduli spaces.

---

## How Paper 80 Unlocks the Millennium Strike (Paper 81+)

### The Wall Without Paper 80

Attempting the Hodge counterexample now: Lean asks you to prove a polynomial matrix has no solutions. Constructively, you need Python to compute the Grobner basis or exact functional determinant over Q(t), and Lean to verify that polynomial identity using `ring`. Paper 80 forces the bridge from polynomial algebra in Python into Lean 4.

### The Hodge Counterexample Protocol (Paper 81)

Once the function-field bridge is secure:

1. Target a highly rigid, pathological Calabi-Yau family or twisted abelian family over t.
2. Compute the formal cycle class matrix M(t) over Q(t) via the algebraic Gauss-Manin connection.
3. Python calculates the formal algebraic monodromy group; proves it acts irreducibly on the Hodge class.
4. Prove the polynomial determinant of the augmented system is non-zero in Q[t] — guaranteeing no rational function solution exists anywhere on the moduli space.
5. Emit this determinant calculation to Lean 4, prove non-zero using `ring`.
6. Result: 100% formal, machine-checked proof that the exotic Hodge class is fundamentally non-algebraic.

**Build the collider before you smash the particles.**
