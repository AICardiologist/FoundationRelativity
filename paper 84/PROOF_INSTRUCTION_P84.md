# Paper 84 — The Exotic Trace Probe: Moving Weil Classes via Gauss-Manin

## Working Title
The Gauss-Manin Trace of the Exotic Weil Subspace: A 1-Dimensional Probe
(Paper 84, Constructive Reverse Mathematics Series)

## The Target
Compute the Gauss-Manin connection on the exotic Weil subspace of a 1-parameter
genus-4 hyperelliptic family with Q(i)-action. Use the trace trick to collapse the
70-dimensional exterior power computation into a 1-dimensional scalar ODE, then
determine the differential Galois group of the exotic classes.

---

## Part 0: Lessons from Paper 79 (Token Overflow Prevention)

### Critical Engineering Rules

1. **Print nothing large.** Python scripts must NOT print matrices, connection
   entries, or intermediate polynomials to stdout. Only print scalar summaries
   (dimensions, trace value, Galois group type). All data goes to disk.

2. **Offload everything to Python.** The chatbot writes the script, executes it,
   reads the 1-line summary. No autoregressively generating 8x8 matrices in chat.

3. **Timeout protocol.** If `solve_exotic_trace.py` runs >5 minutes, STOP.
   Do not retry. Consult with Math AI for a structural shortcut. The Griffiths
   reduction for genus 4 is heavier than genus 1 (degree 9 vs degree 3).

4. **Iterate.** Paper 79 pivoted 3 times (E^4 -> Q(zeta_15) sweep -> Generic Weil).
   Paper 84 may need similar pivots. The proof document records each attempt.

---

## Part 1: The Mathematical Setup

### The Family
Genus-4 hyperelliptic curve with Q(i)-action:
```
C_t : y^2 = f(x,t) = x^9 - t*x^5 + x
```
Automorphism: (x, y) -> (-x, i*y), where i = sqrt(-1).
This gives a Q(i)-action on the Jacobian J(C_t), making it a Weil abelian fourfold.

### The Cohomology
- H^1(C_t) is 8-dimensional (genus 4).
- Basis for H^1_dR: {x^k dx/y : k = 0, 1, ..., 7}.
- The Q(i)-action splits H^1 into eigenspaces:
  - V_+ (eigenvalue +i): spanned by even-index basis elements {x^0, x^2, x^4, x^6} dx/y
  - V_- (eigenvalue -i): spanned by odd-index basis elements {x^1, x^3, x^5, x^7} dx/y
  - Each is 4-dimensional.

### The Dimensional Collapse (The Trace Trick)
The exotic Weil subspace W_K in wedge^4(H^1) decomposes over K = Q(i) as:
```
W_K = wedge^4(V_+) + wedge^4(V_-)
```
Since dim(V_+) = 4, wedge^4(V_+) is 1-dimensional.
Therefore the Gauss-Manin connection on wedge^4(V_+) is a 1x1 scalar ODE:
```
nabla_t(omega) = tau(t) * omega
```
where tau(t) = Tr(M_+(t)), the trace of the 4x4 Gauss-Manin connection
restricted to V_+.

**This is the key bypass:** instead of computing a 70x70 exterior connection,
we compute an 8x8 connection, extract the 4x4 V_+ block, and take its trace.

### Expected Outcome (to be verified, NOT assumed)
Math AI predicts tau(t) = -1/(4t). If true:
- Flat section: t^{1/4} (algebraic, degree 4 over Q(t))
- Differential Galois group: mu_4 (finite cyclic of order 4)
- Under base change t = s^4: exotic class becomes rational flat section
- Geometric meaning: moving exotic algebraic cycle exists on pulled-back family

**CRITICAL:** Do NOT hardcode -1/(4t). Run the CAS, inspect the actual output.

---

## Part 2: The CRM Squeeze Structure

### Classical Boundary Node (CLASS)
Resolving exotic algebraic cycles classically requires:
- Hodge Conjecture (open in general!)
- Comparison theorem (de Rham <-> Betti, requires topology over C)
- Baire category arguments for "very general" fibers

### Constructive Bridge (BISH)
The function-field pipeline computes:
1. The 8x8 Gauss-Manin connection M(t) on H^1(C_t) by Griffiths reduction
2. The 4x4 restriction M_+(t) to the V_+ eigenspace
3. The trace tau(t) = Tr(M_+(t))
4. The differential Galois group of the 1D equation y' = tau(t)*y

All steps are polynomial/rational arithmetic over Q(t). No topology.

---

## Part 3: Python Execution Plan

### Task 1: `solve_exotic_trace.py`

The script must:

1. **Define the curve.** f(x,t) = x^9 - t*x^5 + x over Q(t)[x].

2. **Compute the 8x8 Gauss-Manin connection.**
   For each basis element omega_k = x^k dx/y (k=0..7), compute:
   ```
   nabla_t(omega_k) = d/dt(omega_k) = partial_t(1/y) * x^k dx
                     = (-1/(2y)) * partial_t(f)/f * x^k dx    [WRONG]
   ```
   Actually: nabla_t(x^k dx/y) is computed by Griffiths pole reduction.
   The derivative d/dt introduces a pole (x^k * x^5)/(2*y^3) dx that must
   be reduced back to the H^1 basis {x^j dx/y : j=0..7} using the relation
   ```
   d(x^m / y) = (m*x^{m-1}*y - x^m * f'(x)/(2y)) / y^2 dx = exact form
   ```
   The Griffiths reduction for hyperelliptic curves of genus g uses:
   - y^2 = f(x), so y^3 = y * f(x)
   - Reduction: (polynomial in x)/y^3 = (polynomial in x)/(y * f(x))
     Then partial fraction / polynomial division to get degree < 2g = 8.
   - Exact differentials to further reduce.

   **WARNING:** This is the hard computational step. Genus 4 means the
   reduction involves degree-9 polynomials. May be slow.

3. **Extract V_+ block.** The even-index rows/columns {0,2,4,6} of M(t).

4. **Compute trace.** tau(t) = M[0,0] + M[2,2] + M[4,4] + M[6,6].

5. **Emit minimal output.** Print ONLY:
   ```
   Trace tau(t) = <rational function>
   Galois type = <finite/SL2/other>
   ```
   Write full data to `TraceData.lean`.

### Griffiths Reduction Algorithm (Detailed)

For the hyperelliptic curve y^2 = f(x) with deg(f) = 2g+1 = 9:

**Step A: The derivative.**
```
nabla_t(x^k dx/y) = -x^{k+5}/(2y^3) dx    [since partial_t f = -x^5]
```

**Step B: Reduce 1/y^3 to 1/y.**
Use the identity y^2 = f(x), so:
```
x^{k+5} / y^3 = x^{k+5} / (y * f(x))
```
Now perform polynomial division of x^{k+5} by f(x) = x^9 - tx^5 + x:
```
x^{k+5} = q(x) * f(x) + r(x)    where deg(r) < 9
```
Then x^{k+5}/y^3 = q(x)/y + r(x)/(y*f(x)).

The q(x)/y part is already in H^1 form (if deg(q) < 8; reduce further if not).
The r(x)/(y*f(x)) part requires exact differential subtraction.

**Step C: Exact differential reduction.**
Use: d(x^m/y) = [m*x^{m-1}/y - x^m*f'(x)/(2*y^3)] dx
This gives a relation between x^m/y^3 dx and x^{m-1}/y dx forms.

The Bezout approach (Math AI's suggestion): find a, b such that a*f + b*f' = 1,
then use this to systematically reduce pole orders. But gcd(f, f') may not be 1
at special fibers. Over Q(t) as a field, gcd(f, f') = 1 generically (the
discriminant is nonzero as a polynomial in t).

**FALLBACK:** If Griffiths reduction is too slow for genus 4, try:
- Direct ODE approach: the Picard-Fuchs equation for C_t
- Compute M(t) column by column, using SymPy's polynomial division
- Reduce computation time by exploiting the Q(i)-symmetry from the start
  (only compute the 4x4 V_+ block directly)

### Timeout Contingency

If the full 8x8 computation exceeds 5 minutes:

**Shortcut A:** Exploit symmetry. The automorphism (x,y)->(-x,iy) acts on the
basis as omega_k -> (-1)^k * i * omega_k. So M(t) is block-diagonal in the
even/odd splitting. Compute only the 4x4 even block directly.

**Shortcut B:** Use the Picard-Fuchs equation directly. For the family
y^2 = x^9 - tx^5 + x, the periods satisfy a 4th-order ODE (genus 4).
The trace of the connection on V_+ equals the coefficient of the
(g-1)th derivative in the Picard-Fuchs operator.

**Shortcut C:** Consult Math AI for a different family where the computation
is lighter (e.g., lower genus with exotic classes).

---

## Part 4: Lean Architecture

### If tau(t) = -1/(4t) (or similar rational function with finite monodromy)

```lean
-- TraceData.lean (CAS-emitted)
def exotic_trace_num : Int := -1
def exotic_trace_den_coeff : Int := 4  -- tau(t) = num / (den_coeff * t)

-- Paper84_ExoticTrace.lean
-- CLASS boundary: exotic cycle existence via Hodge Conjecture
axiom exotic_cycle_existence (family : HyperellipticFamily) :
  exists exotic_cycle, is_algebraic exotic_cycle

-- BISH bridge: the trace computation determines the Galois group
-- The flat section of y' = tau(t)*y is t^{-num/den_coeff} = t^{1/4}
-- Differential Galois group = mu_4 (finite, order 4)
-- Under t = s^4: the flat section is rational
theorem trace_determines_galois : exotic_trace_num = -1 := by rfl
theorem denominator_is_four : exotic_trace_den_coeff = 4 := by rfl
-- ... etc (full squeeze theorem after CAS output is known)
```

### If tau(t) has infinite monodromy (SL_2 or similar)

Then the exotic class does NOT become algebraic under any finite base change.
This would be a NEGATIVE result: the function-field pipeline detects that
the exotic Weil class is transcendental (not algebraic) over Q(t).
Still interesting for CRM: the pipeline gives a finite certificate of
non-algebraicity, resolving the degree trap for exotic classes.

---

## Part 5: LaTeX Outline

1. Introduction: the frontier (Ancona, Voisin, Engel-Fortman-Schreieder),
   the dimensional bypass, the trace trick
2. The hyperelliptic family and its Q(i)-action
3. The Griffiths-Bezout reduction (8x8 connection computation)
4. The eigenspace splitting and trace extraction
5. The differential Galois group of the exotic subspace
6. The Squeeze (CLASS -> BISH)
7. CRM Audit
8. Formal Verification
9. Discussion (what the trace tells us about exotic cycles)
10. Conclusion

---

## Part 6: Iteration Log

### Attempt 1: 2026-02-27 (first version)
- Script: solve_exotic_trace.py (v1)
- Curve: y^2 = x^9 - tx^5 + x
- Result: FAILED — `AttributeError: 'Poly' object has no attribute 'expand'`
- Issue: `gcdex` returns Poly objects, code expected expressions

### Attempt 2: 2026-02-27 (clean rewrite)
- Script: solve_exotic_trace.py (v2, ~150 lines, no dead code)
- Curve: y^2 = x^9 - tx^5 + x
- Runtime: 0.5 seconds
- Result: **NEGATIVE RESULT — G_gal = Gm (transcendental)**
- Symmetry check: PASSED (M is block-diagonal in even/odd)
- tau_+(t) = (-250t^5 + 1890t^3 - 3564t)/(81t^2 - 324)
- tau_-(t) = (10/9) * tau_+(t)
- Both have polynomial parts (irregular singularity at infinity)
- Flat section: C * exp(P(t)) * (t^2-4)^{2/81} — transcendental
- Math AI prediction (tau = -1/(4t)) was **WRONG**
- Poles at t = ±2 (degeneration of curve: x^8 - tx^4 + 1 has double root)
- Residues at poles: -2/81 (V_+), -20/729 (V_-)

### Interpretation
The exotic Weil classes in wedge^4(V_±) are transcendental over Q(t).
No finite base change can make them algebraic. The polynomial part of
the integral (degree 4 in t) ensures exp(polynomial) is transcendental.
This is the NEGATIVE branch of the proof instruction (Part 4, §2):
the function-field pipeline gives a FINITE CERTIFICATE of non-algebraicity.

---

## Key References
- Ancona, Huber, Lehalleur (2024): On the motive of Weil restriction
- Voisin (2024): On the Hodge conjecture for Weil abelian fourfolds
- Engel, Fortman, Schreieder (2025): exotic classes on abelian fourfolds
- Kovacic (1986): algorithm for 2nd order linear ODE
- van der Put, Singer (2003): Galois Theory of Linear Differential Equations
- Papers 80-83 (Lee 2026): function-field pipeline
