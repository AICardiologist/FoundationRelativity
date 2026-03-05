#!/usr/bin/env python3
"""
Minimal debug: y^2 = x^3 - t*x (genus 1)
Known answer: nabla_t(dx/y) = (1/(4t)) * dx/y - (1/(4t)) * x*dx/y
             nabla_t(x*dx/y) = (1/(4t)) * dx/y + (-1/(4t)) * x*dx/y
             => M = [[1/(4t), 1/(4t)], [-1/(4t), -1/(4t)]]
Wait, let me compute this from scratch.

For y^2 = f(x) = x^3 - tx:
  df/dt = -x
  nabla_t(omega_k) = -(df/dt)/(2y^3) * x^k dx = x^{k+1}/(2y^3) dx

For k=0: nabla_t(dx/y) = x/(2y^3) dx

METHOD: Griffiths reduction (no Bezout).
  x/(2y^3) = x/(2y*f) since y^3 = y*y^2 = y*f

  We want: x/(2y*f) = [some polynomial in x] / y + d(h(x)/y)

  Step 1: x = q * f'(x) + r where f'(x) = 3x^2 - t
    x = 0 * (3x^2 - t) + x  (since deg(x) < deg(f'))
    So q = 0, r = x
    This means x*f'/(2y^3) = 0 (the q part is 0)
    And we still have x/(2y^3) to handle.

Actually, let me use a completely different method: the residue/period approach.

For y^2 = x^3 - tx, the basis of H^1 is {omega_0 = dx/y, omega_1 = x*dx/y}.

The Gauss-Manin connection can be computed via:
  nabla_t(omega_k) = sum_j M[j][k] * omega_j

where the matrix M satisfies the ODE system for periods.

For the Legendre-type family y^2 = x^3 - tx, the Picard-Fuchs equation is:
  4t * Omega'' + 2 * Omega' = 0  (for Omega = integral of dx/y)

  Wait no, let me compute properly.

APPROACH: Direct computation using the universal formula for hyperelliptic
Gauss-Manin connections.

For y^2 = f(x,t) with f = x^3 - tx:
  nabla_t(omega_k) = projection of (-df/dt * x^k)/(2f) * dx/y
                    onto H^1, using the relation f'(x) * dx/y = 0.

The KEY is: nabla_t acts on the cohomology class [x^k dx/y].
The connection is:
  nabla_t([x^k dx/y]) = [(-df/dt * x^k)/(2f(x)) * dx/y]

But (-df/dt * x^k)/(2f(x)) is a RATIONAL FUNCTION of x, not a polynomial!
We need to decompose it into partial fractions and reduce.

Alternatively: (-df/dt * x^k) / (2f) = (-(-x) * x^k) / (2(x^3 - tx))
  = x^{k+1} / (2x(x^2 - t)) = x^k / (2(x^2 - t))

For k=0: 1/(2(x^2 - t)). This is a rational function of x.
For k=1: x/(2(x^2 - t)). Also rational.

Hmm, but the forms in H^1 are dx/y and x*dx/y where y = sqrt(f(x)).
1/(2(x^2-t)) * dx/y is NOT of the standard form. We need to express it
as a linear combination of omega_0 = dx/y and omega_1 = x*dx/y.

CORRECT METHOD:
The Gauss-Manin connection on H^1_dR of a hyperelliptic curve y^2 = f(x,t)
with parameter t is given by the Griffiths-Manin formula:

For omega_k = x^k dx/y:
  nabla_t(omega_k) = sum_j A[j][k] * omega_j

where A[j][k] are determined by:
  (-df/dt) * x^k = sum_j A[j][k] * x^j * 2 * f(x) + h_k'(x) * f(x) - (1/2) * h_k(x) * f'(x)

for some polynomials h_k(x) with deg(h_k) < 2g.

Wait, that's not right either. Let me go back to basics.

DERIVATION FROM FIRST PRINCIPLES:

The relative de Rham cohomology H^1_dR(C_t) has a Gauss-Manin connection.
For an affine hyperelliptic curve y^2 = f(x,t), the algebraic de Rham
cohomology is:

  H^1_dR = Omega^1 / dO  where Omega^1 = {P(x)/y dx : P polynomial}

and dO = {d(Q(x)/y) : Q polynomial} with:
  d(Q(x)/y) = [Q'(x)/y - Q(x)*f'(x)/(2y^3)] dx
             = [Q'(x)*f(x) - Q(x)*f'(x)/2] / (y*f(x)) * dx
             = [Q'(x)*f(x) - Q(x)*f'(x)/2] * dx / y^3

So in H^1 (mod exact forms):
  Q'(x)/y dx = Q(x)*f'(x)/(2y^3) dx  [exact form identity]

The Gauss-Manin derivative of omega_k = x^k dx/y:
  nabla_t(omega_k) = partial_t(x^k dx/y)
                    = x^k * partial_t(1/y) * dx
                    = x^k * (-f_t/(2y^3)) * dx        [where f_t = df/dt]
                    = -f_t * x^k / (2y^3) * dx

Now, -f_t * x^k is a polynomial in x. Call it N(x).
We need to express N(x)/(2y^3) * dx as a sum of omega_j modulo exact forms.

Using y^3 = y * f: N(x)/(2y^3) = N(x)/(2y*f(x))

So N(x)/(2y*f(x)) dx = [N(x)/(2f(x))] * dx/y

The rational function N(x)/(2f(x)) needs to be decomposed.

DECOMPOSITION:
Polynomial division: N(x) = Q(x) * f(x) + R(x) with deg(R) < deg(f)

Then: N(x)/(2f(x)) = Q(x)/2 + R(x)/(2f(x))

The Q(x)/2 part: Q(x)/2 * dx/y is a polynomial times dx/y. But we also
need to use the exact form identity to handle the remaining R(x)/(2f(x))
part... wait, R/(2f) * dx/y = R/(2y*f) * dx = R/(2y^3) * dx.

Hmm, this doesn't terminate. We need a different approach.

THE CORRECT APPROACH (Griffiths transversality):

Write N(x)/(2y^3) dx = [polynomial in x]/y dx + d(h(x)/y)

Expanding d(h(x)/y):
  d(h(x)/y) = [h'(x)/y - h(x)*f'(x)/(2y^3)] dx

So: N(x)/(2y^3) = [poly]/y + h'(x)/y - h(x)*f'(x)/(2y^3)

Multiply by 2y^3:
  N(x) = 2*[poly]*y^2 + 2*h'(x)*y^2 - h(x)*f'(x)
        = 2*[poly]*f(x) + 2*h'(x)*f(x) - h(x)*f'(x)

So we need to find a polynomial h(x) with deg(h) < 2g and
a polynomial P(x) with deg(P) < 2g such that:

  N(x) = 2*P(x)*f(x) + 2*h'(x)*f(x) - h(x)*f'(x)   ... (*)

where M[j][k] = [coefficient of x^j in P(x) + h'(x)]?

No wait. Let me redo. We have:
  N(x)/(2y^3) dx = P(x)/y dx + d(h(x)/y)
                  = P(x)/y dx + h'(x)/y dx - h(x)f'(x)/(2y^3) dx
                  = [P(x) + h'(x)]/y dx - h(x)f'(x)/(2y^3) dx

Rearranging:
  [N(x) + h(x)f'(x)] / (2y^3) dx = [P(x) + h'(x)] / y dx

Multiply both sides by 2y^3/dx:
  N(x) + h(x)*f'(x) = 2*[P(x) + h'(x)]*y^2 = 2*[P(x) + h'(x)]*f(x)

So: N(x) + h(x)*f'(x) = 2*[P(x) + h'(x)]*f(x)

Let S(x) = P(x) + h'(x) (the coefficients we want). Then:
  N(x) + h(x)*f'(x) = 2*S(x)*f(x)

  N(x) = 2*S(x)*f(x) - h(x)*f'(x)

This is one equation in two unknowns (S and h).
The constraint is: deg(S) < 2g and deg(h) < 2g.

Divide: N(x) = 2*S(x)*f(x) - h(x)*f'(x)

Since deg(f) = 2g+1 and deg(f') = 2g, and deg(S) < 2g, deg(h) < 2g:
  deg(2*S*f) < 2g + 2g+1 = 4g+1
  deg(h*f') < 2g + 2g = 4g

For our N(x) = -f_t * x^k which has degree ≤ k + deg(f_t),
we need deg(N) < 4g+1 for a solution to exist. This is always satisfied.

The equation N = 2Sf - hf' is a Bezout-type equation.
Rearranging: hf' - 2Sf = -N, i.e., h*f' + (-2S)*f = -N.

If gcd(f, f') = 1 (i.e., the discriminant is nonzero), then there exist
unique h, S with the degree constraints above.

THIS IS THE CORRECT FORMULATION.

Let me implement this and test.
"""

import sympy as sp
from sympy import Rational as Q, Poly, cancel, expand, degree

x, t = sp.symbols('x t')

def compute_GM_correct(f_poly, g, label):
    """Correct Gauss-Manin computation using the Griffiths method.

    For y^2 = f(x,t), nabla_t(omega_k) = S_k(x) * dx/y
    where S_k(x) is determined by:
      -f_t * x^k = 2*S_k(x)*f(x) - h_k(x)*f'(x)
    with deg(S_k), deg(h_k) < 2g.
    """
    print(f"\n{'='*70}")
    print(f"CORRECT METHOD: {label}")
    print(f"{'='*70}")

    DOMAIN = sp.QQ.frac_field(t)
    n = 2 * g
    f = f_poly
    df_dx = sp.diff(f, x)
    df_dt = sp.diff(f, t)

    print(f"  f = {f}")
    print(f"  f' = {df_dx}")
    print(f"  f_t = {df_dt}")

    M = [[sp.Integer(0)] * n for _ in range(n)]

    for k in range(n):
        N = expand(-df_dt * x**k)  # The numerator

        # Solve: h*f' - 2*S*f = -N, i.e., h*f' + (-2S)*f = -N
        # This is the extended Euclidean problem:
        # Find h, S with deg(h) < 2g, deg(S) < 2g such that
        #   h*f'(x) - 2*S*f(x) = -N(x)
        #
        # Equivalently: h*f' + u*f = -N where u = -2S
        # So: S = -u/2
        #
        # Use polynomial division / extended gcd.
        # Since gcd(f, f') divides disc(f), and we assume disc != 0,
        # gcd(f, f') = 1 (generically).

        # Method: use the extended gcd identity a*f + b*f' = 1
        # Then: h*f' + u*f = -N has solution h = -N*b, u = -N*a
        # But we need deg constraints. Use: if (h0, u0) is one solution,
        # then (h0 + c*f, u0 - c*f') is also a solution for any c.
        # Choose c to reduce degrees.

        f_px = Poly(f, x, domain=DOMAIN)
        fp_px = Poly(df_dx, x, domain=DOMAIN)
        N_px = Poly(-N, x, domain=DOMAIN)  # We want h*f' + u*f = -N, so RHS is -N

        # Extended gcd: a*f + b*f' = gcd
        a_raw, b_raw, gcd_p = sp.gcdex(f_px, fp_px)
        gcd_e = gcd_p.as_expr()

        # Particular solution of h*f' + u*f = -N:
        # From a*f + b*f' = gcd: (-N/gcd)*b * f' + (-N/gcd)*a * f = -N
        # So h0 = (-N/gcd)*b, u0 = (-N/gcd)*a

        # But we need to handle this properly via polynomial arithmetic
        # h0*f' + u0*f = -N
        # h0 = -N * b / gcd, u0 = -N * a / gcd

        N_poly = Poly(-N, x, domain=DOMAIN)  # This is -N(x)

        # Multiply: h0 = b * (-N) / gcd
        h0_expr = cancel(b_raw.as_expr() * (-N) / gcd_e)
        u0_expr = cancel(a_raw.as_expr() * (-N) / gcd_e)

        h0 = Poly(expand(h0_expr), x, domain=DOMAIN)
        u0 = Poly(expand(u0_expr), x, domain=DOMAIN)

        # Verify: h0*f' + u0*f = -N
        check = expand(h0.as_expr() * df_dx + u0.as_expr() * f + N)
        check_simplified = cancel(check)
        if check_simplified != 0:
            print(f"  WARNING: verification failed for k={k}: residual = {check_simplified}")

        # Reduce h0 mod f to get deg(h) < deg(f) = 2g+1
        # h = h0 - q*f, u = u0 + q*f'
        # We want deg(h) < 2g = deg(f')
        q_h, r_h = sp.div(h0, f_px)
        h_final = r_h
        u_final = Poly(expand(u0.as_expr() + q_h.as_expr() * df_dx), x, domain=DOMAIN)

        # Now deg(h_final) < deg(f) = 2g+1
        # But we want deg(h) < 2g. If deg(h_final) = 2g, reduce once more.
        # Actually, we want deg(h) < 2g and deg(S) < 2g where S = -u/2.
        # Since u_final might still be large, let's check:

        # Further reduce: if deg(h_final) >= 2g, subtract more copies of f
        # Wait, h is reduced mod f, so deg(h) < deg(f) = 2g+1.
        # This means deg(h) <= 2g, which is fine for the identity.

        # S = -u_final / 2
        S_expr = cancel(-u_final.as_expr() / 2)
        S_poly = Poly(expand(S_expr), x, domain=DOMAIN)
        h_expr = h_final.as_expr()

        # The connection matrix row is given by S(x) = sum_j M[j][k] x^j
        # But S might have degree >= 2g, in which case we reduce using
        # the cohomological relation f'(x) = 0, i.e., x^{2g} = ...

        # Actually, wait. S(x) should satisfy deg(S) < 2g because:
        # N = 2*S*f - h*f', with deg(N) = k + deg(f_t)
        # deg(2*S*f) = deg(S) + 2g+1
        # deg(h*f') <= 2g + 2g = 4g
        # For the equation to balance: deg(S) + 2g+1 must accommodate deg(N).
        # For k < 2g and deg(f_t) < 2g+1, deg(N) < 4g+1.
        # So deg(S) can be up to 2g-1 at most.

        # Actually, let's just reduce S modulo the cohomological relation
        S_coeffs = []
        S_reduced = S_poly.as_expr()

        # Use the cohomological relation to reduce if needed
        lc_fp = Poly(df_dx, x, domain=DOMAIN).nth(n)  # leading coeff of f'
        fp_poly_obj = Poly(df_dx, x, domain=DOMAIN)

        S_p = Poly(expand(S_reduced), x, domain=DOMAIN)
        for _ in range(50):
            d = sp.degree(S_p, x)
            if d < n:
                break
            lc = S_p.nth(d)
            # x^d = x^{d-n} * x^n, x^n = (-1/lc_fp) * (f' - lc_fp*x^n)
            sub = sp.Integer(0)
            for j in range(n):
                cj = fp_poly_obj.nth(j)
                if cj != 0:
                    sub += cj * x**(d - n + j)
            sub = lc * (-1/lc_fp) * sub
            S_p = Poly(expand(S_p.as_expr() - lc * x**d + sub), x, domain=DOMAIN)

        S_final = S_p.as_expr()
        for j in range(n):
            M[j][k] = cancel(S_final.coeff(x, j))

    # Print results
    print(f"\n  Connection matrix:")
    for i in range(n):
        for j in range(n):
            print(f"    M[{i}][{j}] = {M[i][j]}")

    tr = cancel(sum(M[k][k] for k in range(n)))
    print(f"\n  tr(M) = {tr}")
    print(f"  Symplectic trace: {'PASS' if tr == 0 else 'FAIL'}")

    return M

# Test on y^2 = x^3 - tx
f1 = x**3 - t*x
M1 = compute_GM_correct(f1, 1, "y^2 = x^3 - t*x (genus 1)")
print(f"\n  Expected: M[0][0] = 1/(4t), M[0][1] = 0")
print(f"  Expected: M[1][0] = 0, M[1][1] = -1/(4t)")
print(f"  (From Picard-Fuchs: t*Omega'' + (1/2)*Omega' = 0)")

# Test on Legendre y^2 = x(x-1)(x-t)
f2 = expand(x*(x-1)*(x-t))
M2 = compute_GM_correct(f2, 1, "y^2 = x(x-1)(x-t) (Legendre)")
print(f"\n  Expected: M = (1/(2t(1-t))) * [[t,-1],[t,-t]]")

# Test on genus 2
f3 = x**5 - t*x**3 + x
M3 = compute_GM_correct(f3, 2, "y^2 = x^5 - t*x^3 + x (genus 2)")

# Test on genus 4 (the actual target)
f4 = x**9 - t*x**5 + x
M4 = compute_GM_correct(f4, 4, "y^2 = x^9 - t*x^5 + x (genus 4)")

print(f"\n{'='*70}")
print("REGULARITY CHECK FOR GENUS 4")
print(f"{'='*70}")
for k in range(8):
    mk = cancel(M4[k][k])
    if mk != 0:
        nd = sp.degree(Poly(sp.numer(mk), t))
        dd = sp.degree(Poly(sp.denom(mk), t))
        print(f"  M[{k}][{k}]: deg_t(num)={nd}, deg_t(den)={dd}")

tr4 = cancel(sum(M4[k][k] for k in range(8)))
print(f"  tr = {tr4}")
if tr4 != 0:
    nd = sp.degree(Poly(sp.numer(tr4), t))
    dd = sp.degree(Poly(sp.denom(tr4), t))
    print(f"  deg_t(num)={nd}, deg_t(den)={dd}, regular={'YES' if nd < dd else 'NO'}")
else:
    print(f"  ZERO trace -- PASSED!")

# Partial fraction for genus 4
print(f"\n  Partial fraction of tau_+:")
even_idx = [0, 2, 4, 6]
tau_plus = cancel(sum(M4[even_idx[i]][even_idx[i]] for i in range(4)))
print(f"  tau_+(t) = {tau_plus}")
if tau_plus != 0:
    pf = sp.apart(tau_plus, t)
    print(f"  apart = {pf}")
    res_p2 = cancel(sp.limit(tau_plus * (t-2), t, 2))
    res_m2 = cancel(sp.limit(tau_plus * (t+2), t, -2))
    print(f"  Residue at t=+2: {res_p2}")
    print(f"  Residue at t=-2: {res_m2}")
