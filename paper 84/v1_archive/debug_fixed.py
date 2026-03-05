#!/usr/bin/env python3
"""
Fixed Gauss-Manin computation.

Identity: nabla_t(omega_k) = A(x)/y dx  where
  N(x) = 2*(A+h')*f - h*f'
  i.e., A = B - h'  where B = (A+h') satisfies  h*f' - 2*B*f = -N.

The original Bezout method (v2) computes A = (1/2)*x^{k+5}*a + d/dx(x^{k+5}*b).
The Griffiths method needs A = B - h' where N = 2*B*f - h*f'.

Both methods also need COHOMOLOGICAL REDUCTION of A to deg < 2g.
"""
import sympy as sp
from sympy import Rational as Q, Poly, cancel, expand, degree
import sys

x, t = sp.symbols('x t')

def compute_GM(f_poly, g, label, verbose=False):
    DOMAIN = sp.QQ.frac_field(t)
    n = 2 * g
    f = f_poly
    df_dx = sp.diff(f, x)
    df_dt = sp.diff(f, t)

    fp_poly = Poly(df_dx, x, domain=DOMAIN)
    lc_fp = fp_poly.nth(n)

    def reduce_mod_cohom(p_expr):
        p = Poly(expand(p_expr), x, domain=DOMAIN)
        for _ in range(200):
            d = sp.degree(p, x)
            if d < n:
                break
            lc = p.nth(d)
            sub = sp.Integer(0)
            for j in range(n):
                cj = fp_poly.nth(j)
                if cj != 0:
                    sub += cj * x**(d - n + j)
            sub = lc * (-1/lc_fp) * sub
            p = Poly(expand(p.as_expr() - lc * x**d + sub), x, domain=DOMAIN)
        return [cancel(p.as_expr().coeff(x, j)) for j in range(n)]

    # Bezout: a*f + b*f' = 1
    f_px = Poly(f, x, domain=DOMAIN)
    a_raw, b_raw, gcd_p = sp.gcdex(f_px, fp_poly)
    ge = gcd_p.as_expr()
    a_bez = cancel(a_raw.as_expr() / ge)
    b_bez = cancel(b_raw.as_expr() / ge)
    assert cancel(expand(a_bez * f + b_bez * df_dx)) == 1

    M = [[sp.Integer(0)]*n for _ in range(n)]
    neg_ft = expand(-df_dt)

    for k in range(n):
        # A(x) = (1/2)*neg_ft*x^k*a(x) + d/dx(neg_ft*x^k*b(x))
        num_poly = expand(neg_ft * x**k)
        term1 = expand(num_poly * a_bez) / 2
        P = expand(num_poly * b_bez)
        term2 = expand(sp.diff(P, x))
        A_total = expand(term1 + term2)
        coeffs = reduce_mod_cohom(A_total)
        for j in range(n):
            M[j][k] = coeffs[j]

    tr = cancel(sum(M[k][k] for k in range(n)))
    return M, tr

def report(label, f_poly, g):
    M, tr = compute_GM(f_poly, g, label)
    n = 2*g
    print(f"\n{label}:")
    print(f"  tr(M) = {tr}  {'PASS' if tr == 0 else 'FAIL'}")

    # Regularity of trace
    if tr != 0:
        nd = sp.degree(Poly(sp.numer(tr), t))
        dd = sp.degree(Poly(sp.denom(tr), t))
        print(f"  tr regularity: deg(num)={nd}, deg(den)={dd} {'regular' if nd < dd else 'IRREGULAR'}")

    # For genus 4: eigenspace traces
    if g == 4:
        even = [0,2,4,6]
        tau_p = cancel(sum(M[even[i]][even[i]] for i in range(4)))
        print(f"  tau_+(t) = {tau_p}")
        if tau_p != 0:
            pf = sp.apart(tau_p, t)
            print(f"  apart = {pf}")
            r2 = cancel(sp.limit(tau_p*(t-2), t, 2))
            rm2 = cancel(sp.limit(tau_p*(t+2), t, -2))
            print(f"  Residues: at +2: {r2}, at -2: {rm2}")

    # Genus 1 known answers
    if g == 1 and "x^3 - t*x" in label:
        print(f"  M[0][0] = {M[0][0]}  (expected: 1/(4t))")
        print(f"  M[1][1] = {M[1][1]}  (expected: -1/(4t))")
    if g == 1 and "Legendre" in label:
        print(f"  M[0][0] = {M[0][0]}  (expected: 1/(2-2t))")
        print(f"  M[0][1] = {M[0][1]}  (expected: -1/(2t-2t^2))")
        print(f"  M[1][0] = {M[1][0]}  (expected: 1/(2-2t))")
        print(f"  M[1][1] = {M[1][1]}  (expected: -1/(2-2t))")

    return M

# Tests
report("y^2 = x^3 - t*x", x**3 - t*x, 1)
report("Legendre y^2 = x(x-1)(x-t)", expand(x*(x-1)*(x-t)), 1)
report("Genus 2: y^2 = x^5 - t*x^3 + x", x**5 - t*x**3 + x, 2)
M4 = report("Genus 4: y^2 = x^9 - t*x^5 + x", x**9 - t*x**5 + x, 4)
