#!/usr/bin/env python3
"""
Debug the Gauss-Manin connection algorithm.

Strategy:
1. Test on the Legendre family y^2 = x(x-1)(x-t) (genus 1, known answer)
2. Test on a simpler genus-4 family
3. Identify where the algorithm breaks

The known Legendre answer (from Paper 80):
  M(t) = (1/(2t(1-t))) * [[t, -1], [t, -t]]
  tr(M) = 0

IMPORTANT: For y^2 = f(x) with deg(f) = 2g+1:
  The Gauss-Manin derivative of omega_k = x^k dx/y with respect to t is:
    nabla_t(omega_k) = (-1/(2y^3)) * (df/dt) * x^k dx
                     = -(df/dt) * x^k / (2y^3) dx

  For f = x^9 - t*x^5 + x:  df/dt = -x^5
  So nabla_t(omega_k) = x^{k+5}/(2y^3) dx  [sign is positive]

  For f = x^3 - t*x:  df/dt = -x
  So nabla_t(omega_k) = x^{k+1}/(2y^3) dx
"""

import sympy as sp
from sympy import Rational as Q, Poly, cancel, expand, degree

x, t = sp.symbols('x t')

def compute_GM_connection(f_poly, g, label):
    """Compute Gauss-Manin connection for y^2 = f(x,t).
    Returns the 2g x 2g matrix M(t)."""
    print(f"\n{'='*70}")
    print(f"Testing: {label}")
    print(f"  f(x,t) = {f_poly}")
    print(f"  genus = {g}")
    print(f"{'='*70}")

    DOMAIN = sp.QQ.frac_field(t)
    n = 2 * g  # dimension of H^1_dR

    f = f_poly
    df_dx = sp.diff(f, x)
    df_dt = sp.diff(f, t)

    print(f"  f'(x) = {df_dx}")
    print(f"  df/dt = {df_dt}")

    # Reduction relation: f'(x) dx/y = 0 in cohomology
    # f'(x) = leading_coeff * x^{2g} + lower terms
    # => x^{2g} = -(lower terms)/leading_coeff
    f_prime_poly = Poly(df_dx, x, domain=DOMAIN)
    lc_fprime = f_prime_poly.nth(n)  # coefficient of x^{2g} in f'
    print(f"  Leading coeff of f': {lc_fprime}")
    print(f"  deg(f') = {degree(f_prime_poly, x)}")

    def reduce_to_basis(p_expr):
        """Reduce polynomial to degree < 2g using f'(x) = 0 relation."""
        p = Poly(expand(p_expr), x, domain=DOMAIN)
        for _ in range(200):
            d = sp.degree(p, x)
            if d < n:
                break
            lc = p.nth(d)
            # x^d = x^{d-n} * x^n, and x^n = -(rest of f' / leading_coeff)
            # f'(x) = lc_fprime * x^n + sum_{j<n} c_j x^j
            # => x^n = (-1/lc_fprime) * sum_{j<n} c_j x^j
            sub_terms = sp.Integer(0)
            for j in range(n):
                cj = f_prime_poly.nth(j)
                if cj != 0:
                    sub_terms += cj * x**(d - n + j)
            sub = lc * (-1/lc_fprime) * sub_terms
            p = Poly(expand(p.as_expr() - lc * x**d + sub), x, domain=DOMAIN)
        result = p.as_expr()
        return [cancel(result.coeff(x, j)) for j in range(n)]

    # Bezout identity: a*f + b*f' = 1
    f_px = Poly(f, x, domain=DOMAIN)
    df_px = Poly(df_dx, x, domain=DOMAIN)

    s_raw, t_raw, gcd_poly = sp.gcdex(f_px, df_px)
    gcd_expr = gcd_poly.as_expr()

    a_bez = cancel(s_raw.as_expr() / gcd_expr)
    b_bez = cancel(t_raw.as_expr() / gcd_expr)

    check = cancel(expand(a_bez * f + b_bez * df_dx))
    assert check == 1, f"Bezout FAILED: {check}"
    print(f"  Bezout verified.")
    print(f"  deg(a) = {sp.degree(Poly(a_bez, x), x)}")
    print(f"  deg(b) = {sp.degree(Poly(b_bez, x), x)}")

    # Build connection matrix
    # nabla_t(omega_k) = -(df/dt) * x^k / (2*y^3) * dx
    #                   = -(df/dt) * x^k / (2*y*f) * dx
    # Using Bezout: 1/f = (a*f + b*f')/f = a + b*f'/f
    # So 1/(y*f) = a/y + b*f'/(y*f) = a/y + b*f'/y^3
    #
    # nabla_t(omega_k) = -(df/dt) * x^k * [a/(2y) + b*f'/(2y^3)] dx
    # Term 1: -(df/dt) * x^k * a / (2y) => polynomial * dx/y
    # Term 2: -(df/dt) * x^k * b * f' / (2y^3)
    #   Using d(x^m/y) identity: x^m*f'/(2y^3) = m*x^{m-1}/y
    #   So Term 2 = -(df/dt) * sum_m p_m * m * x^{m-1} / y
    #   where P(x) = x^k * b(x)  [NOTE: no df/dt factor here yet]
    #
    # Wait, let me be more careful. We have:
    #   nabla_t(omega_k) = -(df/dt) * x^k / (2y^3) dx
    #
    # Let neg_dfdt = -df/dt. For our family, -df/dt = x^5 (genus 4) or x (Legendre).
    # So the numerator polynomial is neg_dfdt * x^k.
    #
    # nabla_t(omega_k) = [neg_dfdt * x^k] / (2y^3) dx
    #                   = [neg_dfdt * x^k * a] / (2y) dx
    #                   + [neg_dfdt * x^k * b * f'] / (2y^3) dx

    neg_dfdt = expand(-df_dt)  # This is a polynomial in x
    print(f"  -df/dt = {neg_dfdt}")

    M = [[sp.Integer(0)]*n for _ in range(n)]

    for k in range(n):
        # The numerator polynomial for this column
        num_poly = expand(neg_dfdt * x**k)

        # Term 1: (1/2) * num_poly * a(x)
        term1 = expand(num_poly * a_bez) / 2

        # Term 2: (1/2) * num_poly * b(x) * f'(x) / y^3
        # P(x) = num_poly * b(x)
        P_expr = expand(num_poly * b_bez)
        P_poly = Poly(P_expr, x, domain=DOMAIN)

        term2 = sp.Integer(0)
        for monom, coeff in P_poly.as_dict().items():
            m = monom[0]
            if m >= 1:
                term2 += coeff * m * x**(m-1)
        term2 = expand(term2)

        total = expand(term1 + term2)
        coeffs = reduce_to_basis(total)

        for j in range(n):
            M[j][k] = coeffs[j]

    # Check symplectic trace
    tr = cancel(sum(M[k][k] for k in range(n)))
    print(f"\n  tr(M) = {tr}")
    print(f"  Symplectic trace: {'PASS' if tr == 0 else 'FAIL'}")

    # Check regularity of diagonal entries
    for k in range(n):
        mk = cancel(M[k][k])
        if mk != 0:
            num_d = sp.degree(Poly(sp.numer(mk), t))
            den_d = sp.degree(Poly(sp.denom(mk), t))
            print(f"  M[{k}][{k}]: deg_t(num)={num_d}, deg_t(den)={den_d}")

    # Check trace regularity
    if tr != 0:
        num_d = sp.degree(Poly(sp.numer(tr), t))
        den_d = sp.degree(Poly(sp.denom(tr), t))
        print(f"  tr: deg_t(num)={num_d}, deg_t(den)={den_d}, regular={'YES' if num_d < den_d else 'NO'}")

    return M

# ==========================================
# TEST 1: Legendre family y^2 = x(x-1)(x-t)
# Known answer: M = (1/(2t(1-t))) * [[t,-1],[t,-t]]
# ==========================================
f_legendre = x * (x - 1) * (x - t)  # = x^3 - (1+t)*x^2 + t*x
f_legendre = expand(f_legendre)
M_leg = compute_GM_connection(f_legendre, 1, "Legendre: y^2 = x(x-1)(x-t)")

# Known answer comparison
print("\n  Known M[0][0] = t/(2t(1-t)) = 1/(2(1-t))")
print(f"  Got    M[0][0] = {cancel(M_leg[0][0])}")
print(f"  Known M[0][1] = -1/(2t(1-t))")
print(f"  Got    M[0][1] = {cancel(M_leg[0][1])}")
print(f"  Known M[1][0] = t/(2t(1-t)) = 1/(2(1-t))")
print(f"  Got    M[1][0] = {cancel(M_leg[1][0])}")
print(f"  Known M[1][1] = -t/(2t(1-t)) = -1/(2(1-t))")
print(f"  Got    M[1][1] = {cancel(M_leg[1][1])}")

# ==========================================
# TEST 2: Simple genus-2 family y^2 = x^5 - t*x^3 + x
# Has the same structure as genus 4 but smaller
# ==========================================
f_g2 = x**5 - t * x**3 + x
M_g2 = compute_GM_connection(f_g2, 2, "Genus 2: y^2 = x^5 - t*x^3 + x")

# ==========================================
# TEST 3: The actual genus-4 family
# ==========================================
f_g4 = x**9 - t * x**5 + x
M_g4 = compute_GM_connection(f_g4, 4, "Genus 4: y^2 = x^9 - t*x^5 + x")

# ==========================================
# TEST 4: Alternate genus-1 family y^2 = x^3 - t*x
# df/dt = -x, so nabla_t(omega_0) = x/(2y^3)
# ==========================================
f_alt = x**3 - t * x
M_alt = compute_GM_connection(f_alt, 1, "Alt genus 1: y^2 = x^3 - t*x")

print("\n" + "="*70)
print("SUMMARY OF SYMPLECTIC TRACES")
print("="*70)
