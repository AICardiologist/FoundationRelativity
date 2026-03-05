#!/usr/bin/env python3
"""
Paper 84 — Exotic Trace Probe
Compute the Gauss-Manin connection for the genus-4 hyperelliptic family
    C_t: y^2 = x^9 - t*x^5 + x
and extract the trace of the connection on the V_+ eigenspace.

DESIGN: Minimal stdout. All heavy data to disk.
TIMEOUT: Internal 5-minute timeout.

ALGORITHM:
  nabla_t(x^k dx/y) = x^{k+5}/(2*y^3) dx = x^{k+5}/(2*y*f) dx
  Use Bezout identity a*f + b*f' = 1 to decompose 1/f = a + b*f'/f.
  Term 1: (1/2)*x^{k+5}*a(x) dx/y  (polynomial, reduce mod x^8 relation)
  Term 2: (1/2)*x^{k+5}*b(x)*f'(x)/y^3 dx
    Using d(x^m/y) identity: x^m*f'/y^3 ≡ 2m*x^{m-1}/y in cohomology
    So Term 2 = sum_m p_m*m*x^{m-1} dx/y where P(x) = x^{k+5}*b(x) = sum p_m x^m
"""

import sympy as sp
from sympy import Rational as Q
import time, sys, os

t0 = time.time()
def elapsed():
    return time.time() - t0

x, t = sp.symbols('x t')
DOMAIN = sp.QQ.frac_field(t)

f = x**9 - t*x**5 + x          # y^2 = f(x)
df_dx = sp.diff(f, x)          # f'(x) = 9x^8 - 5tx^4 + 1

# ==========================================================
# Reduction: polynomial mod relation x^8 ≡ (5t/9)*x^4 - 1/9
# From f'(x) dx/y = d(2y) ≡ 0 in H^1_dR.
# ==========================================================
def reduce_to_basis(p_expr):
    """Reduce polynomial p(x) to degree < 8 using x^8 ≡ (5t/9)x^4 - 1/9.
    Returns [c_0, ..., c_7] in Q(t)."""
    p = sp.Poly(sp.expand(p_expr), x, domain=DOMAIN)
    for _ in range(100):
        d = sp.degree(p, x)
        if d < 8:
            break
        lc = p.nth(d)
        # x^d = x^{d-8} * x^8 ≡ x^{d-8} * (5t/9 * x^4 - 1/9)
        sub = lc * (Q(5,9)*t * x**(d-4) - Q(1,9) * x**(d-8))
        p = sp.Poly(sp.expand(p.as_expr() - lc*x**d + sub), x, domain=DOMAIN)
    result = p.as_expr()
    return [sp.cancel(result.coeff(x, j)) for j in range(8)]

# ==========================================================
# Bezout identity: a(x)*f(x) + b(x)*f'(x) = 1 over Q(t)[x]
# ==========================================================
print(f"[{elapsed():.1f}s] Computing Bezout identity...")

f_poly = sp.Poly(f, x, domain=DOMAIN)
df_poly = sp.Poly(df_dx, x, domain=DOMAIN)

s_raw, t_raw, gcd_poly = sp.gcdex(f_poly, df_poly)
gcd_expr = gcd_poly.as_expr()

# Normalize: a*f + b*f' = 1
a_bez = sp.cancel(s_raw.as_expr() / gcd_expr)
b_bez = sp.cancel(t_raw.as_expr() / gcd_expr)

print(f"[{elapsed():.1f}s] gcd degree: {sp.degree(gcd_poly, x)}")

# Verify
check = sp.cancel(sp.expand(a_bez * f + b_bez * df_dx))
assert check == 1, f"Bezout check FAILED: {check}"
print(f"[{elapsed():.1f}s] Bezout verified: a*f + b*f' = 1.")

# ==========================================================
# Build 8x8 Gauss-Manin connection matrix M(t)
# M[j][k] = coefficient of x^j dx/y in nabla_t(x^k dx/y)
# ==========================================================
print(f"[{elapsed():.1f}s] Computing 8x8 connection matrix...")

M = [[sp.Integer(0)]*8 for _ in range(8)]

for k in range(8):
    if elapsed() > 300:
        print(f"TIMEOUT at column k={k}")
        sys.exit(1)

    # nabla_t(x^k dx/y) = x^{k+5}/(2yf) dx
    # = (1/2)*x^{k+5}*a/y dx + (1/2)*x^{k+5}*b*f'/(yf) dx

    # Term 1: (1/2) * x^{k+5} * a(x) — polynomial times dx/y
    term1 = sp.expand(x**(k+5) * a_bez) / 2

    # Term 2: from the identity x^m*f'/(2y^3) ≡ m*x^{m-1}/y
    # Let P(x) = x^{k+5}*b(x). Then (1/2)*P*f'/y^3 ≡ sum p_m*m*x^{m-1}/y
    P_expr = sp.expand(x**(k+5) * b_bez)
    P_poly = sp.Poly(P_expr, x, domain=DOMAIN)

    term2 = sp.Integer(0)
    for monom, coeff in P_poly.as_dict().items():
        m = monom[0]
        if m >= 1:
            term2 += coeff * m * x**(m-1)
    term2 = sp.expand(term2)

    # Total polynomial to reduce to degree < 8
    total = sp.expand(term1 + term2)
    coeffs = reduce_to_basis(total)

    for j in range(8):
        M[j][k] = coeffs[j]

    print(f"[{elapsed():.1f}s] Column {k} done.")

print(f"[{elapsed():.1f}s] Full 8x8 matrix computed.")

# ==========================================================
# Block-diagonality check (automorphism symmetry)
# (x,y)->(-x,iy) acts as (-1)^k * i on x^k dx/y
# V_+ = {k even}, V_- = {k odd}. M should not mix them.
# ==========================================================
even_idx = [0, 2, 4, 6]
odd_idx = [1, 3, 5, 7]
off_block = False
for ei in even_idx:
    for oj in odd_idx:
        if sp.cancel(M[ei][oj]) != 0 or sp.cancel(M[oj][ei]) != 0:
            off_block = True
            break

if off_block:
    print("WARNING: M is NOT block-diagonal! Symmetry check FAILED.")
else:
    print(f"[{elapsed():.1f}s] Symmetry PASSED: M is block-diagonal (even/odd).")

# ==========================================================
# Extract V_+ block (even indices) and compute trace
# ==========================================================
M_plus = [[M[even_idx[i]][even_idx[j]] for j in range(4)] for i in range(4)]
tau_plus = sp.cancel(sum(M_plus[i][i] for i in range(4)))

# Also extract V_- block (odd indices)
M_minus = [[M[odd_idx[i]][odd_idx[j]] for j in range(4)] for i in range(4)]
tau_minus = sp.cancel(sum(M_minus[i][i] for i in range(4)))

# Full trace for consistency check
tau_full = sp.cancel(sum(M[k][k] for k in range(8)))

print(f"\n{'='*60}")
print(f"RESULT: tau_+(t) = {tau_plus}")
print(f"RESULT: tau_-(t) = {tau_minus}")
print(f"RESULT: Tr(M)   = {tau_full}")
print(f"CHECK:  tau_+ + tau_- = {sp.cancel(tau_plus + tau_minus)}")
print(f"{'='*60}")

# Analyze tau_+
def analyze_trace(name, tau):
    if tau == 0:
        print(f"{name}: TRIVIAL (flat section is constant)")
        return "TRIVIAL"
    # Factor
    tau_num = sp.numer(tau)
    tau_den = sp.denom(tau)
    # Check c/t form
    test = sp.cancel(tau * t)
    if not test.has(t):
        c = sp.Rational(test)
        galois = f"FINITE_mu{c.q}" if c.q > 1 else "FINITE_trivial"
        print(f"{name} = {c}/t  =>  flat section ~ t^{{{c}}}")
        print(f"  Galois type: {galois}")
        return galois
    # Partial fraction decomposition
    pf = sp.apart(tau, t)
    print(f"{name} = {pf}")
    # Check if purely logarithmic (ratio of polynomials with simple poles only)
    poly_part = sp.cancel(tau - sum(sp.cancel(c/(t-r)) for r, c in
        [(sp.Integer(2), sp.cancel(sp.limit(tau*(t-2), t, 2))),
         (sp.Integer(-2), sp.cancel(sp.limit(tau*(t+2), t, -2)))]))
    if poly_part != 0:
        print(f"  Polynomial part (irregular singularity at infinity): {poly_part}")
        print(f"  => Flat section involves exp(integral of polynomial)")
        print(f"  Galois type: Gm (transcendental)")
        return "Gm"
    else:
        print(f"  Purely logarithmic => finite monodromy")
        return "FINITE"

galois_plus = analyze_trace("tau_+", tau_plus)
galois_minus = analyze_trace("tau_-", tau_minus)

# Numerical verification at t = 3
print(f"\n--- Numerical check at t=3 ---")
for name, trace_val in [("tau_+", tau_plus), ("tau_-", tau_minus)]:
    val = trace_val.subs(t, 3)
    print(f"{name}(3) = {val} = {float(val):.6f}")

print(f"\n[{elapsed():.1f}s] Total runtime.")

# ==========================================================
# Emit Lean data file
# ==========================================================
os.makedirs("P84_ExoticTrace/Papers/P84_ExoticTrace", exist_ok=True)

with open("P84_ExoticTrace/Papers/P84_ExoticTrace/TraceData.lean", "w") as out:
    out.write("import Mathlib.Tactic\n\n")
    out.write("/-! # Paper 84 — CAS-Emitted Exotic Trace Data\n\n")
    out.write(f"Computed by solve_exotic_trace.py\n")
    out.write(f"Curve: y^2 = x^9 - t*x^5 + x (genus 4)\n")
    out.write(f"V_+ trace: tau_+(t) = {tau_plus}\n")
    out.write(f"V_- trace: tau_-(t) = {tau_minus}\n")
    out.write(f"Galois type (V_+): {galois_plus}\n")
    out.write(f"Galois type (V_-): {galois_minus}\n")
    out.write("-/\n\n")
    out.write(f"def exotic_trace_plus_display : String := \"{tau_plus}\"\n")
    out.write(f"def exotic_trace_minus_display : String := \"{tau_minus}\"\n\n")

    # CAS-verified data
    tau_plus_num = sp.numer(tau_plus)
    tau_plus_den = sp.denom(tau_plus)
    out.write(f"-- tau_+(t) numerator coefficients (descending): {sp.Poly(tau_plus_num, t).all_coeffs()}\n")
    out.write(f"-- tau_+(t) denominator coefficients (descending): {sp.Poly(tau_plus_den, t).all_coeffs()}\n\n")

    out.write(f"-- Galois type: {galois_plus} (V_+), {galois_minus} (V_-)\n")
    out.write(f"def galois_type_plus : String := \"{galois_plus}\"\n")
    out.write(f"def galois_type_minus : String := \"{galois_minus}\"\n\n")

    out.write(f"-- V_+ block diagonal entries\n")
    for i in range(4):
        out.write(f"-- M_+[{i},{i}] = {sp.cancel(M_plus[i][i])}\n")

    out.write(f"\n-- V_- block diagonal entries\n")
    for i in range(4):
        out.write(f"-- M_-[{i},{i}] = {sp.cancel(M_minus[i][i])}\n")

    # Full V_+ matrix
    out.write(f"\n-- Full V_+ block (4x4):\n")
    for i in range(4):
        for j in range(4):
            out.write(f"-- M_+[{i},{j}] = {sp.cancel(M_plus[i][j])}\n")

print(f"[{elapsed():.1f}s] Lean data written.")
