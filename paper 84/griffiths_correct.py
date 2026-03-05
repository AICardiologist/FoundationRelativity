#!/usr/bin/env python3
"""
Correct Gauss-Manin connection for hyperelliptic families y^2 = f(x,t).

A_k = B_k - h_k'  where  h_k*f' - 2*B_k*f = -N_k,  N_k = -f_t * x^k.
"""
import sympy as sp
from sympy import Poly, cancel, expand, diff
import sys

x, t = sp.symbols('x t')
DOMAIN = sp.QQ.frac_field(t)
OUTFILE = "/Users/quantmann/FoundationRelativity/paper 84/GM_output.txt"
fout = open(OUTFILE, "w")

def log(msg):
    fout.write(msg + "\n")

def compute_GM(f_poly, g):
    n = 2 * g
    f = f_poly
    fp = diff(f, x)
    ft = diff(f, t)
    f_p = Poly(f, x, domain=DOMAIN)
    fp_p = Poly(fp, x, domain=DOMAIN)
    a_raw, b_raw, gcd_p = sp.gcdex(f_p, fp_p)
    gcd_e = gcd_p.as_expr()
    a_bez = cancel(a_raw.as_expr() / gcd_e)
    b_bez = cancel(b_raw.as_expr() / gcd_e)
    lc_fp = Poly(fp, x, domain=DOMAIN).nth(n)

    def reduce_to_basis(expr):
        p = Poly(expand(expr), x, domain=DOMAIN)
        fp_poly = Poly(fp, x, domain=DOMAIN)
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
            sub = lc * (-1 / lc_fp) * sub
            p = Poly(expand(p.as_expr() - lc * x**d + sub), x, domain=DOMAIN)
        return [cancel(p.as_expr().coeff(x, j)) for j in range(n)]

    M = [[sp.Integer(0)] * n for _ in range(n)]
    for k in range(n):
        N = expand(-ft * x**k)
        h0_expr = expand(-N * b_bez)
        u0_expr = expand(-N * a_bez)
        h0_p = Poly(h0_expr, x, domain=DOMAIN)
        q_h, r_h = sp.div(h0_p, f_p)
        h_expr = r_h.as_expr()
        u_final_expr = expand(u0_expr + q_h.as_expr() * fp)
        B_expr = cancel(-u_final_expr / 2)
        h_prime = diff(h_expr, x)
        A_expr = expand(B_expr - h_prime)
        coeffs = reduce_to_basis(A_expr)
        for j in range(n):
            M[j][k] = coeffs[j]
    return M

# ---- Tests ----

# 1. Legendre y^2 = x(x-1)(x-t) — known answer
f2 = expand(x * (x - 1) * (x - t))
M2 = compute_GM(f2, 1)
expected = {
    (0,0): cancel(sp.Rational(1,2)/(1-t)),
    (0,1): cancel(sp.Rational(-1,1)/(2*t*(1-t))),
    (1,0): cancel(sp.Rational(1,2)/(1-t)),
    (1,1): cancel(sp.Rational(-1,2)/(1-t)),
}
legendre_ok = all(cancel(M2[i][j] - expected[(i,j)]) == 0 for (i,j) in expected)
tr2 = cancel(M2[0][0] + M2[1][1])
print(f"Legendre: tr={tr2}, known match={'YES' if legendre_ok else 'NO'}")
log(f"Legendre: tr={tr2}, known match={legendre_ok}")
for (i,j) in expected:
    log(f"  M[{i}][{j}] = {M2[i][j]}  (expected {expected[(i,j)]})")

# 2. y^2 = x^3 - tx
f1 = x**3 - t*x
M1 = compute_GM(f1, 1)
tr1 = cancel(M1[0][0] + M1[1][1])
print(f"x^3-tx:   tr={tr1}, M[0][0]={M1[0][0]}, M[1][1]={M1[1][1]}")
log(f"\nx^3-tx: tr={tr1}")
for i in range(2):
    for j in range(2):
        log(f"  M[{i}][{j}] = {M1[i][j]}")

# 3. Genus 2: y^2 = x^5 - tx^3 + x
f3 = x**5 - t*x**3 + x
M3 = compute_GM(f3, 2)
tr3 = cancel(sum(M3[k][k] for k in range(4)))
print(f"Genus 2:  tr={tr3}")
log(f"\nGenus 2: tr={tr3}")
for i in range(4):
    for j in range(4):
        if M3[i][j] != 0:
            log(f"  M[{i}][{j}] = {M3[i][j]}")

# 4. Genus 4: y^2 = x^9 - tx^5 + x (THE TARGET)
print("Computing genus 4... (slow)")
f4 = x**9 - t*x**5 + x
M4 = compute_GM(f4, 4)
tr4 = cancel(sum(M4[k][k] for k in range(8)))
even = [0,2,4,6]
tau_plus = cancel(sum(M4[even[i]][even[i]] for i in range(4)))

print(f"Genus 4:  tr={tr4}  {'PASS' if tr4 == 0 else 'FAIL'}")
print(f"  tau_+(t) = {tau_plus}")

if tau_plus != 0:
    pf = sp.apart(tau_plus, t)
    r2 = cancel(sp.limit(tau_plus*(t-2), t, 2))
    rm2 = cancel(sp.limit(tau_plus*(t+2), t, -2))
    print(f"  apart = {pf}")
    print(f"  Res(+2) = {r2},  Res(-2) = {rm2}")
else:
    print(f"  tau_+ = 0 (unexpected)")

# Regularity check on diagonals
irreg_count = 0
for k in range(8):
    mk = M4[k][k]
    if mk != 0:
        nd = sp.degree(Poly(sp.numer(mk), t))
        dd = sp.degree(Poly(sp.denom(mk), t))
        if nd >= dd:
            irreg_count += 1
print(f"  Irregular diag entries: {irreg_count}/8")

# Dump full matrix to file
log(f"\nGenus 4 full matrix:")
for i in range(8):
    for j in range(8):
        if M4[i][j] != 0:
            log(f"  M[{i}][{j}] = {M4[i][j]}")
log(f"\ntr = {tr4}")
log(f"tau_+ = {tau_plus}")
if tau_plus != 0:
    log(f"apart = {sp.apart(tau_plus, t)}")
    log(f"Res(+2) = {r2}")
    log(f"Res(-2) = {rm2}")

fout.close()
print(f"\nFull output: {OUTFILE}")
