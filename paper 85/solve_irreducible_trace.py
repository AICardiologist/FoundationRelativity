#!/usr/bin/env python3
"""
Paper 85 — Symmetry Breaking Probe.

Computes the Gauss-Manin connection for y^2 = x^9 + tx^7 + x (genus 4)
using the correct Griffiths pole-order reduction: A_k = B_k - h_k'.

This curve has Q(i)-action via sigma(x,y) = (-x, iy) but NO order-8
automorphism tau. The V_+ eigenspace should be an irreducible 4x4 block.

Key question: is tau_+(t) = tr(M_+) zero or nonzero?
"""
import sympy as sp
from sympy import Poly, cancel, expand, diff, Rational as Q, Matrix
import json

x, t = sp.symbols('x t')
DOMAIN = sp.QQ.frac_field(t)

# === The curve ===
f = x**9 + t*x**7 + x
fp = diff(f, x)    # 9x^8 + 7tx^6 + 1
ft = diff(f, t)    # x^7
g = 4               # genus
n = 2*g              # dim H^1 = 8

# Verify: f(-x) = -f(x) (odd => sigma works)
assert expand(f.subs(x, -x) + f) == 0, "f must be odd for Q(i)-action"

# Verify: f(ix) != i*f(x) (tau broken)
fix = expand(f.subs(x, sp.I*x))
if_x = expand(sp.I * f)
tau_broken = expand(fix - if_x) != 0
print(f"tau broken (f(ix) != i*f(x)): {tau_broken}")

# === Bezout identity: a*f + b*f' = 1 ===
f_p = Poly(f, x, domain=DOMAIN)
fp_p = Poly(fp, x, domain=DOMAIN)
a_raw, b_raw, gcd_p = sp.gcdex(f_p, fp_p)
gcd_e = gcd_p.as_expr()
a_bez = cancel(a_raw.as_expr() / gcd_e)
b_bez = cancel(b_raw.as_expr() / gcd_e)

# Cohomological reduction: f'(x) = 0 in H^1 => reduce mod f'
lc_fp = fp_p.nth(n)  # coefficient of x^8 in f' = 9

def reduce_to_basis(expr):
    """Reduce A(x) modulo f'(x)=0 to degree < 8."""
    p = Poly(expand(expr), x, domain=DOMAIN)
    for _ in range(200):
        d = sp.degree(p, x)
        if d < n:
            break
        lc = p.nth(d)
        sub = sp.Integer(0)
        for j in range(n):
            cj = fp_p.nth(j)
            if cj != 0:
                sub += cj * x**(d - n + j)
        sub = lc * (-1 / lc_fp) * sub
        p = Poly(expand(p.as_expr() - lc * x**d + sub), x, domain=DOMAIN)
    return p.as_expr()

# === Compute Gauss-Manin matrix ===
M = [[sp.Integer(0)] * n for _ in range(n)]

for k in range(n):
    N_k = expand(-ft * x**k)  # = -x^{k+7}

    # Solve: h*f' + u*f = -N via extended gcd
    h0_expr = expand(-N_k * b_bez)
    u0_expr = expand(-N_k * a_bez)

    # Reduce h mod f
    h0_p = Poly(h0_expr, x, domain=DOMAIN)
    q_h, r_h = sp.div(h0_p, f_p)
    h_k = r_h.as_expr()
    u_final = expand(u0_expr + q_h.as_expr() * fp)

    # B_k = -u/2,  A_k = B_k - h_k'
    B_k = cancel(-u_final / 2)
    h_k_prime = diff(h_k, x)
    A_k_raw = expand(B_k - h_k_prime)

    # Reduce A_k using f'=0
    A_k_red = reduce_to_basis(A_k_raw)

    # Extract matrix entries
    for j in range(n):
        M[j][k] = cancel(A_k_red.coeff(x, j))

    # Verify identity: N_k + h_k*f' = 2*B_k*f
    check = cancel(expand(N_k + h_k * fp - 2 * B_k * f))
    if check != 0:
        print(f"  VERIFICATION FAILED for k={k}: residual nonzero!")

# === Results ===
OUTDIR = "/Users/quantmann/FoundationRelativity/paper 85/"

# Full trace
tr_full = cancel(sum(M[k][k] for k in range(n)))

# Eigenspace traces
even = [0, 2, 4, 6]
odd = [1, 3, 5, 7]
tau_p = cancel(sum(M[k][k] for k in even))
tau_m = cancel(sum(M[k][k] for k in odd))

# Check block-diagonality of V_+ (even-even entries only?)
off_block = []
for i in even:
    for j in even:
        if M[i][j] != 0 and i != j:
            off_block.append((i, j, M[i][j]))
    for j in odd:
        if M[i][j] != 0:
            off_block.append((i, j, M[i][j]))

print(f"\nPaper 85 — Gauss-Manin for y^2 = x^9 + tx^7 + x")
print(f"  tr(M) = {tr_full}  {'PASS' if tr_full == 0 else 'FAIL'}")
print(f"  tau_+(t) = {tau_p}")
print(f"  tau_-(t) = {tau_m}")
print(f"  tau_+ + tau_- = {cancel(tau_p + tau_m)}  (should be 0)")
if tau_p == 0:
    print(f"  *** tau_+ = 0: UNIVERSAL FLATNESS ***")
else:
    print(f"  *** tau_+ != 0: SYMMETRY BREAKING DETECTED ***")
    # Partial fraction
    pf = sp.apart(tau_p, t)
    print(f"  Partial fraction: {pf}")

# V_+ block structure
print(f"\n  V_+ off-diagonal entries (even-even, nonzero):")
for i, j, v in off_block:
    print(f"    M[{i}][{j}] = {v}")
if not off_block:
    print(f"    (block-diagonal)")

# 1. Full matrix
with open(OUTDIR + "p85_matrix.txt", "w") as fout:
    fout.write("Gauss-Manin connection: y^2 = x^9 + tx^7 + x\n")
    fout.write("Convention: nabla_t(omega_k) = sum_j M[j][k] * omega_j\n\n")
    for i in range(n):
        for j in range(n):
            if M[i][j] != 0:
                fout.write(f"M[{i}][{j}] = {M[i][j]}\n")
    fout.write(f"\ntr(M) = {tr_full}\n")
    fout.write(f"tau_+(t) = {tau_p}\n")
    fout.write(f"tau_-(t) = {tau_m}\n")

# 2. V_+ block (4x4)
with open(OUTDIR + "p85_vplus_block.txt", "w") as fout:
    fout.write("V_+ block (even differentials omega_0, omega_2, omega_4, omega_6)\n\n")
    for i_idx, i in enumerate(even):
        for j_idx, j in enumerate(even):
            entry = M[i][j]
            if entry != 0:
                fout.write(f"M_+[{i_idx}][{j_idx}] = M[{i}][{j}] = {entry}\n")
    fout.write(f"\ntau_+(t) = {tau_p}\n")
    if tau_p != 0:
        fout.write(f"Partial fraction: {sp.apart(tau_p, t)}\n")

print(f"\n  Output: p85_matrix.txt, p85_vplus_block.txt")
