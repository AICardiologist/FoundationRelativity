#!/usr/bin/env python3
"""
Paper 89 — Emit Lean 4 trace data for universal family.
Recomputes diagonal entries and emits numerator identities.
Output: lean_trace_data.lean
"""
import sympy as sp
from sympy import Poly, cancel, expand, diff, Rational as Q

x, a, b, c = sp.symbols('x a b c')
DOMAIN = sp.QQ.frac_field(a, b, c)

f = x**9 + a*x**7 + b*x**5 + c*x**3 + x
fp = diff(f, x)
genus = 4
n = 2 * genus

param_derivs = {'a': diff(f, a), 'b': diff(f, b), 'c': diff(f, c)}

f_p = Poly(f, x, domain=DOMAIN)
fp_p = Poly(fp, x, domain=DOMAIN)
a_raw, b_raw, gcd_p = sp.gcdex(f_p, fp_p)
gcd_e = gcd_p.as_expr()
a_bez = cancel(a_raw.as_expr() / gcd_e)
b_bez = cancel(b_raw.as_expr() / gcd_e)
lc_fp = fp_p.nth(n)

def reduce_to_basis(expr):
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

def to_lean_poly(expr, syms):
    expr = expand(expr)
    if expr == 0:
        return "0"
    p = Poly(expr, *syms, domain='ZZ')
    var_names = [str(s) for s in syms]
    terms = []
    for monom, coeff in sorted(p.as_dict().items(), reverse=True):
        co = int(coeff)
        if co == 0:
            continue
        parts = []
        if abs(co) != 1 or all(m == 0 for m in monom):
            parts.append(str(abs(co)))
        for idx, power in enumerate(monom):
            if power > 0:
                vn = var_names[idx]
                parts.append(f"{vn} ^ {power}" if power > 1 else vn)
        term = " * ".join(parts) if parts else "1"
        if co < 0:
            terms.append(f"- {term}")
        else:
            if terms:
                terms.append(f"+ {term}")
            else:
                terms.append(term)
    return " ".join(terms) if terms else "0"

# Compute diagonal entries for each parameter direction
all_diags = {}
for pname, f_param in param_derivs.items():
    diag = {}
    for k in range(n):
        N_k = expand(-f_param * x**k)
        h0_expr = expand(-N_k * b_bez)
        u0_expr = expand(-N_k * a_bez)
        h0_p = Poly(h0_expr, x, domain=DOMAIN)
        q_h, r_h = sp.div(h0_p, f_p)
        h_k = r_h.as_expr()
        u_final = expand(u0_expr + q_h.as_expr() * fp)
        B_k = cancel(-u_final / 2)
        h_k_prime = diff(h_k, x)
        A_k_raw = expand(B_k - h_k_prime)
        A_k_red = reduce_to_basis(A_k_raw)
        diag[k] = cancel(A_k_red.coeff(x, k))
    all_diags[pname] = diag

# Build Lean file
L = []
L.append("/-")
L.append("  TraceData.lean — Ring-verified identities for Paper 89")
L.append("  Auto-generated from emit_lean_data.py")
L.append("")
L.append("  Universal family: y² = x⁹ + ax⁷ + bx⁵ + cx³ + x")
L.append("  Key result: τ₊ = 0 for all three parameter directions")
L.append("-/")
L.append("")
L.append("import Mathlib")
L.append("")

# Trace vanishing: for each direction, extract numerators over common denom
for pname in ['a', 'b', 'c']:
    diag = all_diags[pname]

    for label, indices in [('plus', [0, 2, 4, 6]), ('minus', [1, 3, 5, 7])]:
        entries = [diag[k] for k in indices]
        numdens = [(sp.fraction(cancel(e))[0], sp.fraction(cancel(e))[1]) for e in entries]
        cd = numdens[0][1]
        for _, den in numdens[1:]:
            cd = sp.lcm(cd, den)
        nums = [expand(num * cancel(cd / den)) for num, den in numdens]
        total = expand(sum(nums))
        assert total == 0, f"tau_{label}_{pname} != 0: {total}"

        sign = '+' if label == 'plus' else '-'
        L.append(f"/-- τ{sign} vanishing in ∂/∂{pname}: numerators over common denominator sum to 0. -/")
        L.append(f"theorem p89_tau_{label}_{pname}_vanishes (a b c : ℤ) :")

        num_strs = [to_lean_poly(n_val, syms=[a, b, c]) for n_val in nums]
        L.append(f"    ({num_strs[0]})")
        for ns in num_strs[1:]:
            L.append(f"    + ({ns})")
        L.append(f"    = 0 := by ring")
        L.append("")

# Structural data
L.append("-- Structural data")
L.append("")
L.append("def p89_genus : Nat := 4")
L.append("")
L.append("theorem p89_g_minus_1_odd : p89_genus - 1 = 3 := by rfl")
L.append("")
L.append("theorem p89_three_is_odd : ¬(2 ∣ (3 : ℤ)) := by decide")
L.append("")

output_path = "/Users/quantmann/FoundationRelativity/paper 89/lean_trace_data.lean"
with open(output_path, "w") as fout:
    fout.write("\n".join(L))

print(f"OK: {output_path}")
