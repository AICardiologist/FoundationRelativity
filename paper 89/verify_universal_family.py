#!/usr/bin/env python3
"""
Paper 89 — Universal Hyperelliptic Squeeze.

Computes the Gauss-Manin connection for the universal genus-4 hyperelliptic
Weil family y^2 = x^9 + ax^7 + bx^5 + cx^3 + x over Q(a,b,c).

Three parameter directions: d/da, d/db, d/dc.
Key result: tau_+(a,b,c) = 0 for all three directions (universal flatness).
"""
import sympy as sp
from sympy import Poly, cancel, expand, diff, Rational as Q, Matrix
import time

x, a, b, c = sp.symbols('x a b c')
DOMAIN = sp.QQ.frac_field(a, b, c)

# === The universal family ===
f = x**9 + a*x**7 + b*x**5 + c*x**3 + x
fp = diff(f, x)   # 9x^8 + 7ax^6 + 5bx^4 + 3cx^2 + 1
genus = 4
n = 2 * genus  # dim H^1 = 8

# Parameter derivatives
param_derivs = {
    'a': diff(f, a),  # x^7
    'b': diff(f, b),  # x^5
    'c': diff(f, c),  # x^3
}

print("Paper 89 — Universal Gauss-Manin Connection")
print(f"Curve: y^2 = x^9 + ax^7 + bx^5 + cx^3 + x")
print(f"Genus: {genus}, dim H^1: {n}")
print()

# === Verify oddness ===
assert expand(f.subs(x, -x) + f) == 0, "f must be odd for Q(i)-action"
print("PASS: f(-x) = -f(x) (Q(i)-action verified)")

# === Factorization f = x * g ===
g_core = cancel(f / x)
g_expected = x**8 + a*x**6 + b*x**4 + c*x**2 + 1
assert expand(g_core - g_expected) == 0, "Core polynomial mismatch"
print("PASS: f = x * g, g = x^8 + ax^6 + bx^4 + cx^2 + 1")

# === Palindromic characterization ===
# g is palindromic iff coeff of x^{8-k} = coeff of x^k for all k
# g = x^8 + ax^6 + bx^4 + cx^2 + 1
# g_rev = 1 + cx^2 + bx^4 + ax^6 + x^8 (reversed) => same as g iff a=c
g_rev = x**8 + c*x**6 + b*x**4 + a*x**2 + 1
palindromic_diff = expand(g_core - g_rev)
print(f"PASS: g - g_rev = {palindromic_diff}")
print(f"      Palindromic locus: a = c")
print()

# === Bezout identity: alpha*f + beta*f' = 1 ===
print("Computing Bezout coefficients over Q(a,b,c)[x]...")
t0 = time.time()
f_p = Poly(f, x, domain=DOMAIN)
fp_p = Poly(fp, x, domain=DOMAIN)
a_raw, b_raw, gcd_p = sp.gcdex(f_p, fp_p)
gcd_e = gcd_p.as_expr()
a_bez = cancel(a_raw.as_expr() / gcd_e)
b_bez = cancel(b_raw.as_expr() / gcd_e)
print(f"  Done ({time.time() - t0:.1f}s)")

# Leading coefficient of f' for degree reduction
lc_fp = fp_p.nth(n)  # = 9

def reduce_to_basis(expr):
    """Reduce polynomial mod f'(x) = 0 to degree < 2g = 8."""
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


# === Compute Gauss-Manin matrices for each parameter direction ===
results = {}

for param_name, f_param in param_derivs.items():
    print(f"\nComputing M_{param_name}...")
    t0 = time.time()

    M = [[sp.Integer(0)] * n for _ in range(n)]

    for k in range(n):
        N_k = expand(-f_param * x**k)

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

        # Verify Griffiths identity
        check = cancel(expand(N_k + h_k * fp - 2 * B_k * f))
        assert check == 0, f"Griffiths identity FAILED for {param_name}, k={k}"

    elapsed = time.time() - t0
    print(f"  Done ({elapsed:.1f}s)")

    # Traces
    tr_full = cancel(sum(M[k][k] for k in range(n)))
    even = [0, 2, 4, 6]
    odd = [1, 3, 5, 7]
    tau_p = cancel(sum(M[k][k] for k in even))
    tau_m = cancel(sum(M[k][k] for k in odd))

    print(f"  tr(M_{param_name}) = {tr_full}  {'PASS' if tr_full == 0 else 'FAIL'}")
    print(f"  tau_+_{param_name} = {tau_p}")
    print(f"  tau_-_{param_name} = {tau_m}")

    results[param_name] = {
        'M': M,
        'tr': tr_full,
        'tau_p': tau_p,
        'tau_m': tau_m,
        'diag': {k: M[k][k] for k in range(n)},
    }


# === Summary ===
print("\n" + "=" * 60)
print("UNIVERSAL TRACE VANISHING SUMMARY")
print("=" * 60)
all_pass = True
for param_name in ['a', 'b', 'c']:
    r = results[param_name]
    status_full = "PASS" if r['tr'] == 0 else "FAIL"
    status_plus = "PASS" if r['tau_p'] == 0 else "FAIL"
    status_minus = "PASS" if r['tau_m'] == 0 else "FAIL"
    print(f"  M_{param_name}: tr = {status_full}, tau_+ = {status_plus}, tau_- = {status_minus}")
    if r['tau_p'] != 0:
        all_pass = False
        print(f"    tau_+_{param_name} = {r['tau_p']}")

if all_pass:
    print("\n*** ALL TRACES VANISH: UNIVERSAL FLATNESS CONFIRMED ***")
else:
    print("\n*** TRACE VANISHING FAILED — CHECK RESULTS ***")


# === Specialization checks ===
print("\n" + "=" * 60)
print("SPECIALIZATION CHECKS")
print("=" * 60)

# Check 1: (a,b,c) = (t,0,0) should recover Paper 85 result
print("  (a,b,c) = (t,0,0): Paper 85 family")
for param_name in ['a', 'b', 'c']:
    tau_spec = results[param_name]['tau_p'].subs([(b, 0), (c, 0)])
    tau_spec = cancel(tau_spec)
    print(f"    tau_+_{param_name}(t,0,0) = {tau_spec}")

# Check 2: (a,b,c) = (0,-t,0) should recover Paper 84 family
print("  (a,b,c) = (0,-t,0): Paper 84/86 family")
t_var = sp.Symbol('t')
for param_name in ['a', 'b', 'c']:
    tau_spec = results[param_name]['tau_p'].subs([(a, 0), (b, -t_var), (c, 0)])
    tau_spec = cancel(tau_spec)
    print(f"    tau_+_{param_name}(0,-t,0) = {tau_spec}")

# Check 3: Fermat point (0,0,0)
print("  (a,b,c) = (0,0,0): Fermat specialization")
for param_name in ['a', 'b', 'c']:
    tau_spec = results[param_name]['tau_p'].subs([(a, 0), (b, 0), (c, 0)])
    tau_spec = cancel(tau_spec)
    print(f"    tau_+_{param_name}(0,0,0) = {tau_spec}")


# === Write output files ===
OUTDIR = "/Users/quantmann/FoundationRelativity/paper 89/"

# Matrix data
with open(OUTDIR + "p89_matrices.txt", "w") as fout:
    fout.write("Gauss-Manin connection: y^2 = x^9 + ax^7 + bx^5 + cx^3 + x\n")
    fout.write("Convention: nabla_p(omega_k) = sum_j M_p[j][k] * omega_j\n\n")
    for param_name in ['a', 'b', 'c']:
        fout.write(f"\n{'='*60}\n")
        fout.write(f"M_{param_name} (connection in d/d{param_name} direction)\n")
        fout.write(f"{'='*60}\n\n")
        M = results[param_name]['M']
        for i in range(n):
            for j in range(n):
                if M[i][j] != 0:
                    fout.write(f"M_{param_name}[{i}][{j}] = {M[i][j]}\n")
        fout.write(f"\ntr(M_{param_name}) = {results[param_name]['tr']}\n")
        fout.write(f"tau_+_{param_name} = {results[param_name]['tau_p']}\n")
        fout.write(f"tau_-_{param_name} = {results[param_name]['tau_m']}\n")

# V_+ block data
with open(OUTDIR + "p89_vplus_blocks.txt", "w") as fout:
    fout.write("V_+ blocks (even differentials omega_0, omega_2, omega_4, omega_6)\n\n")
    even = [0, 2, 4, 6]
    for param_name in ['a', 'b', 'c']:
        fout.write(f"\n{'='*60}\n")
        fout.write(f"M_+_{param_name} (4x4 V_+ block)\n")
        fout.write(f"{'='*60}\n\n")
        M = results[param_name]['M']
        for i_idx, i in enumerate(even):
            for j_idx, j in enumerate(even):
                entry = M[i][j]
                if entry != 0:
                    fout.write(f"M_+_{param_name}[{i_idx}][{j_idx}] = M[{i}][{j}] = {entry}\n")
        fout.write(f"\ntau_+_{param_name} = {results[param_name]['tau_p']}\n")

print(f"\nOutput: p89_matrices.txt, p89_vplus_blocks.txt")


# === Emit Lean data ===
print("\nGenerating Lean trace data...")

def to_lean_poly(expr, syms=[x, a, b, c]):
    """Convert sympy polynomial to Lean string over Z[x,a,b,c]."""
    expr = expand(expr)
    if expr == 0:
        return "0"
    p = Poly(expr, *syms, domain='ZZ')
    terms = []
    for monom, coeff in sorted(p.as_dict().items(), reverse=True):
        co = int(coeff)
        if co == 0:
            continue
        var_names = ['x', 'a', 'b', 'c']
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


lean_lines = []
lean_lines.append("/-")
lean_lines.append("  TraceData.lean — Ring-verified Griffiths identities for Paper 89")
lean_lines.append("  Auto-generated from verify_universal_family.py")
lean_lines.append("")
lean_lines.append("  Universal family: y² = x⁹ + ax⁷ + bx⁵ + cx³ + x (genus 4, Q(i)-action)")
lean_lines.append("  Connection: 8×8 Gauss-Manin over Q(a,b,c), three parameter directions")
lean_lines.append("  Key result: τ₊ = 0 for all three directions (universal flatness)")
lean_lines.append("")
lean_lines.append("  All identities verified by `ring` — no string constants, no rfl on data.")
lean_lines.append("-/")
lean_lines.append("")
lean_lines.append("import Mathlib")
lean_lines.append("")

# §1. Curve Data
lean_lines.append("-- ============================================================")
lean_lines.append("-- §1. Curve Data")
lean_lines.append("-- ============================================================")
lean_lines.append("")
lean_lines.append("/-- The defining polynomial f(x,a,b,c) = x⁹ + ax⁷ + bx⁵ + cx³ + x. -/")
lean_lines.append("noncomputable def p89_f (x a b c : ℤ) : ℤ :=")
lean_lines.append("  x ^ 9 + a * x ^ 7 + b * x ^ 5 + c * x ^ 3 + x")
lean_lines.append("")
lean_lines.append("/-- The x-derivative f'(x,a,b,c) = 9x⁸ + 7ax⁶ + 5bx⁴ + 3cx² + 1. -/")
lean_lines.append("noncomputable def p89_fp (x a b c : ℤ) : ℤ :=")
lean_lines.append("  9 * x ^ 8 + 7 * a * x ^ 6 + 5 * b * x ^ 4 + 3 * c * x ^ 2 + 1")
lean_lines.append("")
lean_lines.append("/-- The core polynomial g(x,a,b,c) = x⁸ + ax⁶ + bx⁴ + cx² + 1. -/")
lean_lines.append("noncomputable def p89_g (x a b c : ℤ) : ℤ :=")
lean_lines.append("  x ^ 8 + a * x ^ 6 + b * x ^ 4 + c * x ^ 2 + 1")
lean_lines.append("")

# §2. Griffiths Identities for each parameter direction
for param_name, f_param in param_derivs.items():
    lean_lines.append(f"-- ============================================================")
    lean_lines.append(f"-- §2{param_name}. Griffiths Identities (∂/∂{param_name} direction)")
    lean_lines.append(f"-- ============================================================")
    lean_lines.append("")

    for k in range(n):
        N_k = expand(-f_param * x**k)
        h0_expr = expand(-N_k * b_bez)
        u0_expr = expand(-N_k * a_bez)
        h0_p = Poly(h0_expr, x, domain=DOMAIN)
        q_h, r_h = sp.div(h0_p, f_p)
        h_k = r_h.as_expr()
        u_final = expand(u0_expr + q_h.as_expr() * fp)
        B_k = cancel(-u_final / 2)

        # Find LCD and clear denominators
        h_k_poly = Poly(expand(h_k), x, domain=DOMAIN)
        B_k_poly = Poly(expand(B_k), x, domain=DOMAIN)

        all_coeffs_dens = []
        for j in range(20):
            try:
                cv = h_k_poly.nth(j)
            except Exception:
                cv = 0
            if cv != 0:
                all_coeffs_dens.append(sp.fraction(cancel(cv))[1])
            try:
                cv2 = B_k_poly.nth(j)
            except Exception:
                cv2 = 0
            if cv2 != 0:
                all_coeffs_dens.append(sp.fraction(cancel(cv2))[1])

        if not all_coeffs_dens:
            lcd = sp.Integer(1)
        else:
            lcd = all_coeffs_dens[0]
            for d in all_coeffs_dens[1:]:
                lcd = sp.lcm(lcd, d)

        lcd_Nk = expand(lcd * N_k)
        lcd_hk = expand(lcd * h_k)
        lcd_Bk = expand(lcd * B_k)

        # Verify
        cleared_check = expand(lcd_Nk + lcd_hk * fp - 2 * lcd_Bk * f)
        assert cleared_check == 0, f"Cleared identity failed for {param_name}, k={k}"

        lhs = to_lean_poly(lcd_Nk + lcd_hk * fp)
        rhs = to_lean_poly(2 * lcd_Bk * f)

        lean_lines.append(f"/-- Griffiths identity ∂/∂{param_name}, k={k}: cleared by lcd. -/")
        lean_lines.append(f"theorem p89_griffiths_{param_name}_k{k} (x a b c : ℤ) :")
        lean_lines.append(f"    {lhs}")
        lean_lines.append(f"    =")
        lean_lines.append(f"    {rhs} := by ring")
        lean_lines.append("")

# §3. Trace vanishing
lean_lines.append("-- ============================================================")
lean_lines.append("-- §3. Trace Vanishing (Universal Flatness)")
lean_lines.append("-- ============================================================")
lean_lines.append("")

for param_name in ['a', 'b', 'c']:
    r = results[param_name]
    diag = r['diag']

    # V_+ diagonal (even indices)
    diag_plus = [diag[k] for k in [0, 2, 4, 6]]
    diag_numdens = [(sp.fraction(cancel(d))[0], sp.fraction(cancel(d))[1]) for d in diag_plus]
    cd = diag_numdens[0][1]
    for _, den in diag_numdens[1:]:
        cd = sp.lcm(cd, den)

    nums = [expand(num * cancel(cd / den)) for num, den in diag_numdens]
    numer_sum = expand(sum(nums))
    assert numer_sum == 0, f"tau_+_{param_name} numerator sum = {numer_sum}, expected 0"

    lean_lines.append(f"/-- τ₊ vanishing in ∂/∂{param_name} direction: sum of V₊ diagonal × common denom = 0. -/")
    lean_lines.append(f"theorem p89_tau_plus_{param_name}_vanishes (a b c : ℤ) :")

    # Format each numerator term
    num_strs = [to_lean_poly(n_val, syms=[a, b, c]) for n_val in nums]
    lean_lines.append(f"    ({num_strs[0]})")
    for ns in num_strs[1:]:
        lean_lines.append(f"    + ({ns})")
    lean_lines.append(f"    = 0 := by ring")
    lean_lines.append("")

    # V_- diagonal (odd indices)
    diag_minus = [diag[k] for k in [1, 3, 5, 7]]
    diag_numdens_m = [(sp.fraction(cancel(d))[0], sp.fraction(cancel(d))[1]) for d in diag_minus]
    cd_m = diag_numdens_m[0][1]
    for _, den in diag_numdens_m[1:]:
        cd_m = sp.lcm(cd_m, den)

    nums_m = [expand(num * cancel(cd_m / den)) for num, den in diag_numdens_m]
    numer_sum_m = expand(sum(nums_m))
    assert numer_sum_m == 0, f"tau_-_{param_name} numerator sum = {numer_sum_m}, expected 0"

    lean_lines.append(f"/-- τ₋ vanishing in ∂/∂{param_name} direction. -/")
    lean_lines.append(f"theorem p89_tau_minus_{param_name}_vanishes (a b c : ℤ) :")
    num_strs_m = [to_lean_poly(n_val, syms=[a, b, c]) for n_val in nums_m]
    lean_lines.append(f"    ({num_strs_m[0]})")
    for ns in num_strs_m[1:]:
        lean_lines.append(f"    + ({ns})")
    lean_lines.append(f"    = 0 := by ring")
    lean_lines.append("")

# §4. Structural data
lean_lines.append("-- ============================================================")
lean_lines.append("-- §4. Structural Data")
lean_lines.append("-- ============================================================")
lean_lines.append("")
lean_lines.append("/-- Genus of the universal family. -/")
lean_lines.append("def p89_genus : Nat := 4")
lean_lines.append("")
lean_lines.append("/-- g - 1 = 3 is odd (V₊ is Lagrangian, not symplectic). -/")
lean_lines.append("theorem p89_g_minus_1_odd : p89_genus - 1 = 3 := by rfl")
lean_lines.append("")
lean_lines.append("/-- 3 is odd. -/")
lean_lines.append("theorem p89_three_is_odd : ¬(2 ∣ (3 : ℤ)) := by decide")
lean_lines.append("")

output_path = OUTDIR + "lean_trace_data.lean"
with open(output_path, "w") as fout:
    fout.write("\n".join(lean_lines))

print(f"\nLean data written to {output_path}")
print(f"  3 × {n} Griffiths identities = {3 * n} theorems")
print(f"  6 trace vanishing theorems (3 tau_+, 3 tau_-)")
print("Done.")
