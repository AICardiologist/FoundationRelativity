#!/usr/bin/env python3
"""
Paper 92: Exact polynomial reconstruction for Lean emission.

Reconstructs the trace numerator polynomials using:
  1. Evaluate diagonal entries at integer grid points (univariate gcdex, fast)
  2. Multiply by LCD at each point to get integer numerators
  3. Solve Vandermonde system over Q (exact) to get polynomial coefficients

Iterates on the degree bound until the reconstruction verifies at extra points.
"""

import sys, time, itertools
from fractions import Fraction as F
import sympy as sp
from sympy import (Symbol, symbols, Poly, cancel, expand, diff,
                   Rational, Integer, fraction, gcdex, Matrix)

# ---------------------------------------------------------------------------
# Core: evaluate diagonal entries at a specialisation point
# ---------------------------------------------------------------------------
def eval_diag_entries(g, param_vals):
    """
    Returns for each param direction j:
      - list of g rational diagonal entries (as sympy Rationals)
      - the LCD (as integer)
      - list of g integer numerators (diag * lcd)
      - trace (should be 0)
    """
    n = 2 * g
    x = Symbol('x')
    n_params = g - 1

    # Build specialised f(x)
    f_expr = x**(2*g + 1) + x
    for j in range(n_params):
        exp = 2*g - 2*(j + 1) + 1
        f_expr += param_vals[j] * x**exp
    fp_expr = diff(f_expr, x)

    f_p = Poly(f_expr, x, domain='QQ')
    fp_p = Poly(fp_expr, x, domain='QQ')

    a_raw, b_raw, gcd_p = gcdex(f_p, fp_p)
    ge = gcd_p.as_expr()
    if ge == 0:
        return None
    a_bez = cancel(a_raw.as_expr() / ge)
    b_bez = cancel(b_raw.as_expr() / ge)
    lc_fp = fp_p.nth(n)

    def reduce_mod_fp(p):
        for _ in range(200):
            d = p.degree()
            if d < n:
                break
            lc = p.nth(d)
            if lc == 0:
                break
            sub = Poly(Rational(-1, lc_fp) * lc, x, domain='QQ') * Poly(x**(d - n), x, domain='QQ') * fp_p
            p = p + sub
            p = Poly(cancel(p.as_expr()), x, domain='QQ')
        return p

    out = {}
    for j in range(n_params):
        s_j = 2*g - 2*(j + 1) + 1
        entries = []
        for kv in range(g):
            k = 2 * kv
            D = k + s_j
            N_k = Poly(-x**D, x, domain='QQ')

            nb = Poly(cancel((-N_k * Poly(b_bez, x, domain='QQ')).as_expr()), x, domain='QQ')
            na = Poly(cancel((-N_k * Poly(a_bez, x, domain='QQ')).as_expr()), x, domain='QQ')

            q_h, r_h = sp.div(nb, f_p, x, domain='QQ')
            h_k = r_h.as_expr()
            u_final = cancel(na.as_expr() + q_h.as_expr() * fp_expr)
            B_k = cancel(-u_final / 2)
            h_kp = diff(h_k, x)
            A_raw = Poly(cancel(B_k - h_kp), x, domain='QQ')
            A_red = reduce_mod_fp(A_raw)
            entries.append(Rational(A_red.nth(k)))

        # Compute LCD
        dens = [fraction(cancel(e))[1] for e in entries if e != 0]
        lcd = Integer(1)
        for d in dens:
            lcd = sp.lcm(lcd, d)

        nums = [int(e * lcd) for e in entries]
        trace = sum(nums)
        out[j] = {'entries': entries, 'lcd': int(lcd), 'nums': nums, 'trace': trace}

    return out


# ---------------------------------------------------------------------------
# Monomial enumeration
# ---------------------------------------------------------------------------
def monomials_up_to_degree(n_vars, max_deg):
    """All monomials (as tuples of exponents) with total degree <= max_deg."""
    from itertools import combinations_with_replacement
    mons = []
    for d in range(max_deg + 1):
        for combo in combinations_with_replacement(range(n_vars), d):
            exps = [0] * n_vars
            for idx in combo:
                exps[idx] += 1
            mons.append(tuple(exps))
    return mons


def eval_monomial(mon, pt):
    """Evaluate monomial exponent tuple at integer point."""
    v = 1
    for k, e in enumerate(mon):
        if e > 0:
            v *= pt[k] ** e
    return v


# ---------------------------------------------------------------------------
# Reconstruction for one genus
# ---------------------------------------------------------------------------
def reconstruct_genus(g, max_degree=None):
    """
    Reconstruct trace numerator polynomials for genus g.
    Returns dict with polynomial expressions for each (direction, diag entry).
    """
    n_params = g - 1
    params = [Symbol(f'a{j}') for j in range(1, n_params + 1)]

    if max_degree is None:
        max_degree = g  # start with g, increase if needed

    print(f"\n  Reconstructing genus {g}, trying degree bound {max_degree}...")

    mons = monomials_up_to_degree(n_params, max_degree)
    n_mons = len(mons)
    print(f"    {n_mons} monomials in {n_params} variables up to degree {max_degree}")

    # Generate evaluation grid: integers 0..R in each variable
    import math
    R = max(2, math.ceil(n_mons ** (1.0 / n_params)))
    while (R + 1) ** n_params < n_mons + 5:
        R += 1

    all_pts = list(itertools.islice(
        itertools.product(range(R + 1), repeat=n_params),
        n_mons + 20
    ))
    print(f"    Using {len(all_pts)} evaluation points (grid 0..{R})")

    # Evaluate at all points
    print(f"    Evaluating...")
    t0 = time.time()

    # Store: eval_data[j_dir][kv] = list of (point_idx, numerator_value)
    eval_data = {j: {kv: [] for kv in range(g)} for j in range(n_params)}
    valid_pts = []  # indices into all_pts

    for i, pt in enumerate(all_pts):
        pt_list = list(pt)
        try:
            res = eval_diag_entries(g, pt_list)
        except:
            res = None
        if res is None:
            continue

        # Check all traces zero
        all_zero = all(res[j]['trace'] == 0 for j in range(n_params))
        if not all_zero:
            print(f"    ERROR: nonzero trace at {pt_list}")
            return None

        valid_pts.append(i)
        for j in range(n_params):
            for kv in range(g):
                eval_data[j][kv].append(res[j]['nums'][kv])

    elapsed = time.time() - t0
    print(f"    {len(valid_pts)} valid points [{elapsed:.1f}s]")

    if len(valid_pts) < n_mons:
        print(f"    ERROR: only {len(valid_pts)} valid points, need {n_mons}")
        return None

    # Build Vandermonde matrix (rational, exact)
    print(f"    Building {n_mons}×{n_mons} Vandermonde...")
    V_rows = []
    for i_valid in range(n_mons):
        pt = all_pts[valid_pts[i_valid]]
        row = [eval_monomial(mon, pt) for mon in mons]
        V_rows.append(row)

    V = Matrix(V_rows)

    # For each (direction, diag entry): solve V * coeffs = rhs
    result_polys = {}
    for j in range(n_params):
        pname = f'a{j+1}'
        print(f"    Solving for d/d{pname}...")
        t0 = time.time()

        diag_polys = {}
        for kv in range(g):
            rhs = Matrix([eval_data[j][kv][i] for i in range(n_mons)])
            try:
                coeffs = V.solve(rhs)
            except Exception as e:
                print(f"      ERROR solving for kv={kv}: {e}")
                return None

            # Build polynomial
            poly_expr = Integer(0)
            for idx, mon in enumerate(mons):
                c = coeffs[idx]
                if c != 0:
                    term = Integer(c)
                    for k_var, e in enumerate(mon):
                        if e > 0:
                            term *= params[k_var] ** e
                    poly_expr += term
            diag_polys[kv] = expand(poly_expr)

        # Verify: sum should be zero
        total = expand(sum(diag_polys[kv] for kv in range(g)))
        if total != 0:
            print(f"      SUM NONZERO for {pname}: {total}")
            print(f"      Degree bound {max_degree} may be too low. Try increasing.")
            return None
        print(f"      Sum verified = 0 [{time.time()-t0:.1f}s]")

        # Verify at extra points (beyond the interpolation set)
        n_extra = min(5, len(valid_pts) - n_mons)
        verified_extra = 0
        for i_extra in range(n_mons, n_mons + n_extra):
            if i_extra >= len(valid_pts):
                break
            pt = all_pts[valid_pts[i_extra]]
            for kv in range(g):
                expected = eval_data[j][kv][i_extra]
                # Evaluate polynomial at pt
                actual = int(diag_polys[kv].subs({
                    params[k]: pt[k] for k in range(n_params)
                }))
                if actual != expected:
                    print(f"      MISMATCH at extra point {pt}, kv={kv}: got {actual}, expected {expected}")
                    print(f"      Degree bound {max_degree} is too low.")
                    return None
            verified_extra += 1
        if verified_extra > 0:
            print(f"      Verified at {verified_extra} extra points")

        result_polys[j] = {'param_name': pname, 'diag_nums': diag_polys}

    return {
        'g': g, 'n': 2*g, 'params': params,
        'diag_data': result_polys,
        'all_zero': True,
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
if __name__ == "__main__":
    g = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    max_deg = int(sys.argv[2]) if len(sys.argv) > 2 else None
    result = reconstruct_genus(g, max_degree=max_deg)
    if result:
        print(f"\n  SUCCESS for genus {g}")
        # Print the polynomial for the first direction, first entry
        j0_data = result['diag_data'][0]
        pname = j0_data['param_name']
        for kv in range(g):
            poly = j0_data['diag_nums'][kv]
            nterms = len(Poly(poly, *result['params']).as_dict()) if poly != 0 else 0
            print(f"    d/d{pname} diag_{kv}: {nterms} terms")
    else:
        print(f"\n  FAILED for genus {g}")
