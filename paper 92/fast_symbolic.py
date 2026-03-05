#!/usr/bin/env python3
"""
Paper 92: Fast symbolic Griffiths reduction.

Key optimization: keep everything as Poly objects over the fraction field.
Avoid expand() and cancel() on raw expressions — use Poly arithmetic instead.

Computes ONLY the trace for each parameter direction (not full matrix).
"""

import sys, time, gc
import sympy as sp
from sympy import (Symbol, Poly, cancel, expand, diff, Rational, Integer, fraction)

def compute_trace_symbolic(g, verbose=True):
    """
    Compute tau_+ for all parameter directions of genus g.
    Returns {j_idx: {'tau': sympy_expr, 'diag': {kv: expr}, 'param': str}}
    """
    n = 2 * g
    x = Symbol('x')
    n_params = g - 1
    params = [Symbol(f'a{j}') for j in range(1, n_params + 1)]

    # Build f and f'
    f_expr = x**(2*g + 1) + x
    for j_idx, aj in enumerate(params):
        exp = 2*g - 2*(j_idx + 1) + 1
        f_expr += aj * x**exp
    fp_expr = diff(f_expr, x)

    DOMAIN = sp.QQ.frac_field(*params) if n_params > 0 else sp.QQ

    f_p = Poly(f_expr, x, domain=DOMAIN)
    fp_p = Poly(fp_expr, x, domain=DOMAIN)

    if verbose:
        print(f"  f = {f_expr}")
        print(f"  Computing Bézout over {DOMAIN}[x]...")

    t0 = time.time()
    a_bez_raw, b_bez_raw, gcd_p = sp.gcdex(f_p, fp_p)
    gcd_e = gcd_p.as_expr()

    # Convert Bézout coefficients to Poly over DOMAIN
    # a_bez * f + b_bez * f' = 1
    a_bez_p = Poly(a_bez_raw.as_expr() / gcd_e, x, domain=DOMAIN)
    b_bez_p = Poly(b_bez_raw.as_expr() / gcd_e, x, domain=DOMAIN)
    if verbose:
        print(f"  Bézout done [{time.time()-t0:.1f}s]")

    lc_fp = fp_p.nth(n)  # = 2g + 1

    def reduce_mod_fp_poly(p):
        """Reduce Poly p(x) in DOMAIN[x] mod f'(x) to degree < n."""
        for _ in range(500):
            d = p.degree()
            if d < n:
                break
            lc = p.nth(d)
            if lc == 0:
                break
            # p -= (lc / lc_fp) * x^{d-n} * f'(x)
            shift = Poly(x**(d - n), x, domain=DOMAIN)
            correction = shift * fp_p
            # Scale by lc/lc_fp
            # We need to multiply correction by (lc / lc_fp)
            # Do it coefficient by coefficient
            scaled = Poly({k: v * lc / lc_fp for k, v in correction.as_dict().items()},
                         x, domain=DOMAIN)
            p = p - scaled
            # Simplify by removing degree-d term explicitly
            # (it should be cancelled but let's be safe)
        return p

    results = {}

    for j_idx in range(n_params):
        pname = f'a{j_idx + 1}'
        s_j = 2*g - 2*(j_idx + 1) + 1

        if verbose:
            print(f"\n  Direction d/d{pname} (df/d{pname} = x^{s_j})...")

        t_dir = time.time()
        diag_entries = {}

        for k_vp in range(g):
            k = 2 * k_vp  # even basis index
            D = k + s_j

            t1 = time.time()

            # N_k = -x^D as a Poly
            N_k_p = Poly(-x**D, x, domain=DOMAIN)

            # Step 1: h0 = -N_k * b_bez (as Poly multiplication)
            # Since N_k = -x^D, this is just x^D * b_bez
            # Shift b_bez by D: multiply each monomial's x-degree by adding D
            h0_p = Poly({(k_x + D,): v for (k_x,), v in b_bez_p.as_dict().items()},
                       x, domain=DOMAIN)

            # Step 2: u0 = -N_k * a_bez = x^D * a_bez
            u0_p = Poly({(k_x + D,): v for (k_x,), v in a_bez_p.as_dict().items()},
                       x, domain=DOMAIN)

            # Step 3: h_k = h0 mod f, q = h0 div f
            q_h, r_h = sp.div(h0_p, f_p, x, domain=DOMAIN)
            h_k_p = r_h

            # Step 4: u_final = u0 + q * f'
            u_final_p = u0_p + q_h * fp_p

            # Step 5: B_k = -u_final / 2
            B_k_dict = {k_x: -v / 2 for k_x, v in u_final_p.as_dict().items()}
            B_k_p = Poly(B_k_dict, x, domain=DOMAIN) if B_k_dict else Poly(0, x, domain=DOMAIN)

            # Step 6: h_k' (derivative of h_k w.r.t. x)
            h_k_prime_dict = {}
            for (k_x,), v in h_k_p.as_dict().items():
                if k_x > 0:
                    h_k_prime_dict[(k_x - 1,)] = v * k_x
            h_k_prime_p = Poly(h_k_prime_dict, x, domain=DOMAIN) if h_k_prime_dict else Poly(0, x, domain=DOMAIN)

            # Step 7: A_k = B_k - h_k'
            A_k_p = B_k_p - h_k_prime_p

            # Step 8: Reduce A_k mod f'
            A_k_red = reduce_mod_fp_poly(A_k_p)

            # Step 9: Extract diagonal entry = coeff of x^k
            diag_entry = A_k_red.nth(k) if A_k_red.degree() >= k else 0

            diag_entries[k_vp] = diag_entry

            t2 = time.time()
            if verbose:
                print(f"    k={k}: [{t2-t1:.1f}s]", end="")
                if isinstance(diag_entry, (int, Integer)) and diag_entry == 0:
                    print(" = 0")
                else:
                    print(f" (nonzero)")

        # Compute trace
        tau_raw = sum(diag_entries.values())
        tau_simplified = cancel(tau_raw)

        elapsed = time.time() - t_dir
        status = "ZERO" if tau_simplified == 0 else f"NONZERO"
        if verbose:
            print(f"  tau_+({pname}) = {status} [{elapsed:.1f}s]")

        results[j_idx] = {
            'param': pname,
            'diag': diag_entries,
            'tau': tau_simplified,
        }

        # Free memory
        gc.collect()

    return results, params


def to_lean_poly(expr, syms):
    """Convert sympy polynomial to Lean string over Z[syms]."""
    expr = expand(expr)
    if expr == 0:
        return "0"
    p = Poly(expr, *syms, domain='ZZ')
    sym_names = [str(s) for s in syms]
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
                vn = sym_names[idx]
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


def emit_lean_for_genus(g, results, params, filename):
    """Emit Lean trace vanishing theorems for one genus."""
    lines = []
    param_decl = " ".join([f"({p} : ℤ)" for p in params])

    for j_idx, res in sorted(results.items()):
        pname = res['param']
        diag = res['diag']
        tau = res['tau']

        if tau != 0:
            lines.append(f"-- WARNING: tau_+({pname}) nonzero")
            continue

        # Clear denominators
        numdens = []
        for kv in sorted(diag.keys()):
            d_val = diag[kv]
            if d_val == 0:
                numdens.append((Integer(0), Integer(1)))
            else:
                n, d = fraction(cancel(d_val))
                numdens.append((expand(n), expand(d)))

        if all(nd[0] == 0 for nd in numdens):
            lines.append(f"/-- τ₊ vanishing in ∂/∂{pname} (all diag zero). -/")
            lines.append(f"theorem tau_plus_g{g}_{pname}_vanishes {param_decl} :")
            lines.append(f"    (0 : ℤ) = 0 := by ring")
            lines.append("")
            continue

        # Find LCD
        cd = Integer(1)
        for n_val, d_val in numdens:
            if d_val != 1 and d_val != 0:
                cd = sp.lcm(cd, d_val)

        # Clear denominators
        nums = []
        for n_val, d_val in numdens:
            if d_val == 0 or n_val == 0:
                nums.append(Integer(0))
            else:
                nums.append(expand(n_val * cancel(cd / d_val)))

        total = expand(sum(nums))
        assert total == 0, f"Sum nonzero for g={g}, {pname}: {total}"

        num_strs = [to_lean_poly(nv, list(params)) for nv in nums]
        n_chars = sum(len(s) for s in num_strs)

        lines.append(f"/-- τ₊ vanishing in ∂/∂{pname}: sum of V₊ diagonal × lcd = 0.")
        lines.append(f"    {g} terms, {n_chars} characters in polynomial expressions. -/")
        lines.append(f"theorem tau_plus_g{g}_{pname}_vanishes {param_decl} :")
        lines.append(f"    ({num_strs[0]})")
        for ns in num_strs[1:]:
            lines.append(f"    + ({ns})")
        lines.append(f"    = 0 := by ring")
        lines.append("")

    with open(filename, 'w') as fh:
        fh.write("\n".join(lines))
    print(f"  Lean fragment written to {filename} ({len(lines)} lines)")
    return lines


if __name__ == "__main__":
    g = int(sys.argv[1]) if len(sys.argv) > 1 else 5

    print(f"Computing genus {g}...")
    t0 = time.time()
    results, params = compute_trace_symbolic(g)
    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")

    all_zero = all(r['tau'] == 0 for r in results.values())
    print(f"All traces zero: {all_zero}")

    if all_zero:
        fname = f"{LEAN_OUTPUT_DIR}trace_g{g}.lean" if 'LEAN_OUTPUT_DIR' in dir() else f"trace_g{g}.lean"
        fname = f"/Users/quantmann/FoundationRelativity/paper 92/trace_g{g}.lean"
        emit_lean_for_genus(g, results, params, fname)
