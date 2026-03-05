#!/usr/bin/env python3
"""
sweep_cm_types.py — Sweep all 16 CM types for Q(zeta_15)
Optimized: precompute all C(8,4)=70 wedge-4 dual vectors once,
then select the correct 34 non-(2,2) quads per CM type.
"""
import sys
from itertools import combinations, product
from sympy import Matrix, Rational, eye, Symbol, Poly, cyclotomic_poly, rem
import sympy

z = Symbol('z')
PHI15 = Poly(cyclotomic_poly(15, z), z, domain='QQ')
N_H1 = 8
ALL_EMBEDDINGS = [1, 2, 4, 7, 8, 11, 13, 14]

def poly_red(p):
    return rem(Poly(p, z, domain='QQ'), PHI15, z)

def poly_mul(a, b):
    return poly_red(a * b)

def poly_coeffs(p, deg=8):
    p_reduced = poly_red(p)
    d = p_reduced.as_dict()
    return [Rational(d.get((i,), 0)) for i in range(deg)]

def substitute_z_power(poly_list, k):
    result = []
    for p in poly_list:
        d = p.as_dict()
        new_poly = Poly(0, z, domain='QQ')
        for (exp,), coeff in d.items():
            new_poly += coeff * Poly(z**(exp * k), z, domain='QQ')
        result.append(poly_red(new_poly))
    return result

def poly_det(rows, n):
    if n == 1:
        return rows[0][0]
    if n == 2:
        return poly_red(poly_mul(rows[0][0], rows[1][1]) - poly_mul(rows[0][1], rows[1][0]))
    det = Poly(0, z, domain='QQ')
    for j in range(n):
        minor_rows = []
        for i in range(1, n):
            minor_rows.append([rows[i][k] for k in range(n) if k != j])
        sub_det = poly_det(minor_rows, n - 1)
        sign = (-1) ** j
        if sign == 1:
            det = poly_red(det + poly_mul(rows[0][j], sub_det))
        else:
            det = poly_red(det - poly_mul(rows[0][j], sub_det))
    return det

def permutation_sign(perm):
    n = len(perm)
    inversions = 0
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inversions += 1
    return (-1) ** inversions


def main():
    print("Sweeping all 16 CM types for Q(zeta_15)")
    print("Conjugate pairs: {1,14}, {2,13}, {4,11}, {7,8}")
    print()

    # --- Precompute eigenvectors for all 8 embeddings ---
    base = [poly_red(Poly(z**k, z, domain='QQ')) for k in range(N_H1)]
    left_eig = {}
    for k in ALL_EMBEDDINGS:
        left_eig[k] = substitute_z_power(base, k)
    print("[OK] Eigenvectors for all 8 embeddings computed")

    # --- Precompute ALL C(8,4)=70 wedge-4 dual vectors ---
    basis4 = list(combinations(range(N_H1), 4))
    dim4 = 70
    all_embedding_quads = list(combinations(ALL_EMBEDDINGS, 4))
    assert len(all_embedding_quads) == 70

    quad_rows = {}
    for qi, quad in enumerate(all_embedding_quads):
        vecs = [left_eig[a] for a in quad]
        dual_vec = []
        for b_idx, b in enumerate(basis4):
            rows = []
            for i in range(4):
                row = [vecs[i][b[j]] for j in range(4)]
                rows.append(row)
            dual_vec.append(poly_det(rows, 4))

        rows_for_quad = []
        for zexp in range(8):
            row = []
            for comp_idx in range(dim4):
                c = poly_coeffs(dual_vec[comp_idx])
                row.append(c[zexp])
            rows_for_quad.append(row)
        quad_rows[quad] = rows_for_quad

        if (qi + 1) % 10 == 0:
            print(f"  [{qi+1}/70] wedge-4 dual vectors computed...")

    print("[OK] All 70 wedge-4 dual vectors precomputed")

    # --- Precompute C(8,2)=28 wedge-2 dual vectors ---
    basis2 = list(combinations(range(N_H1), 2))
    dim2 = 28
    all_embedding_pairs = list(combinations(ALL_EMBEDDINGS, 2))

    pair_rows = {}
    for pair in all_embedding_pairs:
        (a, b) = pair
        ua = left_eig[a]
        ub = left_eig[b]
        dual_vec = []
        for (i, j) in basis2:
            coeff = poly_red(poly_mul(ua[i], ub[j]) - poly_mul(ua[j], ub[i]))
            dual_vec.append(coeff)
        rows_for_pair = []
        for zexp in range(8):
            row = []
            for comp_idx in range(dim2):
                c = poly_coeffs(dual_vec[comp_idx])
                row.append(c[zexp])
            rows_for_pair.append(row)
        pair_rows[pair] = rows_for_pair

    print("[OK] All 28 wedge-2 dual vectors precomputed")
    print()

    # --- Sweep CM types ---
    conj_pairs = [(1, 14), (2, 13), (4, 11), (7, 8)]
    results = []

    for choices in product([0, 1], repeat=4):
        cm_phi = sorted([conj_pairs[i][choices[i]] for i in range(4)])
        cm_phi_bar = sorted([15 - a for a in cm_phi])
        cm_phi_set = set(cm_phi)
        cm_phi_bar_set = set(cm_phi_bar)

        # --- H^{1,1}: non-(1,1) pairs ---
        non_11 = []
        for pair in all_embedding_pairs:
            a, b = pair
            if (a in cm_phi_set and b in cm_phi_set) or \
               (a in cm_phi_bar_set and b in cm_phi_bar_set):
                non_11.append(pair)

        h11_rows = []
        for pair in non_11:
            h11_rows.extend(pair_rows[pair])
        if h11_rows:
            C_h11 = Matrix(h11_rows)
            ns_basis = C_h11.nullspace()
        else:
            ns_basis = []
            for i in range(dim2):
                ei = Matrix.zeros(dim2, 1)
                ei[i] = 1
                ns_basis.append(ei)
        ns_dim = len(ns_basis)

        # --- H^{2,2}: non-(2,2) quads ---
        non_22 = []
        for quad in all_embedding_quads:
            n_phi = sum(1 for a in quad if a in cm_phi_set)
            if n_phi != 2:
                non_22.append(quad)

        h22_rows = []
        for quad in non_22:
            h22_rows.extend(quad_rows[quad])
        C_h22 = Matrix(h22_rows)
        h22_basis = C_h22.nullspace()
        h22_dim = len(h22_basis)

        if h22_dim == 0:
            print(f"  Phi={cm_phi}  NS={ns_dim}  H22=0  Div=0  Exotic=0")
            results.append((cm_phi, ns_dim, 0, 0, 0))
            continue

        # --- Divisor subspace ---
        idx4 = {b: i for i, b in enumerate(basis4)}
        ns_vecs = [[v[i] for i in range(28)] for v in ns_basis]

        div_vecs = []
        for a in range(ns_dim):
            for b in range(a+1, ns_dim):
                v = Matrix.zeros(70, 1)
                for i_idx, I_set in enumerate(basis2):
                    alpha = ns_vecs[a][i_idx]
                    if alpha == 0:
                        continue
                    for j_idx, J_set in enumerate(basis2):
                        beta = ns_vecs[b][j_idx]
                        if beta == 0:
                            continue
                        if set(I_set) & set(J_set):
                            continue
                        merged = tuple(sorted(set(I_set) | set(J_set)))
                        if len(merged) != 4:
                            continue
                        perm = list(I_set) + list(J_set)
                        sign = permutation_sign(perm)
                        if merged in idx4:
                            v[idx4[merged]] += alpha * beta * sign
                div_vecs.append(v)

        if div_vecs:
            Div_mat = Matrix.hstack(*div_vecs)
            div_basis_raw = Div_mat.columnspace()
            div_dim = len(div_basis_raw)
        else:
            div_basis_raw = []
            div_dim = 0

        # Intersection with H^{2,2}
        H22_mat = Matrix.hstack(*h22_basis)
        h22_rank = H22_mat.rank()
        div_in_h22 = []
        for v in div_basis_raw:
            aug = Matrix.hstack(H22_mat, v)
            if aug.rank() == h22_rank:
                div_in_h22.append(v)
        div_h22_dim = len(div_in_h22)

        # Cup product (same for all CM types — precompute outside loop if desired)
        full_set = set(range(N_H1))
        Cup = Matrix.zeros(70, 70)
        for i, I_set in enumerate(basis4):
            complement = tuple(sorted(full_set - set(I_set)))
            if complement in idx4:
                j = idx4[complement]
                perm = list(I_set) + list(complement)
                sign = permutation_sign(perm)
                Cup[i, j] = sign

        # Exotic
        if div_h22_dim > 0:
            constraint_cols = []
            for d in div_in_h22:
                col = H22_mat.T * Cup * d
                constraint_cols.append(col)
            Constraint = Matrix.hstack(*constraint_cols).T
            exotic_alpha = Constraint.nullspace()
        else:
            exotic_alpha = []
            for i in range(h22_dim):
                ei = Matrix.zeros(h22_dim, 1)
                ei[i] = 1
                exotic_alpha.append(ei)

        exotic_dim = len(exotic_alpha)
        tag = " *** EXOTIC ***" if exotic_dim > 0 else ""
        print(f"  Phi={cm_phi}  NS={ns_dim}  H22={h22_dim}  Div={div_h22_dim}  Exotic={exotic_dim}{tag}")
        results.append((cm_phi, ns_dim, h22_dim, div_h22_dim, exotic_dim))

    print()
    exotic_found = [r for r in results if r[4] > 0]
    if exotic_found:
        print(f"FOUND {len(exotic_found)} CM type(s) with exotic classes:")
        for phi, ns, h22, div, ex in exotic_found:
            print(f"  Phi={phi}  NS={ns}  H22={h22}  Div={div}  Exotic={ex}")
    else:
        print("NO CM type for Q(zeta_15) produces exotic Weil classes.")
        print("Need a different CM field.")


if __name__ == '__main__':
    main()
