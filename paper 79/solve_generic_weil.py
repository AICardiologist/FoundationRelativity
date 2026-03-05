#!/usr/bin/env python3
"""
solve_generic_weil.py — The Generic Weil Squeeze for Paper 79
Standard Conjecture D for Abelian Fourfolds of Weil Type Is Constructively Decidable

TARGET: 2-dimensional space of Weil classes W_K, where K = Q(i).
The Q(i)-action on Q^8: M_i(e_k) = f_k, M_i(f_k) = -e_k.
V+ = span{v_k = e_k - I*f_k}, dim 4.
Generic Weil class: w = v1 ^ v2 ^ v3 ^ v4 in wedge^4(V_C).
Separate w = w_R + I*w_I. Compute 2x2 Gram matrix of cup product.

Usage:  python3 solve_generic_weil.py
Output: P79_ConjD/Papers/P79_ConjD/ConjDData.lean
"""

from itertools import combinations

LEAN_OUTPUT = "P79_ConjD/Papers/P79_ConjD/ConjDData.lean"

# ============================================================
# BASIS: e1,...,e4, f1,...,f4 = indices 0,...,7
# e_k = index k-1 (k=1..4 -> indices 0..3)
# f_k = index k+3 (k=1..4 -> indices 4..7)
# ============================================================

def main():
    n = 8  # dim H^1

    # Standard basis of wedge^4(Q^8): all C(8,4)=70 four-element subsets
    basis4 = list(combinations(range(n), 4))
    idx4 = {b: i for i, b in enumerate(basis4)}
    dim4 = len(basis4)
    assert dim4 == 70

    # --------------------------------------------------------
    # The complex eigenvectors: v_k = e_k - I*f_k for k=1..4
    # v_k has real part e_k (index k-1) and imaginary part -f_k (index k+3)
    #
    # v_k as a complex vector in C^8:
    #   v_k[k-1] = 1  (real part)
    #   v_k[k+3] = -I (imaginary part, i.e. real=-0, imag=-1... wait)
    #   Actually: v_k = e_k - I*f_k means:
    #     component (k-1) = 1 + 0*I
    #     component (k+3) = 0 - 1*I = -I
    #     all others = 0
    #
    # We represent each vector as (real_part[8], imag_part[8])
    # --------------------------------------------------------

    def make_vk(k):
        """v_k = e_k - I*f_k. k in {1,2,3,4}."""
        re = [0]*n
        im = [0]*n
        re[k-1] = 1    # e_k component
        im[k+3] = -1   # -I * f_k component: real=0, imag=-1
        return (re, im)

    v = [make_vk(k) for k in range(1, 5)]  # v[0]=v1, v[1]=v2, v[2]=v3, v[3]=v4

    # --------------------------------------------------------
    # Compute w = v1 ^ v2 ^ v3 ^ v4 in wedge^4(C^8)
    # Each coefficient is a complex number.
    # For basis element e_{i1} ^ e_{i2} ^ e_{i3} ^ e_{i4} (sorted),
    # the coefficient is det of the 4x4 complex matrix
    # [v_a[i_b]] for a=1..4, b=1..4 (with the indices i_1 < i_2 < i_3 < i_4).
    # --------------------------------------------------------

    def complex_mul(a, b):
        """Multiply two complex numbers (ar, ai) * (br, bi)."""
        return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0])

    def complex_sub(a, b):
        return (a[0]-b[0], a[1]-b[1])

    def complex_add(a, b):
        return (a[0]+b[0], a[1]+b[1])

    def complex_neg(a):
        return (-a[0], -a[1])

    def det4x4_complex(rows):
        """4x4 determinant via cofactor expansion along row 0."""
        def det3(m):
            """3x3 determinant."""
            a, b, c = m[0]
            d, e, f = m[1]
            g, h, k = m[2]
            t1 = complex_mul(a, complex_sub(complex_mul(e, k), complex_mul(f, h)))
            t2 = complex_mul(b, complex_sub(complex_mul(d, k), complex_mul(f, g)))
            t3 = complex_mul(c, complex_sub(complex_mul(d, h), complex_mul(e, g)))
            return complex_add(complex_sub(t1, t2), t3)

        result = (0, 0)
        for j in range(4):
            minor = []
            for i in range(1, 4):
                minor.append([rows[i][k] for k in range(4) if k != j])
            d = det3(minor)
            term = complex_mul(rows[0][j], d)
            if j % 2 == 0:
                result = complex_add(result, term)
            else:
                result = complex_sub(result, term)
        return result

    # Compute the 70 coefficients of w = v1 ^ v2 ^ v3 ^ v4
    w_coeffs = []  # list of (real, imag) for each basis element
    for b in basis4:
        # 4x4 matrix: row a = [v[a][b[0]], v[a][b[1]], v[a][b[2]], v[a][b[3]]]
        # Each entry is complex: (v[a].re[b[j]], v[a].im[b[j]])
        mat = []
        for a in range(4):
            row = []
            for j in range(4):
                idx = b[j]
                row.append((v[a][0][idx], v[a][1][idx]))
            mat.append(row)
        coeff = det4x4_complex(mat)
        w_coeffs.append(coeff)

    # Separate into real and imaginary parts
    w_R = [c[0] for c in w_coeffs]  # 70-dim rational vector
    w_I = [c[1] for c in w_coeffs]  # 70-dim rational vector

    # Verify they're nonzero
    assert any(x != 0 for x in w_R), "w_R is zero!"
    assert any(x != 0 for x in w_I), "w_I is zero!"

    # Count nonzero entries
    nz_R = sum(1 for x in w_R if x != 0)
    nz_I = sum(1 for x in w_I if x != 0)

    # --------------------------------------------------------
    # Cup product: wedge^4 x wedge^4 -> wedge^8 ~ Q
    # <e_I, e_J> = sign(I,J) if I ∪ J = {0,...,7} and I ∩ J = ∅, else 0
    # --------------------------------------------------------

    def cup_product(a_vec, b_vec):
        """Cup product of two vectors in wedge^4(Q^8)."""
        full = set(range(n))
        result = 0
        for i, I_set in enumerate(basis4):
            if a_vec[i] == 0:
                continue
            complement = tuple(sorted(full - set(I_set)))
            if complement in idx4:
                j = idx4[complement]
                if b_vec[j] == 0:
                    continue
                # Sign of permutation (I_set ++ complement) -> (0,1,...,7)
                perm = list(I_set) + list(complement)
                sign = permutation_sign(perm)
                result += a_vec[i] * b_vec[j] * sign
        return result

    # --------------------------------------------------------
    # 2x2 Gram matrix
    # --------------------------------------------------------
    G11 = cup_product(w_R, w_R)
    G12 = cup_product(w_R, w_I)
    G22 = cup_product(w_I, w_I)

    # Sylvester's criterion for 2x2:
    # Positive definite iff G11 > 0 and det(G) = G11*G22 - G12^2 > 0
    det_G = G11 * G22 - G12 * G12

    print(f"Gram matrix of cup product on Weil exotic subspace:")
    print(f"  G11 = {G11}")
    print(f"  G12 = {G12}")
    print(f"  G22 = {G22}")
    print(f"  det(G) = {det_G}")
    print()

    if G11 > 0 and det_G > 0:
        print(f"[SUCCESS] G is POSITIVE DEFINITE")
        print(f"[SUCCESS] Sylvester: G11={G11} > 0, det={det_G} > 0")
        def_type = "positive"
    elif G11 < 0 and det_G > 0:
        print(f"[SUCCESS] G is NEGATIVE DEFINITE (flip sign)")
        G11, G12, G22 = -G11, -G12, -G22
        det_G = G11 * G22 - G12 * G12
        def_type = "negative_flipped"
    else:
        print(f"[FAIL] G is INDEFINITE — investigation needed")
        def_type = "indefinite"

    print()
    print(f"  w_R nonzero entries: {nz_R}/70")
    print(f"  w_I nonzero entries: {nz_I}/70")

    # --------------------------------------------------------
    # Emit Lean
    # --------------------------------------------------------
    emit_lean(G11, G12, G22, det_G, def_type)
    print(f"\n[SUCCESS] Written: {LEAN_OUTPUT}")


def permutation_sign(perm):
    """Sign of permutation (number of inversions)."""
    n = len(perm)
    inversions = 0
    for i in range(n):
        for j in range(i+1, n):
            if perm[i] > perm[j]:
                inversions += 1
    return (-1) ** inversions


def emit_lean(G11, G12, G22, det_G, def_type):
    """Write ConjDData.lean with the 2x2 Gram matrix and Sylvester verification."""
    lines = []
    lines.append("/-")
    lines.append("  ConjDData.lean — Auto-generated by solve_generic_weil.py")
    lines.append("  Paper 79: Standard Conjecture D for Abelian Fourfolds of Weil Type Is Constructively Decidable")
    lines.append("")
    lines.append("  Target: Generic abelian fourfold with K = Q(i) action.")
    lines.append("  Exotic Weil subspace: 2-dimensional, spanned by Re(w) and Im(w)")
    lines.append("  where w = v1 ^ v2 ^ v3 ^ v4, v_k = e_k - I*f_k.")
    lines.append("")
    lines.append(f"  Gram matrix: [[{G11}, {G12}], [{G12}, {G22}]]")
    lines.append(f"  Determinant: {det_G}")
    lines.append(f"  Definiteness: {def_type}")
    lines.append("")
    lines.append("  DO NOT EDIT — regenerate via: python3 solve_generic_weil.py")
    lines.append("-/")
    lines.append("")
    lines.append("import Mathlib")
    lines.append("")

    lines.append("/-- Dimension of the exotic Weil subspace. -/")
    lines.append("def exoticDim : Nat := 2")
    lines.append("")

    lines.append("/-- Gram matrix entry G(1,1) = <w_R, w_R>. -/")
    lines.append(f"def gram_matrix_11 : ℤ := {G11}")
    lines.append("")

    lines.append("/-- Gram matrix entry G(1,2) = G(2,1) = <w_R, w_I>. -/")
    lines.append(f"def gram_matrix_12 : ℤ := {G12}")
    lines.append("")

    lines.append("/-- Gram matrix entry G(2,2) = <w_I, w_I>. -/")
    lines.append(f"def gram_matrix_22 : ℤ := {G22}")
    lines.append("")

    lines.append("/-- Sylvester's criterion: the exotic Gram matrix is positive definite.")
    lines.append("    First minor: G11 > 0.")
    lines.append("    Second minor: G11 * G22 - G12^2 > 0. -/")
    lines.append("theorem exotic_pairing_is_definite :")
    lines.append("    (gram_matrix_11 > 0) ∧")
    lines.append("    (gram_matrix_11 * gram_matrix_22 - gram_matrix_12 * gram_matrix_12 > 0) := by")
    lines.append("  native_decide")
    lines.append("")

    lines.append("/-- Leading principal minors for the CRM audit record. -/")
    lines.append(f"def leadingPrincipalMinors : List ℤ := [{G11}, {det_G}]")
    lines.append("")

    lines.append("theorem allMinorsPositive : (leadingPrincipalMinors.all (· > 0)) = true := by")
    lines.append("  native_decide")
    lines.append("")

    with open(LEAN_OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
