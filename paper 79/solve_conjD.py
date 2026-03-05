#!/usr/bin/env python3
"""
solve_conjD.py — Asymmetric Offloading Script for Paper 79
Standard Conjecture D for Abelian Fourfolds of Weil Type Is Constructively Decidable

ALGORITHM: Dual Eigenvector Method over Q[z]/Phi_15(z)
  - No complex numbers, no matrix inversions over algebraic fields
  - Left eigenvectors annihilate non-(p,p) components
  - Cyclotomic coefficient extraction yields rational linear equations
  - All computation strictly over Q

Pipeline:
  1. CM action: companion matrix M of Phi_15 on Q^8
  2. Right/left eigenvectors over Q(z) = Q[z]/Phi_15(z)
  3. Hodge (1,1) via dual annihilation of non-(1,1) in wedge^2 -> NS(A)_Q
  4. Hodge (2,2) via dual annihilation of non-(2,2) in wedge^4
  5. Divisor subspace: wedge products of NS(A)_Q basis vectors
  6. Exotic subspace: orthogonal complement of divisors in H^{2,2} w.r.t. cup product
  7. Gram matrix, Sylvester's criterion, Lean emission

Usage:  python3 solve_conjD.py
Output: P79_ConjD/Papers/P79_ConjD/ConjDData.lean
"""

import sys
from itertools import combinations
from sympy import (
    Matrix, Rational, eye, zeros, Symbol, Poly, cyclotomic_poly, rem
)
import sympy

# ============================================================
# CONFIGURATION
# ============================================================
LEAN_OUTPUT = "P79_ConjD/Papers/P79_ConjD/ConjDData.lean"
N_H1 = 8  # dim H^1(A, Q)

# CM type for Q(zeta_15): Phi = {1,2,4,7}, Phi_bar = {8,11,13,14}
CM_PHI = [1, 2, 4, 7]
CM_PHI_BAR = [8, 11, 13, 14]
ALL_EMBEDDINGS = sorted(CM_PHI + CM_PHI_BAR)  # {1,2,4,7,8,11,13,14}


# ============================================================
# POLYNOMIAL ARITHMETIC IN Q[z] / Phi_15(z)
# ============================================================
z = Symbol('z')
PHI15 = Poly(cyclotomic_poly(15, z), z, domain='QQ')

def poly_red(p):
    """Reduce polynomial p modulo Phi_15(z) over Q."""
    return rem(Poly(p, z, domain='QQ'), PHI15, z)

def poly_mul(a, b):
    """Multiply two elements of Q[z]/Phi_15 and reduce."""
    return poly_red(a * b)

def poly_coeffs(p, deg=8):
    """Extract coefficient vector [c0, c1, ..., c7] from polynomial in z."""
    p_reduced = poly_red(p)
    d = p_reduced.as_dict()
    return [Rational(d.get((i,), 0)) for i in range(deg)]


# ============================================================
# STEP 1: COMPANION MATRIX AND EIGENVECTORS
# ============================================================
def build_companion():
    """Build the 8x8 rational companion matrix of Phi_15(z)."""
    # Phi_15(z) = z^8 - z^7 + z^5 - z^4 + z^3 - z + 1
    coeffs = PHI15.all_coeffs()  # [1, -1, 0, 1, -1, 1, 0, -1, 1] (z^8 down to z^0)
    n = N_H1
    M = Matrix.zeros(n, n)
    for i in range(n - 1):
        M[i + 1, i] = 1
    for i in range(n):
        M[i, n - 1] = -coeffs[n - i]  # -c_i where Phi = z^8 + c7*z^7 + ... + c0
    return M


def right_eigenvector_base(M):
    """
    Right eigenvector of companion matrix M for eigenvalue z (formal).
    For companion matrix of Phi_15, the right eigenvector for eigenvalue z is:
      v = [1, z, z^2, ..., z^7]^T  (reduced mod Phi_15)
    Returns list of 8 polynomials in z.
    """
    return [poly_red(Poly(z**k, z, domain='QQ')) for k in range(N_H1)]


def left_eigenvector_base(M):
    """
    Left eigenvector u such that u^T M = z u^T.
    For the companion matrix, u^T = [p_0, p_1, ..., p_7] where
    p_i are determined by the recurrence from u^T M = z u^T.

    We solve: u_j = sum_i u_i M_{i,j} / z ... actually let's derive directly.
    u^T M = z u^T means for each column j of M:
      sum_i u_i M_{ij} = z * u_j

    For the companion matrix (subdiagonal 1s, last column = -coeffs):
      Column j (0 <= j < 7): M_{j+1, j} = 1, rest 0 except last col
        => u_{j+1} = z * u_j  for j = 0,...,6
      Column 7: M_{i, 7} = -c_i
        => sum_i u_i (-c_i) = z * u_7

    From u_{j+1} = z u_j: u_j = z^j u_0.
    Set u_0 = 1: u_j = z^j.
    Check column 7: sum_i z^i (-c_i) = -Phi_15(z) + z^8 = z^8 (since Phi_15(z)=0 mod Phi_15).
    And z * u_7 = z * z^7 = z^8. Check.

    So left eigenvector = right eigenvector = [1, z, z^2, ..., z^7] for
    the companion matrix. They coincide because companion matrices are
    non-derogatory.
    """
    return [poly_red(Poly(z**k, z, domain='QQ')) for k in range(N_H1)]


def substitute_z_power(poly_list, k):
    """
    Given polynomials in z, substitute z -> z^k (mod Phi_15).
    This gives eigenvectors for eigenvalue zeta^k.
    """
    result = []
    for p in poly_list:
        # Replace z with z^k
        d = p.as_dict()
        new_poly = Poly(0, z, domain='QQ')
        for (exp,), coeff in d.items():
            new_poly += coeff * Poly(z**(exp * k), z, domain='QQ')
        result.append(poly_red(new_poly))
    return result


# ============================================================
# STEP 2: WEDGE PRODUCT INFRASTRUCTURE
# ============================================================
def wedge_basis(n, k):
    """Return sorted list of k-element subsets of {0,...,n-1}."""
    return list(combinations(range(n), k))

def wedge_index_map(basis):
    """Map tuple -> index."""
    return {b: i for i, b in enumerate(basis)}

def permutation_sign(perm):
    """Sign of permutation that sorts perm to ascending order."""
    n = len(perm)
    arr = list(perm)
    inversions = 0
    for i in range(n):
        for j in range(i + 1, n):
            if arr[i] > arr[j]:
                inversions += 1
    return (-1) ** inversions


def wedge_vectors(vecs):
    """
    Given a list of vectors [v_1, ..., v_k] where each v_i is a list of
    polynomials in z (length N_H1), compute their wedge product as a vector
    in wedge^k(Q(z)^8).

    Returns a list of polynomials (one per basis element of wedge^k).
    """
    k = len(vecs)
    n = N_H1
    basis = wedge_basis(n, k)
    result = [Poly(0, z, domain='QQ')] * len(basis)
    idx = wedge_index_map(basis)

    for b_idx, b in enumerate(basis):
        # The coefficient of e_{b[0]} ^ ... ^ e_{b[k-1]} is
        # det of the k x k matrix [v_i[b[j]]]
        rows = []
        for i in range(k):
            row = [vecs[i][b[j]] for j in range(k)]
            rows.append(row)
        # Compute determinant over Q[z]/Phi_15
        det = poly_det(rows, k)
        result[b_idx] = det
    return result


def poly_det(rows, n):
    """Determinant of n x n matrix of polynomials, using Leibniz formula for small n."""
    if n == 1:
        return rows[0][0]
    if n == 2:
        return poly_red(poly_mul(rows[0][0], rows[1][1]) - poly_mul(rows[0][1], rows[1][0]))
    # General case: expansion along first row
    det = Poly(0, z, domain='QQ')
    for j in range(n):
        # Minor: delete row 0, column j
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


# ============================================================
# STEP 3: BUILD RATIONAL CONSTRAINT MATRICES
# ============================================================
def build_hodge_constraints_h2(left_eigvecs_by_embedding):
    """
    Build rational linear equations for H^{1,1} cap Q^28.

    Non-(1,1) pairs: both indices in Phi or both in Phi_bar.
    For each such pair {a,b}, compute u_a ^ u_b (left dual 2-vector in Q(z)^28).
    Dot product with x in Q^28, extract 8 coefficients -> 8 rational equations.
    """
    basis2 = wedge_basis(N_H1, 2)
    dim2 = len(basis2)  # 28

    # Non-(1,1) pairs: (2,0) has both from Phi, (0,2) has both from Phi_bar
    non_11_pairs = []
    for pair in combinations(CM_PHI, 2):         # (2,0) type
        non_11_pairs.append(pair)
    for pair in combinations(CM_PHI_BAR, 2):      # (0,2) type
        non_11_pairs.append(pair)
    # C(4,2) + C(4,2) = 6 + 6 = 12 pairs

    # For each pair, compute wedge of left eigenvectors
    rows = []
    for (a, b) in non_11_pairs:
        ua = left_eigvecs_by_embedding[a]
        ub = left_eigvecs_by_embedding[b]
        # Wedge u_a ^ u_b: for each basis element e_{i,j} of wedge^2,
        # coefficient = ua[i]*ub[j] - ua[j]*ub[i]
        dual_vec = []
        for (i, j) in basis2:
            coeff = poly_red(poly_mul(ua[i], ub[j]) - poly_mul(ua[j], ub[i]))
            dual_vec.append(coeff)

        # Extract 8 rational equations from each dual vector component
        for comp_idx in range(dim2):
            coeffs_list = poly_coeffs(dual_vec[comp_idx])
            for c in coeffs_list:
                pass  # We need: for each x in Q^28, sum_comp x[comp] * dual_vec[comp] = 0
        # Actually: the constraint is <dual_vec, x> = 0 in Q(z).
        # This is sum_{comp} x[comp] * dual_vec[comp] = 0 as polynomial in z.
        # Since x is rational, x[comp] are rationals, so:
        # sum_{comp} x[comp] * dual_vec[comp] = polynomial in z
        # Setting each of 8 z-coefficients to 0 gives 8 equations.
        for zexp in range(8):
            row = []
            for comp_idx in range(dim2):
                c = poly_coeffs(dual_vec[comp_idx])
                row.append(c[zexp])
            rows.append(row)

    # Constraint matrix: (12*8) x 28 = 96 x 28
    return Matrix(rows)


def build_hodge_constraints_h4(left_eigvecs_by_embedding):
    """
    Build rational linear equations for H^{2,2} cap Q^70.

    Non-(2,2) quadruples: NOT exactly 2 from Phi and 2 from Phi_bar.
    Types: (4,0), (3,1), (1,3), (0,4).
    """
    basis4 = wedge_basis(N_H1, 4)
    dim4 = len(basis4)  # 70

    non_22_quads = []

    # (4,0): all 4 from Phi
    for quad in combinations(CM_PHI, 4):          # C(4,4) = 1
        non_22_quads.append(quad)

    # (0,4): all 4 from Phi_bar
    for quad in combinations(CM_PHI_BAR, 4):      # C(4,4) = 1
        non_22_quads.append(quad)

    # (3,1): 3 from Phi, 1 from Phi_bar
    for triple in combinations(CM_PHI, 3):        # C(4,3) = 4
        for single in CM_PHI_BAR:                 # 4
            non_22_quads.append(tuple(sorted(list(triple) + [single])))
    # 4*4 = 16

    # (1,3): 1 from Phi, 3 from Phi_bar
    for single in CM_PHI:                         # 4
        for triple in combinations(CM_PHI_BAR, 3):# C(4,3) = 4
            non_22_quads.append(tuple(sorted([single] + list(triple))))
    # 4*4 = 16

    # Total: 1 + 1 + 16 + 16 = 34
    assert len(non_22_quads) == 34, f"Expected 34 non-(2,2) quads, got {len(non_22_quads)}"

    rows = []
    for quad in non_22_quads:
        # Compute wedge of 4 left eigenvectors u_{quad[0]} ^ ... ^ u_{quad[3]}
        vecs = [left_eigvecs_by_embedding[a] for a in quad]
        dual_vec = wedge_vectors(vecs)  # length 70, each a polynomial in z

        # <dual_vec, x> = 0 for rational x; extract 8 z-coefficients per equation
        for zexp in range(8):
            row = []
            for comp_idx in range(dim4):
                c = poly_coeffs(dual_vec[comp_idx])
                row.append(c[zexp])
            rows.append(row)

    # Constraint matrix: (34*8) x 70 = 272 x 70
    return Matrix(rows)


# ============================================================
# STEP 4: CUP PRODUCT MATRIX
# ============================================================
def build_cup_product_matrix():
    """
    Build the 70x70 cup product matrix for wedge^4 Q^8 x wedge^4 Q^8 -> wedge^8 Q^8 ~ Q.
    <e_I, e_J> = sign(I ++ J -> sorted) if I union J = {0,...,7}, else 0.
    """
    basis4 = wedge_basis(N_H1, 4)
    idx = wedge_index_map(basis4)
    dim = len(basis4)
    Cup = Matrix.zeros(dim, dim)
    full_set = set(range(N_H1))

    for i, I_set in enumerate(basis4):
        complement = tuple(sorted(full_set - set(I_set)))
        if complement in idx:
            j = idx[complement]
            perm = list(I_set) + list(complement)
            sign = permutation_sign(perm)
            Cup[i, j] = sign

    return Cup


# ============================================================
# STEP 5: DIVISOR SUBSPACE
# ============================================================
def build_divisor_subspace(ns_basis_vecs):
    """
    Compute divisor subspace in wedge^4: wedge products of pairs of NS(A)_Q basis vectors.

    ns_basis_vecs: list of vectors in Q^28 (NS basis in wedge^2).
    Returns: list of vectors in Q^70 (divisor images in wedge^4).
    """
    basis2 = wedge_basis(N_H1, 2)
    basis4 = wedge_basis(N_H1, 4)
    idx4 = wedge_index_map(basis4)
    dim4 = len(basis4)

    div_vectors = []
    ns_count = len(ns_basis_vecs)

    for a in range(ns_count):
        for b in range(a + 1, ns_count):
            # Wedge product of two vectors in wedge^2 -> wedge^4
            # v_a = sum_I alpha_I e_I,  v_b = sum_J beta_J e_J
            # v_a ^ v_b = sum_{I,J disjoint} alpha_I beta_J sign(I,J) e_{I union J}
            v = Matrix.zeros(dim4, 1)
            for i_idx, I_set in enumerate(basis2):
                alpha = ns_basis_vecs[a][i_idx]
                if alpha == 0:
                    continue
                for j_idx, J_set in enumerate(basis2):
                    beta = ns_basis_vecs[b][j_idx]
                    if beta == 0:
                        continue
                    # Check disjoint
                    if set(I_set) & set(J_set):
                        continue
                    merged = tuple(sorted(set(I_set) | set(J_set)))
                    if len(merged) != 4:
                        continue
                    perm = list(I_set) + list(J_set)
                    sign = permutation_sign(perm)
                    if merged in idx4:
                        v[idx4[merged]] += alpha * beta * sign
            div_vectors.append(v)

    return div_vectors


# ============================================================
# MAIN
# ============================================================
def main():
    print("Paper 79: Standard Conjecture D for Weil Fourfolds — Constructively Decidable")
    print("Algorithm: Dual Eigenvector Method over Q[z]/Phi_15(z)")
    print()

    # --- Step 1: Companion matrix ---
    M = build_companion()
    assert M**15 == eye(N_H1), "FATAL: M^15 != I"
    print("[OK] Companion matrix M verified: M^15 = I")

    # --- Step 2: Eigenvectors for all embeddings ---
    # Right eigenvector for eigenvalue z: [1, z, z^2, ..., z^7]
    # For eigenvalue z^k: substitute z -> z^k
    right_eig = {}
    left_eig = {}
    base_right = right_eigenvector_base(M)
    base_left = left_eigenvector_base(M)
    for k in ALL_EMBEDDINGS:
        right_eig[k] = substitute_z_power(base_right, k)
        left_eig[k] = substitute_z_power(base_left, k)
    print(f"[OK] Eigenvectors computed for embeddings {ALL_EMBEDDINGS}")

    # --- Step 3: Rational H^{1,1} (NS group) ---
    print("[..] Building H^{1,1} constraints (96 x 28)...")
    C_h11 = build_hodge_constraints_h2(left_eig)
    assert C_h11.shape == (96, 28), f"Bad shape: {C_h11.shape}"
    ns_basis = C_h11.nullspace()
    ns_dim = len(ns_basis)
    print(f"[OK] NS(A)_Q dimension = {ns_dim}")

    # --- Step 4: Rational H^{2,2} ---
    print("[..] Building H^{2,2} constraints (272 x 70)...")
    C_h22 = build_hodge_constraints_h4(left_eig)
    assert C_h22.shape == (272, 70), f"Bad shape: {C_h22.shape}"
    h22_basis = C_h22.nullspace()
    h22_dim = len(h22_basis)
    print(f"[OK] H^{{2,2}} cap Q^70 dimension = {h22_dim}")

    if h22_dim == 0:
        print("FATAL: Hodge (2,2) subspace is trivial.")
        sys.exit(1)

    # --- Step 5: Cup product ---
    Cup = build_cup_product_matrix()
    print("[OK] Cup product matrix (70x70) built")

    # --- Step 6: Divisor subspace ---
    print(f"[..] Computing divisor subspace from {ns_dim} NS generators...")
    # Convert NS basis from sympy column vectors to lists
    ns_vecs = []
    for v in ns_basis:
        ns_vecs.append([v[i] for i in range(28)])
    div_vecs = build_divisor_subspace(ns_vecs)
    print(f"[..] {len(div_vecs)} raw divisor products computed")

    if div_vecs:
        Div_mat = Matrix.hstack(*div_vecs)
        div_basis = Div_mat.columnspace()
        div_dim = len(div_basis)
    else:
        div_basis = []
        div_dim = 0
    print(f"[OK] Divisor subspace in H^4: dim = {div_dim}")

    # Project divisor basis into H^{2,2}: find intersection
    H22_mat = Matrix.hstack(*h22_basis)  # 70 x h22_dim

    # Divisor vectors that lie in H^{2,2}:
    # v is in colspace(H22) iff rank([H22 | v]) = rank(H22)
    h22_rank = H22_mat.rank()
    div_in_h22 = []
    for v in div_basis:
        aug = Matrix.hstack(H22_mat, v)
        if aug.rank() == h22_rank:
            div_in_h22.append(v)

    div_h22_dim = len(div_in_h22)
    print(f"[OK] Divisor subspace in H^{{2,2}}: dim = {div_h22_dim}")

    # --- Step 7: Exotic subspace ---
    # Exotic = orthogonal complement of div_in_h22 inside H^{2,2} w.r.t. Cup
    # Express everything in H^4 coordinates.
    # x in H^{2,2}: x = H22_mat * alpha for alpha in Q^{h22_dim}
    # Constraint: x^T Cup d = 0 for all d in div_in_h22
    # => alpha^T (H22_mat^T Cup d) = 0

    if div_h22_dim > 0:
        # Build constraint matrix on alpha coordinates
        constraint_cols = []
        for d in div_in_h22:
            col = H22_mat.T * Cup * d
            constraint_cols.append(col)
        Constraint = Matrix.hstack(*constraint_cols).T  # div_h22_dim x h22_dim
        exotic_alpha_basis = Constraint.nullspace()
    else:
        # No divisors in H22: entire H22 is exotic
        exotic_alpha_basis = []
        for i in range(h22_dim):
            ei = Matrix.zeros(h22_dim, 1)
            ei[i] = 1
            exotic_alpha_basis.append(ei)

    exotic_dim = len(exotic_alpha_basis)
    print(f"[OK] Exotic subspace dimension = {exotic_dim}")

    if exotic_dim == 0:
        print("FATAL: Exotic subspace is trivial. Fourfold has no exotic Weil classes.")
        sys.exit(1)

    # --- Step 8: Gram matrix on exotic subspace ---
    # B = H22_mat * [alpha_1 | ... | alpha_N]  (70 x exotic_dim, columns in H^4)
    Alpha = Matrix.hstack(*exotic_alpha_basis)  # h22_dim x exotic_dim
    B = H22_mat * Alpha  # 70 x exotic_dim
    G = B.T * Cup * B  # exotic_dim x exotic_dim

    # Simplify
    for i in range(exotic_dim):
        for j in range(exotic_dim):
            G[i, j] = sympy.nsimplify(sympy.Rational(G[i, j]))

    # Sign convention: make G[0,0] > 0
    if G[0, 0] < 0:
        G = -G
        print("[..] Flipped sign: using -G for positive definiteness")

    # --- Step 9: Sylvester's criterion ---
    minors = []
    all_positive = True
    for k in range(1, exotic_dim + 1):
        m = G[:k, :k].det()
        m = sympy.nsimplify(sympy.Rational(m))
        minors.append(m)
        if m <= 0:
            all_positive = False

    if all_positive:
        print(f"[OK] ALL {exotic_dim} leading principal minors are strictly positive")
        print(f"[OK] Gram matrix is POSITIVE DEFINITE")
        def_type = "positive"
    else:
        print(f"[!!] NOT all minors positive — investigating...")
        for k, m in enumerate(minors, 1):
            sign_str = "+" if m > 0 else ("-" if m < 0 else "0")
            print(f"     Minor {k}: {m} ({sign_str})")
        def_type = "indefinite"

    # --- Step 10: Emit Lean ---
    emit_lean(G, minors, exotic_dim, def_type, h22_dim, div_h22_dim, ns_dim)

    # Summary
    print()
    print("=" * 60)
    print(f"[SUCCESS] H^{{1,1}} dim = {ns_dim}, H^{{2,2}} dim = {h22_dim}, "
          f"Div dim = {div_h22_dim}, Exotic dim = {exotic_dim}")
    print(f"[SUCCESS] Definiteness: {def_type}")
    print(f"[SUCCESS] Lean file: {LEAN_OUTPUT}")
    print("=" * 60)


# ============================================================
# LEAN EMITTER
# ============================================================
def emit_lean(G, minors, N, def_type, h22_dim, div_dim, ns_dim):
    """Write ConjDData.lean with hardcoded rational data + native_decide proofs."""
    lines = []
    lines.append("/-")
    lines.append("  ConjDData.lean — Auto-generated by solve_conjD.py")
    lines.append("  Paper 79: Standard Conjecture D for Abelian Fourfolds of Weil Type Is Constructively Decidable")
    lines.append(f"")
    lines.append(f"  CM field: Q(zeta_15), simple abelian fourfold")
    lines.append(f"  NS(A)_Q dimension (H^{{1,1}} cap Q^28): {ns_dim}")
    lines.append(f"  Hodge (2,2) dimension (H^{{2,2}} cap Q^70): {h22_dim}")
    lines.append(f"  Divisor subspace in H^{{2,2}}: {div_dim}")
    lines.append(f"  Exotic subspace dimension: {N}")
    lines.append(f"  Definiteness: {def_type}")
    lines.append(f"")
    lines.append(f"  DO NOT EDIT — regenerate via: python3 solve_conjD.py")
    lines.append("-/")
    lines.append("")
    lines.append("import Mathlib")
    lines.append("")

    lines.append(f"/-- Dimension of the exotic Weil subspace. -/")
    lines.append(f"def exoticDim : Nat := {N}")
    lines.append("")

    # Minors
    lines.append(f"/-- Leading principal minors of the Gram matrix (cup product on exotic subspace). -/")
    lines.append(f"def leadingPrincipalMinors : List ℚ :=")
    minor_strs = []
    for m in minors:
        r = sympy.Rational(m)
        if r.q == 1:
            minor_strs.append(f"  {r.p}")
        else:
            minor_strs.append(f"  ({r.p} : ℚ) / {r.q}")
    lines.append("  [" + ",\n   ".join(minor_strs) + "]")
    lines.append("")

    # Decidable proof
    lines.append("/-- Sylvester's criterion: all leading principal minors are strictly positive. -/")
    lines.append("def allMinorsPositive : (leadingPrincipalMinors.all (· > 0)) = true := by")
    lines.append("  native_decide")
    lines.append("")

    # Gram matrix entries (for reference)
    lines.append(f"/-- Gram matrix entries (row-major, {N}x{N}). -/")
    lines.append(f"def gramMatrixEntries : List ℚ :=")
    entries = []
    for i in range(N):
        for j in range(N):
            r = sympy.Rational(G[i, j])
            if r.q == 1:
                entries.append(f"{r.p}")
            else:
                entries.append(f"({r.p} : ℚ) / {r.q}")
    chunk = 5
    entry_lines = []
    for k in range(0, len(entries), chunk):
        entry_lines.append("   " + ", ".join(entries[k:k+chunk]))
    lines.append("  [" + ",\n".join(entry_lines) + "]")
    lines.append("")

    with open(LEAN_OUTPUT, 'w') as f:
        f.write('\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
