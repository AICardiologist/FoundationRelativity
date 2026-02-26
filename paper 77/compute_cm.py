#!/usr/bin/env python3
"""
Compute the CM diagonalisation for Anderson's exotic Weil classes on E^4.

Steps:
  1. Enumerate 70 basis elements of Λ^4(Q^8)
  2. Compute 70x70 CM action matrix
  3. Find +1 eigenspace (dim 38)
  4. Separate Hodge (2,2) from (4,0)+(0,4) within +1 eigenspace
  5. Compute divisor (1,1) classes in Λ^2(Q^8) and their cup products
  6. Find exotic class = Hodge \ divisor products
  7. Compute cycle class vectors for generators
  8. Solve M·x = w_exotic

Output: explicit rational coefficients for the squeeze target.
"""
from fractions import Fraction
from itertools import combinations
import json

F = Fraction  # shorthand

# ============================================================
# Step 1: Basis of Λ^4(Q^8)
# ============================================================
# Basis elements indexed by 4-element subsets of {0,...,7}, sorted.
basis4 = list(combinations(range(8), 4))  # 70 elements
idx4 = {b: i for i, b in enumerate(basis4)}
assert len(basis4) == 70

# Also need Λ^2(Q^8) for divisor products
basis2 = list(combinations(range(8), 2))  # 28 elements
idx2 = {b: i for i, b in enumerate(basis2)}
assert len(basis2) == 28

# ============================================================
# Step 2: CM action on Q^8
# ============================================================
# e_0 -> -e_1,  e_1 -> e_0   (factor 0)
# e_2 -> -e_3,  e_3 -> e_2   (factor 1)
# e_4 -> -e_5,  e_5 -> e_4   (factor 2)
# e_6 -> -e_7,  e_7 -> e_6   (factor 3)

def cm_on_basis_vector(k):
    """CM action on e_k. Returns (sign, index)."""
    factor = k // 2
    coord = k % 2
    if coord == 0:
        return (-1, k + 1)  # e_{2j} -> -e_{2j+1}
    else:
        return (1, k - 1)   # e_{2j+1} -> e_{2j}

# ============================================================
# Step 3: Induced CM action on Λ^4(Q^8)
# ============================================================
def wedge_product_sign(indices):
    """Compute the sign needed to sort indices into ascending order.
    Returns (sign, sorted_tuple) or (0, None) if repeated indices."""
    lst = list(indices)
    n = len(lst)
    sign = 1
    # Bubble sort counting transpositions
    for i in range(n):
        for j in range(i + 1, n):
            if lst[i] > lst[j]:
                lst[i], lst[j] = lst[j], lst[i]
                sign *= -1
            elif lst[i] == lst[j]:
                return 0, None
    return sign, tuple(lst)

def cm_action_on_wedge(subset):
    """CM action on e_{a0} ^ e_{a1} ^ e_{a2} ^ e_{a3}.
    Returns list of (coefficient, basis_index) pairs."""
    # Apply CM to each basis vector
    images = []
    total_sign = 1
    new_indices = []
    for k in subset:
        s, j = cm_on_basis_vector(k)
        total_sign *= s
        new_indices.append(j)

    sign, sorted_idx = wedge_product_sign(new_indices)
    if sign == 0:
        return []  # zero (repeated index)

    coeff = F(total_sign * sign)
    return [(coeff, idx4[sorted_idx])]

# Build 70x70 CM matrix
cm_matrix = [[F(0)] * 70 for _ in range(70)]
for i, b in enumerate(basis4):
    result = cm_action_on_wedge(b)
    for coeff, j in result:
        cm_matrix[j][i] += coeff

# Verify M^2 = I
print("Verifying M^2 = I on Λ^4(Q^8)...")
identity_check = True
for i in range(70):
    for j in range(70):
        val = sum(cm_matrix[i][k] * cm_matrix[k][j] for k in range(70))
        expected = F(1) if i == j else F(0)
        if val != expected:
            identity_check = False
            break
print(f"  M^2 = I: {identity_check}")

# ============================================================
# Step 4: Find +1 eigenspace of CM on Λ^4
# ============================================================
# Since M^2 = I, the +1 eigenspace is ker(M - I).
# Projection onto +1 eigenspace: P = (I + M) / 2

def add_vec(v, w):
    return [v[i] + w[i] for i in range(len(v))]

def scale_vec(c, v):
    return [c * x for x in v]

# Project each basis vector onto +1 eigenspace
proj_plus = []  # rows = projected basis vectors
for i in range(70):
    # e_i projected: (e_i + M e_i) / 2
    ei = [F(0)] * 70
    ei[i] = F(1)
    mei = [cm_matrix[j][i] for j in range(70)]
    proj = scale_vec(F(1, 2), add_vec(ei, mei))
    proj_plus.append(proj)

# Find a basis for the +1 eigenspace by row reduction
def row_reduce(matrix, ncols):
    """Row-reduce a matrix over Q. Return (rref, pivot_cols)."""
    mat = [row[:] for row in matrix]
    nrows = len(mat)
    pivot_cols = []
    row_idx = 0
    for col in range(ncols):
        # Find pivot
        pivot = None
        for r in range(row_idx, nrows):
            if mat[r][col] != F(0):
                pivot = r
                break
        if pivot is None:
            continue
        # Swap
        mat[row_idx], mat[pivot] = mat[pivot], mat[row_idx]
        # Scale
        scale = F(1) / mat[row_idx][col]
        mat[row_idx] = [x * scale for x in mat[row_idx]]
        # Eliminate
        for r in range(nrows):
            if r != row_idx and mat[r][col] != F(0):
                factor = mat[r][col]
                mat[r] = [mat[r][j] - factor * mat[row_idx][j] for j in range(ncols)]
        pivot_cols.append(col)
        row_idx += 1
    return mat, pivot_cols

rref, pivots = row_reduce(proj_plus, 70)
# Non-zero rows form a basis for the +1 eigenspace
eigenspace_plus = []
for row in rref:
    if any(x != F(0) for x in row):
        eigenspace_plus.append(row)

dim_plus = len(eigenspace_plus)
print(f"\n+1 eigenspace dimension: {dim_plus}")
assert dim_plus == 38, f"Expected 38, got {dim_plus}"

# ============================================================
# Step 5: Identify (4,0)+(0,4) part
# ============================================================
# f_j = e_{2j} + i*e_{2j+1} for j=0,1,2,3
# f0^f1^f2^f3 = product of all 4 holomorphic forms
# Expand: (e0+ie1)^(e2+ie3)^(e4+ie5)^(e6+ie7)
# Real part and imaginary part are both in Λ^4(Q^8)

def expand_holomorphic_wedge():
    """Expand f0∧f1∧f2∧f3 into real and imaginary parts."""
    # Each factor contributes either e_{2j} (coeff 1) or e_{2j+1} (coeff i)
    # Total: product of 4 factors, each with 2 terms
    real_part = [F(0)] * 70
    imag_part = [F(0)] * 70

    for choice in range(16):  # 2^4 choices
        indices = []
        i_power = 0  # power of i
        for j in range(4):
            if (choice >> j) & 1:
                indices.append(2 * j + 1)  # e_{2j+1}, coefficient i
                i_power += 1
            else:
                indices.append(2 * j)  # e_{2j}, coefficient 1

        sign, sorted_idx = wedge_product_sign(indices)
        if sign == 0:
            continue

        # i^{i_power} * sign
        coeff_real = F(0)
        coeff_imag = F(0)
        ip = i_power % 4
        if ip == 0:
            coeff_real = F(sign)
        elif ip == 1:
            coeff_imag = F(sign)
        elif ip == 2:
            coeff_real = F(-sign)
        elif ip == 3:
            coeff_imag = F(-sign)

        bidx = idx4[sorted_idx]
        real_part[bidx] += coeff_real
        imag_part[bidx] += coeff_imag

    return real_part, imag_part

real_40, imag_40 = expand_holomorphic_wedge()

# Verify these are in the +1 eigenspace
def apply_cm(v):
    return [sum(cm_matrix[i][j] * v[j] for j in range(70)) for i in range(70)]

cm_real = apply_cm(real_40)
cm_imag = apply_cm(imag_40)
print(f"\nCM(real_40) == real_40: {cm_real == real_40}")
print(f"CM(imag_40) == imag_40: {cm_imag == imag_40}")

# ============================================================
# Step 6: Hodge (2,2) subspace = +1 eigenspace minus (4,0)+(0,4)
# ============================================================
# Project out the (4,0)+(0,4) part from the +1 eigenspace
# using Gram-Schmidt (with rational inner product)

def dot(v, w):
    return sum(v[i] * w[i] for i in range(len(v)))

def norm_sq(v):
    return dot(v, v)

# Orthogonalize real_40 and imag_40
v1 = real_40[:]
ns1 = norm_sq(v1)
v2 = [imag_40[i] - dot(imag_40, v1) / ns1 * v1[i] for i in range(70)]
ns2 = norm_sq(v2)

print(f"\n(4,0)+(0,4) basis norms: {ns1}, {ns2}")

# Project +1 eigenspace basis vectors to remove (4,0)+(0,4) components
hodge_candidates = []
for vec in eigenspace_plus:
    # Remove v1 and v2 components
    proj = vec[:]
    c1 = dot(proj, v1) / ns1
    proj = [proj[i] - c1 * v1[i] for i in range(70)]
    c2 = dot(proj, v2) / ns2
    proj = [proj[i] - c2 * v2[i] for i in range(70)]
    hodge_candidates.append(proj)

# Row-reduce to get basis for Hodge (2,2)
rref_hodge, pivots_hodge = row_reduce(hodge_candidates, 70)
hodge_basis = [row for row in rref_hodge if any(x != F(0) for x in row)]
dim_hodge = len(hodge_basis)
print(f"\nHodge (2,2) dimension: {dim_hodge}")
assert dim_hodge == 36, f"Expected 36, got {dim_hodge}"

# ============================================================
# Step 7: CM-invariant divisor classes in Λ^2(Q^8)
# ============================================================
# Build CM action on Λ^2(Q^8)
cm2_matrix = [[F(0)] * 28 for _ in range(28)]
for i, b in enumerate(basis2):
    # CM on e_a ^ e_b
    (s0, j0) = cm_on_basis_vector(b[0])
    (s1, j1) = cm_on_basis_vector(b[1])
    sign, sorted_idx = wedge_product_sign([j0, j1])
    if sign != 0:
        coeff = F(s0 * s1 * sign)
        cm2_matrix[idx2[sorted_idx]][i] += coeff

# +1 eigenspace of CM on Λ^2 (= divisor classes = NS ⊗ Q)
proj2_plus = []
for i in range(28):
    ei = [F(0)] * 28
    ei[i] = F(1)
    mei = [cm2_matrix[j][i] for j in range(28)]
    proj = scale_vec(F(1, 2), [ei[k] + mei[k] for k in range(28)])
    proj2_plus.append(proj)

rref2, pivots2 = row_reduce(proj2_plus, 28)
ns_basis = [row for row in rref2 if any(x != F(0) for x in row)]
dim_ns = len(ns_basis)
print(f"\nNS(E^4) ⊗ Q dimension (divisor classes in H^2): {dim_ns}")

# ============================================================
# Step 8: Cup products of divisor classes in H^4
# ============================================================
def cup_product_22_to_4(v2_a, v2_b):
    """Cup product of two Λ^2 classes to get a Λ^4 class."""
    result = [F(0)] * 70
    for i, bi in enumerate(basis2):
        if v2_a[i] == F(0):
            continue
        for j, bj in enumerate(basis2):
            if v2_b[j] == F(0):
                continue
            # bi ^ bj in Λ^4
            indices = list(bi) + list(bj)
            sign, sorted_idx = wedge_product_sign(indices)
            if sign == 0:
                continue
            coeff = v2_a[i] * v2_b[j] * F(sign)
            result[idx4[sorted_idx]] += coeff
    return result

# Generate all cup products of NS basis vectors
print("\nComputing divisor product subspace...")
div_products = []
for i in range(dim_ns):
    for j in range(i, dim_ns):
        cup = cup_product_22_to_4(ns_basis[i], ns_basis[j])
        if any(x != F(0) for x in cup):
            div_products.append(cup)

rref_div, pivots_div = row_reduce(div_products, 70)
div_basis = [row for row in rref_div if any(x != F(0) for x in row)]
dim_div = len(div_basis)
print(f"Divisor product subspace dimension in H^4: {dim_div}")

# ============================================================
# Step 9: Exotic classes = Hodge (2,2) mod divisor products
# ============================================================
# Find Hodge classes not in divisor product subspace
# Combine Hodge basis and div basis, row reduce to find the quotient

combined = div_basis + hodge_basis
rref_comb, pivots_comb = row_reduce(combined, 70)
comb_basis = [row for row in rref_comb if any(x != F(0) for x in row)]
dim_comb = len(comb_basis)
dim_exotic = dim_hodge - dim_div  # if div_basis ⊂ hodge_basis
print(f"\nCombined rank: {dim_comb}")
print(f"Exotic dimension (Hodge - div): {dim_hodge} - {dim_div} = {dim_hodge - dim_div}")

# To find an explicit exotic class, project a Hodge basis vector
# orthogonal to the divisor product subspace
# First, orthogonalize the divisor basis
def gram_schmidt(basis_vecs):
    """Gram-Schmidt over Q."""
    ortho = []
    for v in basis_vecs:
        w = v[:]
        for u in ortho:
            nu = norm_sq(u)
            if nu == F(0):
                continue
            c = dot(w, u) / nu
            w = [w[i] - c * u[i] for i in range(len(w))]
        if any(x != F(0) for x in w):
            ortho.append(w)
    return ortho

div_ortho = gram_schmidt(div_basis)
print(f"Orthogonalized divisor basis: {len(div_ortho)} vectors")

# Find Hodge vectors orthogonal to all divisor products
exotic_classes = []
for hv in hodge_basis:
    w = hv[:]
    for u in div_ortho:
        nu = norm_sq(u)
        if nu == F(0):
            continue
        c = dot(w, u) / nu
        w = [w[i] - c * u[i] for i in range(len(w))]
    if any(x != F(0) for x in w):
        exotic_classes.append(w)

rref_exotic, _ = row_reduce(exotic_classes, 70)
exotic_basis = [row for row in rref_exotic if any(x != F(0) for x in row)]
print(f"Exotic class basis dimension: {len(exotic_basis)}")

if len(exotic_basis) > 0:
    # Pick the first exotic class, clear denominators
    exotic = exotic_basis[0]
    # Find LCD
    from math import gcd
    denoms = [x.denominator for x in exotic if x != F(0)]
    lcd = denoms[0]
    for d in denoms[1:]:
        lcd = lcd * d // gcd(lcd, d)
    exotic_int = [int(x * lcd) for x in exotic]
    # Simplify by GCD
    g = abs(exotic_int[0])
    for x in exotic_int[1:]:
        if x != 0:
            g = gcd(g, abs(x))
    if g > 0:
        exotic_int = [x // g for x in exotic_int]

    print(f"\nExotic Weil class (integer coordinates, cleared denominators):")
    nonzero = [(i, exotic_int[i]) for i in range(70) if exotic_int[i] != 0]
    print(f"  Nonzero entries ({len(nonzero)}):")
    for idx_val, val in nonzero:
        print(f"    basis {basis4[idx_val]}: {val}")

    # Save for Lean
    result = {
        "dim_hodge": dim_hodge,
        "dim_ns": dim_ns,
        "dim_div": dim_div,
        "dim_exotic": len(exotic_basis),
        "exotic_vector": [str(x) for x in exotic],
        "exotic_int": exotic_int,
        "basis_labels": [list(b) for b in basis4],
    }
    with open("cm_computation_result.json", "w") as f:
        json.dump(result, f, indent=2)
    print("\nResults saved to cm_computation_result.json")
else:
    print("\nERROR: No exotic classes found!")
    print("This would contradict Anderson's theorem.")
