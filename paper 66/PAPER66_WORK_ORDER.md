# PAPER 66 WORK ORDER
## Form-Class Resolution for Non-Cyclic Cubics
### Computational Task: Identify the Arithmetic Predictor

**Date:** 2026-02-23  
**Depends on:** Paper 65 (computation complete), Papers 56–58 (h = f identity)  
**Goal:** For non-cyclic (S₃) totally real cubics, determine WHICH binary quadratic form class the Weil lattice Gram matrix belongs to, and identify the arithmetic invariant that predicts it.  
**Agent requirements:** SageMath (strongly preferred — has NumberField, BinaryQF, ClassGroup built in). Alternative: Python + sympy but much harder.

---

## 1. THE QUESTION

For cyclic cubics, the Weil lattice Gram matrix is a "scalar form" — the 𝒪_K-Hermitian pairing is rank 1, determined by a single number h, and h · Nm(𝔄) = f. The form class is trivial (it collapses to one integer).

For non-cyclic (S₃) cubics, the Gram matrix G = [[a, b], [b, c]] has a ≠ c. There is no single "h." The invariant is the GL₂(ℤ)-equivalence class of the positive-definite binary quadratic form [a, 2b, c] (in classical BQF notation: ax² + 2bxy + cy²) with discriminant (2b)² - 4ac = -4·disc(F)·|Δ_K|.

Paper 65 showed that for disc(F) = 229, K = ℚ(i) (|Δ_K| = 4), the determinant is 229·4 = 916, and there are 17 reduced forms of discriminant -4·916 = -3664. But only ONE of these is the actual Weil lattice Gram matrix. Which one?

**This work order resolves that question computationally and identifies the predictor.**

---

## 2. STRATEGY

### Phase 1: Determine the correct form class from CM theory (not by enumeration)

The Weil lattice is not an arbitrary lattice of the given determinant. It has specific structure imposed by:
- The CM type (E, Φ₀) where E = F·K
- The polarization on A × B
- The 𝒪_K-action on H⁴(X, ℤ)

This structure determines the Gram matrix UNIQUELY (up to GL₂(ℤ) equivalence). The computation should proceed FROM the CM data TO the Gram matrix, not by enumerating all possible forms.

**Method:** For each (K, F) pair:

1. Construct the CM field E = F·K (degree 6 over ℚ).
2. Compute 𝒪_E (ring of integers of E).
3. The Weil lattice W_int lives inside H⁴(X, ℤ), and its 𝒪_K-module structure is determined by the 𝒪_E-module structure of the CM abelian threefold.
4. Specifically: the Weil lattice as a ℤ-module has a Gram matrix computable from the CM period matrix and the intersection pairing.

For the FIRST PASS, we can bypass the full period matrix computation and use a shortcut:

**Shortcut via the trace form of 𝒪_F:**

The self-intersection pairing on the Weil lattice is related to the trace form of the totally real cubic F. Specifically, the Gram matrix of W_int (on the 𝒪_K-basis) should be determined by the trace form Tr_{F/ℚ}(xy) restricted to a rank-2 sublattice of 𝒪_F, twisted by the 𝒪_K-structure.

For a cyclic cubic with integral basis {1, α, α²} and trace matrix M = [Tr(eᵢeⱼ)]:
- The trace matrix M is 3×3
- The Gram matrix G of the Weil lattice is a 2×2 matrix derived from M

The derivation: the exotic Weil class w₀ lives in H²(A) ⊗ H²(B), and the intersection pairing factors through the trace form of 𝒪_E over 𝒪_K, which further factors through Tr_{F/ℚ}.

**Concrete computation for the shortcut:**

Given F with integral basis {e₁, e₂, e₃} and trace matrix M = [Tr(eᵢeⱼ)]:
- Compute the 2×2 "reduced trace form" by projecting M onto the codimension-1 sublattice orthogonal to the trace element (since the Weil class is "exotic" = orthogonal to the Lefschetz classes).
- This 2×2 form IS the Gram matrix of the Weil lattice (up to the |Δ_K| factor).

**TEST THIS ON THE KNOWN CASES:**

For F = ℚ(ζ₇ + ζ₇⁻¹) (conductor 7, cyclic):
- Integral basis: {1, α, α²} where α = 2cos(2π/7)
- Trace matrix: M = [[3, 1, -2], [1, 5, 1], [-2, 1, 5]] (from Paper 56)
- det(M) = 49 = 7²  ✓
- Reduced 2×2 form (orthogonal to trace): should give det = 49 and diagonal form (7, 0, 7|Δ_K|/...) confirming h = 7.

For F with disc = 229 (non-cyclic, x³ - 4x - 1):
- Integral basis: {1, α, α²} where α is a root of x³ - 4x - 1
- Compute trace matrix M
- Compute reduced 2×2 form
- Compare with Paper 56's reduced form [[14, 3], [3, 17]]

If the shortcut works, we can compute the Gram matrix for ALL non-cyclic cubics without period matrices.

### Phase 2: Compute Gram matrices for all non-cyclic cubics with disc ≤ 2000

Once the method is validated on known cases:

1. Enumerate all non-cyclic totally real cubics with disc(F) ≤ 2000
2. For each, compute the trace matrix M of 𝒪_F
3. Compute the reduced 2×2 Gram form G
4. Record the GL₂(ℤ) equivalence class of G
5. Pair with K = ℚ(√-d) for d = 1, 2, 3, 7 (four Heegner fields)

### Phase 3: Pattern search — identify the arithmetic predictor

For each non-cyclic F, we have:
- disc(F) (the discriminant — not a perfect square)
- The Galois closure F̃ with Gal(F̃/ℚ) = S₃
- The reduced Gram form (a, b, c) with ac - b² = disc(F)
- The Artin conductor components: disc(F) = f(χ₁)·f(χ₂)

Search for relationships:

**Candidate 1: Artin conductor decomposition.**
For S₃ cubics, the discriminant factors as disc(F) = f₁·f₂ where f₁, f₂ are the two Artin conductor components. Does the Gram form satisfy a = f₁, c = f₂ (after reduction)? Or a + c = f₁ + f₂? Or ac = f₁·f₂ + b²?

**Candidate 2: Ideal class of 𝒪_F.**
The class number h_F of the cubic field F itself (not K) determines how 𝒪_F decomposes. Does h_F predict the Gram form class?

**Candidate 3: Regulator of F.**
The regulator R_F measures the "size" of the unit group. Does R_F relate to the form entries?

**Candidate 4: Splitting behavior.**
How primes split in F determines the trace matrix entries. The splitting type of small primes (2, 3, 5, 7) in F might predict the Gram form.

**Candidate 5: Genus of the form.**
Binary quadratic forms of discriminant D are organized into genera by their values mod small primes. The genus of the Gram form might be determined by the splitting behavior of F at the same primes.

**Candidate 6: The form IS the trace form.**
The simplest possibility: the Gram matrix of the Weil lattice is exactly the 2×2 reduced trace form of 𝒪_F (projected orthogonal to the Lefschetz component). If true, this says the Weil lattice is literally the trace lattice of the cubic field, which would be a beautiful result connecting Hodge theory to algebraic number theory at the integral level.

---

## 3. STEP-BY-STEP COMPUTATION

### Step 1: Validate the trace-form shortcut

```python
# SageMath pseudocode

def trace_matrix(F):
    """Compute 3x3 trace matrix of O_F."""
    B = F.ring_of_integers().basis()
    M = matrix(ZZ, 3, 3)
    for i in range(3):
        for j in range(3):
            M[i,j] = (B[i] * B[j]).trace()
    return M

def reduced_gram_form(M):
    """Project 3x3 trace matrix to 2x2 Weil lattice Gram matrix.
    
    The Lefschetz component is spanned by the trace element e₀ = 1.
    The exotic Weil lattice is the orthogonal complement of e₀ in 
    the trace lattice.
    
    Method: Gram-Schmidt-like projection. If M = [Tr(eᵢeⱼ)] with
    e₀ = 1, then the orthogonal complement of e₀ has basis
    {e₁ - (Tr(e₁)/Tr(1))·e₀, e₂ - (Tr(e₂)/Tr(1))·e₀}
    and the 2x2 Gram matrix is the Schur complement of M[0,0] in M.
    """
    # Schur complement: G = M[1:,1:] - M[1:,0] * M[0,1:] / M[0,0]
    n = M[0,0]  # = Tr(1·1) = [F:Q] = 3
    G = matrix(QQ, 2, 2)
    for i in range(2):
        for j in range(2):
            G[i,j] = M[i+1,j+1] - M[i+1,0]*M[0,j+1] / n
    return G

# Test on known cyclic case: F = Q(zeta_7 + zeta_7^{-1})
R.<x> = QQ[]
F = NumberField(x^3 + x^2 - 2*x - 1, 'a')  # conductor 7
M = trace_matrix(F)
G = reduced_gram_form(M)
print(f"Cyclic f=7: M = {M}, det(M) = {M.det()}")
print(f"Reduced G = {G}, det(G) = {G.det()}")
# EXPECTED: det(M) = 49, G should give h = 7 somehow

# Test on known non-cyclic case: disc = 229
F2 = NumberField(x^3 - 4*x - 1, 'b')  # disc = 229
M2 = trace_matrix(F2)
G2 = reduced_gram_form(M2)
print(f"Non-cyclic disc=229: M = {M2}, det(M2) = {M2.det()}")
print(f"Reduced G = {G2}, det(G2) = {G2.det()}")
# COMPARE with Paper 56: G should be GL2(Z)-equivalent to [[14,3],[3,17]]
```

**CRITICAL VALIDATION:** If reduced_gram_form(M2) gives a matrix GL₂(ℤ)-equivalent to [[14, 3], [3, 17]] for disc = 229, the shortcut works and we can proceed at scale. If not, we need to understand what additional twisting is needed (perhaps the |Δ_K| factor, or the 𝒪_K-action).

**If the shortcut DOESN'T work directly:**
Try including the |Δ_K| factor:
- G_full = G · |Δ_K| (scale by discriminant of K)
- Or: G is the Gram matrix of the trace lattice of 𝒪_E (not 𝒪_F), where E = F·K

The CM field E = F·K has degree 6. Its trace form is 6×6. The Weil lattice sits inside this as a specific 2-dimensional sublattice determined by the CM type. Computing this sublattice requires knowing the CM type Φ₀, but for a fixed (K, F) pair, there are only finitely many CM types.

### Step 2: Scale computation

Once validated, run for all non-cyclic cubics:

```python
# Enumerate non-cyclic totally real cubics with disc ≤ 2000
cubics = []
for F in NumberFields(degree=3, disc_upper=2000):
    if F.is_totally_real() and not F.discriminant().is_square():
        cubics.append(F)

results = []
for F in cubics:
    disc_F = F.discriminant()
    M = trace_matrix(F)
    G = reduced_gram_form(M)
    
    # Reduce the form
    Q = BinaryQF(G[0,0], 2*G[0,1], G[1,1])  # classical BQF notation
    Q_red = Q.reduced_form()
    
    # Artin conductor decomposition
    # disc(F) = f1 * f2 for S3 cubics
    # f1, f2 are the Artin conductor components
    f1, f2 = artin_conductor_components(F)  # need to implement
    
    results.append({
        'disc': disc_F,
        'poly': F.defining_polynomial(),
        'trace_matrix': M,
        'gram_2x2': G,
        'reduced_form': Q_red,
        'form_class': Q_red,  # the GL2(Z) class
        'f1': f1, 'f2': f2,
        'class_number_F': F.class_number(),
        'regulator': F.regulator(),
    })
```

### Step 3: Pattern extraction

For each non-cyclic F, compute and tabulate:

| disc(F) | poly | (a, b, c) reduced | f₁ | f₂ | h_F | R_F | a/f₁ | c/f₂ | a+c | b mod small primes |

Then search for:

```python
for r in results:
    a, b, c = r['reduced_form'].coefficients()
    f1, f2 = r['f1'], r['f2']
    disc = r['disc']
    
    # Test: a = f1, c = f2?
    print(f"disc={disc}: a={a}, f1={f1}, c={c}, f2={f2}, match={a==f1 and c==f2}")
    
    # Test: a*c = disc + b^2?  (tautological — always true by definition)
    # Instead test: does b have a clean formula?
    
    # Test: b² mod disc
    print(f"  b={b}, b^2 mod disc = {b^2 % disc}")
    
    # Test: a + c
    print(f"  a+c = {a+c}, sqrt(4*disc + (2b)^2)/2 = ..., trace = {r['trace_matrix'].trace()}")
    
    # Test: form genus
    # The genus is determined by the values of the form mod 4, mod p for p | disc
    
    # Test: is the form the principal form of disc -4*disc_F?
    principal = BinaryQF_reduced_representatives(-4*disc, primitive_only=True)[0]
    print(f"  principal form: {principal}, match: {Q_red == principal}")
```

### Step 4: Formulate and test conjecture

Based on the pattern search, formulate a conjecture of the form:

**"For a non-cyclic totally real cubic F with Galois closure S₃ and Artin conductor decomposition disc(F) = f₁·f₂, paired with an imaginary quadratic field K of class number 1, the GL₂(ℤ) equivalence class of the Weil lattice Gram matrix is [FORMULA]."**

Test this conjecture against ALL computed cases. If it holds with zero exceptions, that's the theorem for Paper 66.

---

## 4. ARTIN CONDUCTOR COMPUTATION

For an S₃ cubic F, the discriminant factors as disc(F) = f₁ · f₂ where f₁ and f₂ are the Artin conductors of the two non-trivial irreducible representations of S₃ (the sign character and the standard 2-dimensional representation).

In SageMath:

```python
def artin_conductor_components(F):
    """Compute Artin conductor components for S3 cubic F.
    
    For an S3 cubic, disc(F) = f(sign) * f(std)^2 where:
    - f(sign) is the conductor of the sign character of S3
    - f(std) is the conductor of the 2-dim standard representation
    
    Actually for a cubic field, disc(F) = f(rho)^2 / f(trivial)
    where rho is the permutation representation... need to be careful.
    """
    # The simplest approach: factor disc(F) and use ramification data
    G = F.galois_closure('c')
    # ... or use the LMFDB Artin representation data
    
    # SIMPLER: for a cubic field F with Galois closure F~ and 
    # Gal(F~/Q) = S3, the discriminant is
    #   disc(F) = (-1)^s * prod_p p^{a_p}
    # where a_p depends on the ramification type at p.
    # Fully ramified: a_p = 2
    # Tamely ramified (p != 2,3): a_p = 2
    # For p = 2, 3: more complex
    
    # The factorization disc(F) = f1 * f2 may not exist cleanly
    # for all S3 cubics. Investigate case by case.
    pass
```

**NOTE:** The Artin conductor decomposition for S₃ cubics is more subtle than for cyclic cubics. For cyclic cubics, disc(F) = f² is clean. For S₃ cubics, disc(F) = d_K · f² where d_K is the discriminant of the quadratic resolvent field and f is the conductor of the 2-dimensional representation. This decomposition IS the arithmetic data that might predict the form class.

Specifically: every S₃ cubic F has a **quadratic resolvent** — a unique quadratic field Q(√D) corresponding to the quotient S₃ → ℤ/2ℤ. The discriminant of F factors as:

```
disc(F) = D · f²
```

where D = discriminant of the quadratic resolvent and f = Artin conductor of the faithful 2-dim representation.

**THIS IS THE MOST LIKELY PREDICTOR.** The quadratic resolvent D and the 2-dim conductor f together determine disc(F), and they likely determine the Gram form class as well.

Test: for disc(F) = 229:
- Factor 229... it's prime. So either D = 229, f = 1, or D = 1, f = √229 (not integer).
- Since 229 is prime, the quadratic resolvent has discriminant D = 229 (or -229 or 4·229...).
- Need to compute the actual resolvent for x³ - 4x - 1.

```python
# Quadratic resolvent of x³ + px + q:
# resolvent polynomial is y² + disc(F) (for the depressed cubic)
# or more generally, for x³ + ax + b:
# disc = -4a³ - 27b²
# resolvent quadratic: y² - disc = 0, i.e., Q(√disc)

# For x³ - 4x - 1: a = -4, b = -1
# disc = -4(-4)³ - 27(1) = 256 - 27 = 229
# resolvent: Q(√229)
```

So the quadratic resolvent of x³ - 4x - 1 is ℚ(√229), with discriminant 229 (since 229 ≡ 1 mod 4, the discriminant is 229). And disc(F) = 229 = 229 · 1², so f = 1 (the 2-dim representation is unramified!).

This means for this field, D = 229 and f_Artin = 1. The Gram form [[14, 3], [3, 17]] has det = 229. Does 14 or 17 relate to 229 in a clean way? 14 + 17 = 31. 14 · 17 = 238 = 229 + 9 = 229 + 3². Hmm — 14·17 - 3² = 229. That's just the determinant condition.

What about: 14 = (229 + 1)/2 - 101? No, that's noise.

**We need more data points before conjecturing.** That's what the computation is for.

---

## 5. DELIVERABLES

| File | Description |
|------|-------------|
| `p65b_trace_shortcut_validation.py` | Validates trace-form shortcut on known cases |
| `p65b_gram_computation.py` | Computes Gram forms for all non-cyclic cubics disc ≤ 2000 |
| `p65b_pattern_search.py` | Systematic search for arithmetic predictor |
| `p65b_results.csv` | Full data: disc, poly, Gram form, resolvent, conductors |
| `p65b_analysis.md` | Pattern search report with conjecture (or negative result) |

### Plots

1. Scatter: (disc(F), a) and (disc(F), c) for the reduced Gram form entries
2. Scatter: (D_resolvent, a) where D is the quadratic resolvent discriminant
3. Heat map: form class vs. resolvent discriminant D and conductor f_Artin
4. If pattern found: verification plot showing all cases on predicted curve

---

## 6. SUCCESS CRITERIA

**Discovery (best case):** A clean formula: "The reduced Gram form (a, b, c) satisfies a = φ₁(D, f), b = φ₂(D, f), c = φ₃(D, f) where D is the quadratic resolvent discriminant and f is the Artin conductor of the 2-dim S₃ representation." This would be a genuine theorem connecting Hodge theory (the Weil lattice intersection form) to Galois theory (the Artin conductor) at the integral level. The cyclic case h·Nm(𝔄) = f is recovered when D = 1 (trivial resolvent) and f = conductor.

**Partial discovery:** The form GENUS (not the exact class) is determined by (D, f). The genus is a coarser invariant than the class, determined by local conditions. If the genus is predicted but the class within the genus is not, that's still interesting — it means the Weil lattice knows about local ramification but not about global class group structure.

**Clean negative result:** No pattern. The form class depends on the full structure of 𝒪_E (not just D and f). This tells you h = f is special to the cyclic case in a precise way: cyclic cubics are exactly the locus where the trace form projection is scalar.

**Computation failure:** The trace-form shortcut doesn't produce the correct Gram matrix. This means the Weil lattice is NOT simply the trace lattice of 𝒪_F, and a deeper computation (period matrices, CM type) is needed. Still informative — it rules out the simplest explanation.

---

## 7. EXECUTION ORDER

1. **Validate trace-form shortcut** on cyclic f = 7 and non-cyclic disc = 229. This is the gate. If it doesn't work, stop and rethink.
2. **Compute quadratic resolvents** for all non-cyclic cubics with disc ≤ 2000. Record D and f_Artin.
3. **Compute Gram forms** via the trace shortcut for all non-cyclic cubics.
4. **Pattern search** across the full dataset.
5. **Formulate conjecture** (or document negative result).
6. **Write Paper 66** (or fold into Paper 65 as an extended section).

If Step 1 fails, fall back to: compute the full 𝒪_E trace form (6×6) and identify the Weil sublattice within it. This is harder but still concrete.

---

## 8. THE PRIZE

If the form-class predictor exists and involves the Artin conductor decomposition, then:

- **Cyclic case (ℤ/3ℤ):** trivial resolvent, D = 1, disc(F) = f². Form class is scalar. h · Nm(𝔄) = f.
- **Non-cyclic case (S₃):** nontrivial resolvent ℚ(√D), disc(F) = D · f_Artin². Form class is [a, b, c] predicted by (D, f_Artin, K).
- **Unifying statement:** "The GL₂(ℤ) class of the Weil lattice Gram form is determined by the Artin conductor data of the Galois closure of F, twisted by the Steinitz class of K."

This would be a theorem that connects three classical subjects — Hodge theory (intersection forms), algebraic number theory (Artin conductors), and lattice theory (binary quadratic forms) — through the exotic Weil class construction. The constructive lens found it because it forced exact computation; the classical lens missed it because det(G) = disc(F)·|Δ_K| was sufficient for all classical purposes.

That's the prize. The computation will tell us if it's real.
