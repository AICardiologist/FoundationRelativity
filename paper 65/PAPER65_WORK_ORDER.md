# Paper 65: Self-Intersection Patterns Beyond Cyclic Cubics — Computational Work Order

**For:** Computational AI agent (Claude Code, or equivalent)
**From:** Paul Lee / editorial team
**Date:** February 2026
**Priority:** Execute now. No external API dependencies — all data is self-generated.
**CRITICAL:** LMFDB API is BLOCKED by CAPTCHA. Do NOT attempt to access it. All number field data must be computed from first principles using only integer arithmetic and polynomial algebra.

---

## Context

Papers 56–58 discovered the h = f pattern:

> For each of the nine Heegner fields K = ℚ(√-d) paired with a totally real cyclic Galois cubic F,
> the self-intersection degree of the exotic Weil class on the CM abelian fourfold equals
> the conductor of F: deg(w₀²) = f.

For class number > 1, the pattern generalises to h · Nm(𝔄) = f, where 𝔄 is the Steinitz ideal class.

**This paper asks: how far does this generalise?**

Three families:
- **Family 3** (primary, execute first): Systematic h · Nm(𝔄) = f across many (K, F) pairs
- **Family 1** (secondary): What happens for non-cyclic cubics (S₃ Galois group)?
- **Family 2** (stretch goal): Quartic CM fields

---

## Mathematical Background

### The Key Equation (Schoen 1998, Milne 1999)

The Gram matrix G of the rank-2 Weil lattice W_int on a CM abelian fourfold satisfies:

```
det(G) = disc(F) · |Δ_K|
```

where disc(F) is the discriminant of the totally real cubic F and Δ_K is the discriminant of the imaginary quadratic field K.

### How h = f Emerges (Class Number 1, Cyclic F)

When h_K = 1 (𝒪_K is PID) AND F is cyclic Galois (Gal = ℤ/3ℤ):
1. PID ⟹ W_int is free over 𝒪_K ⟹ Gram matrix G is diagonal
2. Cyclic Galois ⟹ conductor-discriminant: disc(F) = f²
3. Diagonal G with det = f² · |Δ_K| and 𝒪_K-scaling ⟹ h² = f²
4. Positive-definite (Hodge-Riemann) ⟹ h = f

### The Steinitz Twist (Class Number > 1, Cyclic F)

When h_K > 1, 𝒪_K is not PID. Steinitz theorem: W_int ≅ 𝒪_K ⊕ 𝔄 for some ideal 𝔄.
The corrected formula: h · Nm(𝔄) = f.

Whether the lattice is free or must twist depends on whether f is representable by the principal binary quadratic form of K. If not, arithmetic forces the Steinitz twist (Paper 58: ℚ(√-5), f = 7 example).

---

## Family 3: Systematic Verification (PRIMARY TASK)

### Step 1: Compute Class Numbers

Compute h_K for all squarefree d from 1 to 200 using reduced binary quadratic forms.

```python
def class_number(d):
    """
    Compute class number of Q(sqrt(-d)) for squarefree d > 0.
    Uses enumeration of reduced binary quadratic forms of discriminant Δ.
    """
    if d % 4 == 3:
        Delta = -d
    else:
        Delta = -4 * d
    
    absDelta = abs(Delta)
    count = 0
    import math
    a_max = int(math.sqrt(absDelta / 3.0)) + 1
    
    for a in range(1, a_max + 1):
        # b must satisfy b² ≡ Δ (mod 4a) and -a < b ≤ a
        for b in range(-a + 1, a + 1):
            numerator = b * b - Delta  # b² - Δ = b² + |Δ|
            if numerator % (4 * a) != 0:
                continue
            c = numerator // (4 * a)
            if c < a:
                continue
            # Reduced form conditions
            if a == c and b < 0:
                continue
            if b == -a:  # |b| = a but b negative
                continue
            count += 1
    
    return count
```

**Verify against known values before proceeding:**
- d=1: h=1, d=2: h=1, d=3: h=1, d=7: h=1, d=11: h=1, d=19: h=1, d=43: h=1, d=67: h=1, d=163: h=1 (the nine Heegner numbers)
- d=5: h=2, d=6: h=2, d=10: h=2, d=13: h=2, d=15: h=2
- d=14: h=4, d=17: h=4, d=21: h=4
- d=23: h=3

Save output as `p65_class_numbers.csv` with columns: d, Delta_K, h_K, class_group_structure.

### Step 2: Find Cyclic Cubic Polynomials

For each prime p ≡ 1 (mod 3) up to 200, and for f = 9, find the minimal polynomial of the corresponding cyclic cubic by searching for x³ + x² + ax + b with discriminant = f².

```python
def find_cyclic_cubic(f):
    """
    Find (a, b) such that x³ + x² + ax + b defines a cyclic cubic of conductor f.
    Discriminant formula for x³ + x² + ax + b:
        disc = a² - 4a³ + 18ab - 4b - 27b²
    We need disc = f².
    Also need: irreducible over Q (no rational roots) and totally real (3 real roots).
    """
    target = f * f
    results = []
    
    search_range = max(f + 10, 100)
    for a in range(-search_range, 1):  # a is typically negative for these
        for b in range(-search_range, search_range + 1):
            disc = a*a - 4*a*a*a + 18*a*b - 4*b - 27*b*b
            if disc != target:
                continue
            
            # Check irreducibility: no rational roots
            # Rational root theorem: roots divide b
            has_root = False
            if b == 0:
                has_root = True  # x=0 is root
            else:
                for r in range(1, abs(b) + 1):
                    if abs(b) % r != 0:
                        continue
                    for sign in [1, -1]:
                        x = sign * r
                        if x**3 + x**2 + a*x + b == 0:
                            has_root = True
                            break
                    if has_root:
                        break
            
            if not has_root:
                results.append((a, b))
    
    return results[0] if results else None
```

**Target conductors (primes ≡ 1 mod 3, up to 200):**
7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109, 127, 139, 151, 157, 163, 181, 193, 199

Plus f = 9 (from ℚ(ζ₉)).

**Verify:** For each found polynomial, confirm disc = f² by direct computation.

Save as `p65_cyclic_cubics.csv` with columns: f, a_coeff, b_coeff, disc, disc_is_f_squared.

### Step 3: Representability by Principal Form

For each pair (d, f), determine whether f is represented by the principal binary quadratic form of ℚ(√-d).

```python
def principal_form_represents(d, n):
    """
    Check if n is represented by the principal form of Q(sqrt(-d)).
    
    d ≡ 3 (mod 4): form is x² + xy + ((d+1)/4)y², discriminant -d
    d ≡ 1, 2 (mod 4): form is x² + dy², discriminant -4d
    
    Returns (True, x, y) or (False, None, None).
    """
    import math
    
    if d % 4 == 3:
        c = (d + 1) // 4
        y_max = int(math.sqrt(n / c)) + 2
        for y in range(0, y_max):
            for x in range(0, n + 1):
                val = x*x + x*y + c*y*y
                if val == n:
                    return True, x, y
                if val > n:
                    break
        # Also check negative x
        for y in range(1, y_max):
            for x in range(-n, 0):
                val = x*x + x*y + c*y*y
                if val == n:
                    return True, x, y
                if val > n and x > -y//2:
                    break
        return False, None, None
    else:
        y_max = int(math.sqrt(n / d)) + 2
        for y in range(0, y_max):
            remainder = n - d * y * y
            if remainder < 0:
                break
            x = int(math.sqrt(remainder))
            if x * x == remainder:
                return True, x, y
        return False, None, None
```

### Step 4: Determine h and Nm(𝔄) for Each Pair

```python
def compute_self_intersection(d, f):
    """
    For K = Q(sqrt(-d)), cyclic cubic F of conductor f:
    Compute (h, Nm_A) where h · Nm(A) = f.
    
    If h_K = 1: h = f, Nm(A) = 1 (always, by freeness).
    If h_K > 1: depends on representability of f by principal form.
    """
    h_K = class_number(d)
    
    if h_K == 1:
        return f, 1, "free"
    
    rep, x, y = principal_form_represents(d, f)
    
    if rep:
        # f is represented by principal form → free lattice works
        return f, 1, "free (f representable)"
    else:
        # f NOT represented by principal form → Steinitz twist forced
        # Need to find Nm(A) such that:
        # 1. Nm(A) divides f (since h = f/Nm(A) must be positive)
        # 2. The resulting h is representable by the appropriate form
        # 3. Nm(A) is the norm of an ideal in the correct class
        
        # For class number 2: only one non-trivial class.
        # Try all divisors of f in increasing order.
        divisors = sorted([p for p in range(2, f+1) if f % p == 0])
        
        for Nm_A in divisors:
            h_candidate = f // Nm_A
            if h_candidate * Nm_A != f:
                continue  # not exact division (shouldn't happen for int divisors)
            
            # Check: is Nm_A the norm of a non-principal ideal?
            # For class number 2: Nm_A should NOT be represented by principal form
            # but should be the norm of an ideal (i.e., a prime that doesn't split
            # principally, or a product thereof)
            
            # Simplified check: Nm_A is not represented by principal form
            rep_A, _, _ = principal_form_represents(d, Nm_A)
            if not rep_A:
                # Nm_A is in non-principal class. 
                # Verify h_candidate makes sense (positive integer).
                if h_candidate > 0:
                    return h_candidate, Nm_A, f"steinitz (Nm={Nm_A})"
        
        # Fallback: try rational h
        # h · Nm(A) = f where both could involve the class group structure
        return None, None, "UNDETERMINED — needs manual analysis"
```

### Step 5: Run All Pairs

```python
def run_family3():
    """Main computation for Family 3."""
    
    # All squarefree d from 1 to 200
    squarefree = [d for d in range(1, 201) if is_squarefree(d)]
    
    # All cyclic cubic conductors up to 200
    conductors = [7, 9, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97,
                  103, 109, 127, 139, 151, 157, 163, 181, 193, 199]
    
    results = []
    for d in squarefree:
        h_K = class_number(d)
        for f in conductors:
            h, Nm_A, status = compute_self_intersection(d, f)
            
            if h is not None and Nm_A is not None:
                product = h * Nm_A
                matches = (product == f)
            else:
                product = None
                matches = None
            
            results.append({
                'd': d,
                'Delta_K': -d if d % 4 == 3 else -4*d,
                'h_K': h_K,
                'f': f,
                'h': h,
                'Nm_A': Nm_A,
                'h_times_Nm': product,
                'equals_f': matches,
                'status': status,
            })
    
    return results


def is_squarefree(n):
    """Check if n is squarefree."""
    if n <= 1:
        return n == 1
    for p in range(2, int(n**0.5) + 1):
        if n % (p*p) == 0:
            return False
    return True
```

### Step 6: Verification Checks

Before trusting any results, verify:

1. **Class number spot-check:** Confirm h_K matches known values for at least 20 fields.
2. **Cyclic cubic spot-check:** For f = 7, 13, 19, 43, 67, 163 (the Heegner conductor values), confirm disc = f² and the polynomial is irreducible with three real roots.
3. **Known h = f cases:** For the nine Heegner fields paired with their matching conductor, confirm h = f. These are the cases from Papers 56-57:
   - d=1, f=4 → h=4 (wait: f=4 is not prime ≡ 1 mod 3...)
   
   Actually, let me state the known cases precisely:
   - (d=7, f=7): h = 7 ✓
   - (d=11, f=11): h = 11 ✓
   - (d=19, f=19): h = 19 ✓
   - (d=43, f=43): h = 43 ✓
   - (d=67, f=67): h = 67 ✓
   - (d=163, f=163): h = 163 ✓
   - (d=1, f=...), (d=2, f=...), (d=3, f=...): the small Heegner fields.
     For d=1 (Gaussian integers): paired with appropriate F.
     For d=3: paired with F of conductor 9 → h = 9? Or different pairing.

   The exact pairings from Papers 56-57 should be checked against those papers.
   **At minimum:** the d=7,11,19,43,67,163 cases with f=d should give h=f.

4. **Known Steinitz case:** d=5 (h_K = 2), f=7. The free lattice needs 7 = x² + 5y²,
   but 7 mod 5 = 2, and 2 is not a QR mod 5 (squares mod 5: 0,1,4). So representation
   fails. Steinitz twist forced: Nm(𝔄) should be 2 (smallest prime in non-principal class
   of ℚ(√-5)), giving h = 7/2.

   Wait — h = 7/2 is not an integer. This is fine: h is a positive rational (the
   self-intersection degree in the projective Weil lattice can be rational when the
   lattice is non-free). Verify this case carefully.

---

## Family 1: Non-Cyclic Cubics (SECONDARY TASK)

### Step 1: Enumerate Non-Cyclic Totally Real Cubics

Search for irreducible polynomials x³ + x² + ax + b with:
- Positive discriminant (totally real)
- Non-square discriminant (non-cyclic, so S₃ Galois group)
- |a| ≤ 30, |b| ≤ 30

Collect the first 30-50 such cubics, sorted by discriminant.

### Step 2: For Each Non-Cyclic Cubic, Analyse the Gram Matrix

For each non-cyclic cubic F and each Heegner field K (h_K = 1):

**Key observation to verify:** The Gram matrix G should NOT diagonalise, because
the ℤ/3ℤ Galois symmetry is absent. This means h ≠ √disc(F) (which would be
irrational), and instead h is determined by the full Gram matrix structure.

**Compute:** det(G) = disc(F) · |Δ_K|. Enumerate all positive-definite integer
matrices [[a, b], [b, c]] with ac - b² = disc(F) · |Δ_K|. There are finitely many.

```python
def enumerate_gram_matrices(det_value):
    """
    Find all 2×2 positive-definite integer matrices with given determinant.
    [[a, b], [b, c]] with ac - b² = det_value, a > 0, c > 0, a ≤ c.
    """
    import math
    results = []
    
    # a ranges from 1 to sqrt(det_value) + det_value (since ac ≥ det_value + b²)
    a_max = det_value + 1  # generous upper bound
    for a in range(1, min(a_max, 10000)):
        # b ranges from 0 to a-1 (by reduction theory, |b| ≤ a/2)
        b_max = a // 2
        for b in range(0, b_max + 1):
            numerator = det_value + b * b
            if numerator % a != 0:
                continue
            c = numerator // a
            if c < a:
                continue
            if c < 0:
                continue
            # Additional reduction: if a == c then b ≥ 0 (already ensured)
            results.append((a, b, c))
    
    return results
```

For each possible Gram matrix, record (h, off_diagonal, second_diagonal) = (a, b, c).
The self-intersection degree h is the (1,1) entry a.

### Step 3: Look for Patterns

For each non-cyclic cubic F (with discriminant disc_F):
- List all possible h values from the Gram matrix enumeration.
- Is there a preferred h? (The "correct" one depends on the CM construction.)
- Does h relate to disc_F in a simple way? (e.g., h = disc_F / something?)
- Does h relate to the conductor of the Galois closure F̃?

Record all findings in `p65_family1_gram_analysis.csv`.

---

## Deliverables

### Data Files

1. `p65_class_numbers.csv` — Class numbers for d ≤ 200
2. `p65_cyclic_cubics.csv` — Cyclic cubic polynomials with verified discriminants
3. `p65_family3_results.csv` — All (K, F) pairs: d, f, h_K, h, Nm_A, h·Nm(𝔄), equals_f
4. `p65_family1_cubics.csv` — Non-cyclic cubics with discriminants
5. `p65_family1_gram_candidates.csv` — Gram matrix candidates for non-cyclic cases

### Plots

1. `p65_family3_verification.png` — h · Nm(𝔄) vs f for all cyclic pairs (should lie on y=x)
2. `p65_forcing_heatmap.png` — Heatmap: d (y-axis) vs f (x-axis), colored by whether Steinitz twist is forced
3. `p65_class_numbers.png` — Class number distribution for d ≤ 200

### Summary Report

`p65_computation_report.md` with:

1. **Family 3 verification:** h · Nm(𝔄) = f confirmed for ___ pairs? Any exceptions?
2. **Forcing statistics:** What fraction of (d, f) pairs force non-trivial Steinitz class?
3. **Family 1 findings:** Non-cyclic cubics — does h = f fail? How? What patterns emerge?
4. **Surprises:** Anything unexpected in the data

---

## Execution Order

1. Implement and verify class_number(d) — spot-check 20+ known values
2. Implement and verify cyclic cubic finder — confirm disc = f² for all
3. Implement and verify principal_form_represents() — test known cases
4. Run Family 3 computation (all d ≤ 200 × all f ≤ 200 cyclic conductors)
5. Enumerate non-cyclic cubics with disc ≤ 1000
6. Gram matrix analysis for Family 1
7. Generate plots and report

**Total estimated (curve, conductor) pairs:** ~120 squarefree d × ~22 conductors ≈ 2,640 pairs.
All computation is integer arithmetic. Should run in under 5 minutes.
